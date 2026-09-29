#!/usr/bin/env bash
# The goldens: what the Haskell implementation (tag haskell-final) printed for
# each case in test/golden/cases, one file per case under test/golden/expected.
# The Bend port is measured against them.
#
#   test/golden/run.sh BIN_DIR record [PATTERN]   write expected/NAME
#   test/golden/run.sh BIN_DIR check  [PATTERN]   compare, report PASS/FAIL
#
# BIN_DIR holds `telomare` (and `telomare-repl` for the repl cases). PATTERN is
# a shell glob over case names, `*` by default. Run from anywhere; paths are
# taken relative to the repository root.
#
# A case runs in a scratch directory holding its program and Prelude.tel,
# because telomare loads `<Module>.tel` from the current directory. Cases of
# the same program share that directory, in file order, so a `--compile` case
# leaves its .telc for the cases after it. A case's record is its exit status,
# its stdout, its stderr and, for every file it wrote, the file's sha256 and
# size.
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: $0 BIN_DIR record|check [PATTERN]" >&2
  exit 2
fi
bin_dir="$(cd "$1" && pwd)"
mode="$2"
pattern="${3:-*}"
case "$mode" in
  record | check) ;;
  *)
    echo "$0: mode must be record or check" >&2
    exit 2
    ;;
esac

root="$(cd "$(dirname "$0")/../.." && pwd)"
expected="$root/test/golden/expected"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/actual"
if [ "$mode" = record ]; then mkdir -p "$expected"; fi

# One case's longest run, in seconds (sizing tictactoe takes about a minute).
case_timeout="${GOLDEN_TIMEOUT:-1200}"
passed=0
failed=0

# The scratch directory of a program, made on first use. PROGRAM is a source
# relative to the root, or the .telc an earlier case wrote beside it.
program_dir() {
  local program="$1"
  local base dir
  base="$(basename "$program")"
  base="${base%.telc}"
  dir="$work/programs/${base%.tel}"
  if [ ! -d "$dir" ]; then
    mkdir -p "$dir"
    cp "$root/Prelude.tel" "$dir/"
    case "$program" in
      *.tel) cp "$root/$program" "$dir/" ;;
    esac
  fi
  printf '%s\n' "$dir"
}

# run NAME PROGRAM STDIN COMMAND... : run COMMAND in PROGRAM's directory with
# STDIN (printf %b escapes) and record the result as NAME.
run() {
  local name="$1" program="$2" input="$3"
  shift 3
  # shellcheck disable=SC2053 # PATTERN is a glob on purpose
  if [[ $name != $pattern ]]; then return 0; fi
  local dir out status
  dir="$(program_dir "$program")"
  out="$work/actual/$name"
  touch "$work/marker"
  sleep 0.01
  # From a file, not a pipe: a program that exits before reading its input
  # would otherwise leave the pipe's writer a SIGPIPE status.
  printf '%b' "$input" > "$work/stdin"
  status=0
  (cd "$dir" && timeout "$case_timeout" "$@" < "$work/stdin" > "$work/stdout" 2> "$work/stderr") ||
    status=$?
  {
    printf 'status %s\n' "$status"
    printf '%s\n' '--- stdout'
    cat "$work/stdout"
    printf '%s\n' '--- stderr'
    cat "$work/stderr"
    local written
    written="$(cd "$dir" && find . -type f -newer "$work/marker" | sort)"
    if [ -n "$written" ]; then
      printf '%s\n' '--- files'
      while IFS= read -r file; do
        (cd "$dir" && printf '%s %s %s\n' \
          "$(sha256sum < "$file" | cut -d' ' -f1)" "$(stat -c %s "$file")" "${file#./}")
      done <<< "$written"
    fi
  } > "$out"
  if [ "$mode" = record ]; then
    cp "$out" "$expected/$name"
    printf 'recorded %s (status %s)\n' "$name" "$status"
  elif [ -f "$expected/$name" ] && cmp -s "$out" "$expected/$name"; then
    passed=$((passed + 1))
    printf 'PASS %s\n' "$name"
  else
    failed=$((failed + 1))
    printf 'FAIL %s\n' "$name"
    diff -u "$expected/$name" "$out" | head -40 || true
  fi
}

# case_ NAME PROGRAM STDIN [ARGS...]: `telomare PROGRAM ARGS...` in PROGRAM's
# directory.
case_() {
  local name="$1" program="$2" input="$3"
  shift 3
  run "$name" "$program" "$input" "$bin_dir/telomare" "$(basename "$program")" "$@"
}

# repl_ NAME EXPR: `telomare-repl --expr EXPR` beside the Prelude.
repl_() {
  run "$1" Prelude.tel "" "$bin_dir/telomare-repl" --expr "$2"
}

# shellcheck source=test/golden/cases
. "$root/test/golden/cases"

if [ "$mode" = check ]; then
  printf '%s passed, %s failed\n' "$passed" "$failed"
  if [ "$failed" -ne 0 ]; then exit 1; fi
fi
