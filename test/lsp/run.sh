#!/usr/bin/env bash
# The language server's goldens: what master's telomare-lsp answered to
# each session in test/lsp/sessions, one file per session under
# test/lsp/expected, a message a line (lsp.py's form: keys sorted, the
# session's directory as @DIR@). Where the port answers otherwise on
# purpose, test/lsp/port/NAME holds its answers and the check compares
# against that, as test/golden does.
#
#   test/lsp/run.sh BIN_DIR record      [NAME...]   write expected/NAME
#   test/lsp/run.sh BIN_DIR record-port [NAME...]   write port/NAME
#   test/lsp/run.sh BIN_DIR check       [NAME...]   compare, report PASS/FAIL
#
# BIN_DIR holds `telomare-lsp`. A session runs in a scratch directory
# holding Prelude.tel, test/programs/simpleplus.tel and test/lsp/files.
# `record` drives master's server step by step (it answers concurrently, so
# each request waits for its answer and each notification a while); the
# port's server answers in order, so `check` sends it the whole session at
# once.
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: $0 BIN_DIR record|record-port|check [NAME...]" >&2
  exit 2
fi
bin_dir="$(cd "$1" && pwd)"
mode="$2"
shift 2
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
names=("$@")
if [ "${#names[@]}" -eq 0 ]; then
  for s in "$here"/sessions/*.json; do
    s="${s##*/}"
    names+=("${s%.json}")
  done
fi
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
passed=0
failed=0

for name in "${names[@]}"; do
  dir="$work/$name"
  mkdir -p "$dir"
  cp "$root/Prelude.tel" "$root/test/programs/simpleplus.tel" "$here"/files/*.tel "$dir/"
  session="$here/sessions/$name.json"
  case "$mode" in
    record)
      python3 -I "$here/lsp.py" drive "$session" "$dir" -- "$bin_dir/telomare-lsp" > "$here/expected/$name"
      printf 'recorded %s\n' "$name"
      continue
      ;;
    record-port | check)
      python3 -I "$here/lsp.py" stream "$session" "$dir" > "$work/$name.in"
      (cd "$dir" && timeout 600 "$bin_dir/telomare-lsp" < "$work/$name.in" > "$work/$name.raw" 2> /dev/null) || true
      python3 -I "$here/lsp.py" split "$dir" < "$work/$name.raw" > "$work/$name.out"
      ;;
    *)
      echo "$0: mode must be record, record-port or check" >&2
      exit 2
      ;;
  esac
  if [ "$mode" = record-port ]; then
    cp "$work/$name.out" "$here/port/$name"
    printf 'recorded port/%s\n' "$name"
    continue
  fi
  want="$here/expected/$name"
  if [ -f "$here/port/$name" ]; then want="$here/port/$name"; fi
  if cmp -s "$work/$name.out" "$want"; then
    passed=$((passed + 1))
    printf 'PASS lsp.%s\n' "$name"
  else
    failed=$((failed + 1))
    printf 'FAIL lsp.%s\n' "$name"
    diff -u "$want" "$work/$name.out" | head -40 || true
  fi
done

if [ "$mode" = check ]; then
  printf '%s passed, %s failed\n' "$passed" "$failed"
  [ "$failed" -eq 0 ]
fi
