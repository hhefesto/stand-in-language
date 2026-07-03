#!/usr/bin/env bash
# telomare-bend two-stage driver (shell/awk only):
#   stage 1: the compiler (parser/resolver/sizer/emitter, all in Bend) runs
#            under `bend run-rs` (the lazy Rust runtime — the C runtime's
#            string output is pathologically slow, see PORT.md) and returns
#            the generated program as its pure result value. The result is
#            INPUT-INDEPENDENT and cached by source hash: a .tel program is
#            compiled once, then any input script replays at stage-2 cost.
#   stage 2: the generated (defunctionalized) program + a driver-generated
#            `def inputs()` runs on the standalone HVM C interpreter
#            (`hvm run-c`); its pure result value is the transcript.
#
# Usage: run_telomare_bend.sh <program.tel> [prelude.tel] < input-lines
# Env: TELOMARE_BEND_TIMEOUT (seconds per stage, default 1800),
#      BEND_BIN, HVM_BIN, TELOMARE_BEND_CACHE (default ~/.cache/telomare-bend).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tel_file="${1:?usage: run_telomare_bend.sh <program.tel> [prelude.tel]}"
prelude="${2:-$(dirname "$here")/Prelude.tel}"
bend="${BEND_BIN:-bend}"
hvm="${HVM_BIN:-hvm}"
budget="${TELOMARE_BEND_TIMEOUT:-1800}"
cache_dir="${TELOMARE_BEND_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/telomare-bend}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cat > "$work/inputs.txt" || true

ulimit -s unlimited 2>/dev/null || true

# ---------------------------------------------------------------------------
# emit_chunks <defname> <file>: <=190-char raw chunks (<=380 after escaping,
# so escape pairs never split), each as a small string def, plus a joiner
# (HVM's C backend caps definitions at 4095 nodes).
# ---------------------------------------------------------------------------
emit_chunks() {
  awk -v name="$1" '
    BEGIN { chunk = ""; n = 0 }
    function esc(s) {
      gsub(/\\/, "\\\\", s)
      gsub(/"/, "\\\"", s)
      return s
    }
    function flush() {
      printf "def %s_%d() -> String:\n  return \"%s\"\n\n", name, n, chunk
      n++; chunk = ""
    }
    {
      line = esc($0) "\\n"
      while (length(chunk) + length(line) > 190) {
        take = 190 - length(chunk)
        piece = substr(line, 1, take)
        if (piece ~ /\\$/ && piece !~ /\\\\$/) take--
        chunk = chunk substr(line, 1, take)
        line = substr(line, take + 1)
        flush()
      }
      chunk = chunk line
      if (length(chunk) >= 190) flush()
    }
    END {
      if (chunk != "" || n == 0) flush()
      printf "def %s() -> String:\n  return frags_join([", name
      for (i = 0; i < n; i++) printf "%s%s_%d()", (i ? ", " : ""), name, i
      printf "])\n\n"
    }
  ' "$2"
}

# ---------------------------------------------------------------------------
# emit_inputs <file>: the per-run `def inputs()` in TV encoding — each line
# becomes its own def (a char c is a c-deep i2b nest; one def per line
# stays under the def-size cap for short lines).
# ---------------------------------------------------------------------------
emit_inputs() {
  awk '
    BEGIN {
      ascii = ""
      for (c = 32; c < 127; c++) ascii = ascii sprintf("%c", c)
    }
    function i2b(n,   s, i) {
      s = "TV/Z"
      for (i = 0; i < n; i++) s = "TV/P(" s ", TV/Z)"
      return s
    }
    {
      s = "TV/Z"
      for (i = length($0); i >= 1; i--) {
        c = index(ascii, substr($0, i, 1))
        if (c > 0) s = "TV/P(" i2b(c + 31) ", " s ")"
      }
      printf "def input_line_%d() -> TV:\n  return %s\n\n", NR - 1, s
      n = NR
    }
    END {
      printf "def inputs() -> List(TV):\n  return ["
      for (i = 0; i < n; i++) printf "%sinput_line_%d()", (i ? ", " : ""), i
      printf "]\n"
    }
  ' "$1"
}

# ---------------------------------------------------------------------------
# decode_result: bend/hvm Result term dump -> text. Formats: quoted literal
# (fully-normal strings under run-rs) or String/Cons/tag codepoint chains
# (run-rs lazy / hvm run-c). Emitted/embedded text is ASCII by construction.
# ---------------------------------------------------------------------------
decode_result() {
  awk '
    /Result: / {
      sub(/.*Result: /, "")
      if (substr($0, 1, 1) == "\"") {
        s = substr($0, 2)
        sub(/"[^"]*$/, "", s)
        gsub(/\\\\/, "\001", s)
        gsub(/\\n/, "\n", s)
        gsub(/\\t/, "\t", s)
        gsub(/\\"/, "\"", s)
        gsub(/\001/, "\\", s)
        printf "%s", s
      } else {
        while (match($0, /String\/Cons\/tag[^0-9]{0,3}[0-9]+/)) {
          tok = substr($0, RSTART, RLENGTH)
          gsub(/[^0-9]/, "", tok)
          printf "%c", tok + 0
          $0 = substr($0, RSTART + RLENGTH)
        }
      }
      found = 1
    }
    END { if (!found) { print "decode_result: no Result line found" > "/dev/stderr"; exit 1 } }
  '
}

# ---------------------------------------------------------------------------
# stage 1 (cached): compile+size+emit under run-rs
# ---------------------------------------------------------------------------
mkdir -p "$cache_dir"
src_hash="$(cat "$prelude" "$tel_file" "$here"/*.bend | sha256sum | cut -c1-32)"
cached="$cache_dir/$src_hash.bend"

if [ ! -s "$cached" ]; then
  {
    for m in util lexer parser ir resolver sizer emitter telc; do
      printf 'from %s/%s import *\n' "$here" "$m"
    done
    printf '\n'
    emit_chunks src_prelude "$prelude"
    emit_chunks src_module "$tel_file"
    printf 'def main() -> String:\n  return emit_pipeline(src_prelude(), src_module())\n'
  } > "$work/stage1.bend"

  timeout "$budget" "$bend" run-rs "$work/stage1.bend" 2>"$work/stage1.err" > "$work/stage1.out" \
    || { echo "telomare-bend: stage 1 (compile) failed" >&2; head -5 "$work/stage1.err" >&2; exit 1; }
  decode_result < "$work/stage1.out" > "$work/out.bend"

  if head -1 "$work/out.bend" | grep -q '^# error:'; then
    cat "$work/out.bend" >&2
    exit 1
  fi
  mv "$work/out.bend" "$cached"
fi

# ---------------------------------------------------------------------------
# stage 2: append the inputs def, run on the HVM C interpreter (no gcc, no
# per-def size cap in practice, sound duplication for the defunctionalized
# encoding; run-rs refuses parts of it)
# ---------------------------------------------------------------------------
cp "$cached" "$work/run.bend"
emit_inputs "$work/inputs.txt" >> "$work/run.bend"

timeout "$budget" "$bend" gen-hvm "$work/run.bend" > "$work/run.hvm" 2>"$work/stage2.err" \
  || { echo "telomare-bend: stage 2 (gen-hvm) failed" >&2; head -5 "$work/stage2.err" >&2; exit 1; }
timeout "$budget" "$hvm" run-c "$work/run.hvm" 2>"$work/stage2.err" > "$work/stage2.out" \
  || { echo "telomare-bend: stage 2 (run) failed" >&2; head -5 "$work/stage2.err" >&2; exit 1; }
decode_result < "$work/stage2.out"
