#!/usr/bin/env bash
# telomare hybrid driver (shell/awk only): Haskell front end, HVM2 runtime.
#   stage 1: `telomare --emit-hvm <program.tel>` — GHC does parse/resolve/
#            Possible.hs recursion sizing (the part that needs laziness and
#            sharing) and prints the generated Bend program. The result is
#            INPUT-INDEPENDENT and cached by source hash: a .tel program is
#            compiled once, then any input script replays at stage-2 cost.
#   stage 2: the generated (defunctionalized) program + a driver-generated
#            `def inputs()` runs on the standalone HVM C interpreter
#            (`bend gen-hvm | hvm run-c`); its pure result is the transcript.
#
# Usage: run_telomare_hvm.sh <program.tel> [prelude.tel] < input-lines
# Env: TELOMARE_HVM_TIMEOUT (seconds per stage, default 1800),
#      TELOMARE_BIN (the Haskell telomare binary, default `telomare`),
#      TELOMARE_EMIT_FLAG (--emit-hvm [default] or --emit-hvm-ccc),
#      BEND_BIN, HVM_BIN, TELOMARE_HVM_CACHE (default ~/.cache/telomare-hvm),
#      TELOMARE_HVM_MAX_OUTPUT_BYTES (default 10485760).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tel_file="${1:?usage: run_telomare_hvm.sh <program.tel> [prelude.tel]}"
prelude="${2:-$(dirname "$here")/Prelude.tel}"
telomare="${TELOMARE_BIN:-telomare}"
emit_flag="${TELOMARE_EMIT_FLAG:---emit-hvm}"
bend="${BEND_BIN:-bend}"
hvm="${HVM_BIN:-hvm}"
budget="${TELOMARE_HVM_TIMEOUT:-1800}"
max_output="${TELOMARE_HVM_MAX_OUTPUT_BYTES:-10485760}"
cache_dir="${TELOMARE_HVM_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/telomare-hvm}"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
cat > "$work/inputs.txt" || true

show_err() {
  awk 'NR <= 20 { print }' "$1" >&2
}

# ---------------------------------------------------------------------------
# emit_inputs <file>: the per-run `def inputs()` in TV encoding — each line
# becomes its own def (a char c is a c-deep i2b nest; one def per line
# stays under HVM's per-def size cap for short lines).
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
# decode_result: hvm Result term dump -> text. Formats: quoted literal or
# String/Cons/tag codepoint chains. Emitted text is ASCII by construction.
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
# stage 1 (cached): parse+resolve+size+emit under GHC. The compiler binary
# content hash is part of the cache key so a rebuilt compiler invalidates entries.
# ---------------------------------------------------------------------------
mkdir -p "$cache_dir"
tel_dir="$(cd "$(dirname "$tel_file")" && pwd)"
tel_base="$(basename "$tel_file")"
bin_path="$(command -v "$telomare" || true)"
if [ -n "$bin_path" ] && [ -r "$bin_path" ]; then
  bin_id="$bin_path:$(sha256sum "$bin_path" | awk '{ print $1 }')"
else
  bin_id="$telomare"
fi
src_hash="$( { sha256sum "$prelude" "$tel_file"; printf '%s\n' "$bin_id" "$emit_flag"; } | sha256sum | cut -c1-32)"
cached="$cache_dir/$src_hash.bend"

if [ ! -s "$cached" ]; then
  # getModulesFor resolves imports relative to the working directory
  (cd "$tel_dir" && timeout "$budget" "$telomare" "$emit_flag" "$tel_base") \
    2>"$work/stage1.err" > "$work/out.bend" \
    || { echo "telomare-hvm: stage 1 (compile) failed" >&2; show_err "$work/stage1.err"; exit 1; }
  [ -s "$work/out.bend" ] || { echo "telomare-hvm: stage 1 produced no output" >&2; exit 1; }
  mv "$work/out.bend" "$cached"
fi

# ---------------------------------------------------------------------------
# stage 2: append the inputs def, run on the HVM C interpreter (no gcc, no
# per-def size cap in practice, sound duplication for the defunctionalized
# encoding)
# ---------------------------------------------------------------------------
cp "$cached" "$work/run.bend"
emit_inputs "$work/inputs.txt" >> "$work/run.bend"

timeout "$budget" "$bend" gen-hvm "$work/run.bend" > "$work/run.hvm" 2>"$work/stage2.err" \
  || { echo "telomare-hvm: stage 2 (gen-hvm) failed" >&2; show_err "$work/stage2.err"; exit 1; }
rm -f "$work/output-capped"
timeout "$budget" "$hvm" run-c "$work/run.hvm" 2>"$work/stage2.err" \
  | awk -v max="$max_output" -v capped="$work/output-capped" '
      {
        bytes += length($0) + 1
        if (bytes > max) {
          print "telomare-hvm: stage 2 output exceeded " max " bytes" > "/dev/stderr"
          print "capped" > capped
          exit 99
        }
        print
      }
    ' > "$work/stage2.out" \
  || { echo "telomare-hvm: stage 2 (run) failed" >&2; show_err "$work/stage2.err"; [ ! -e "$work/output-capped" ] || exit 99; exit 1; }
decode_result < "$work/stage2.out"
