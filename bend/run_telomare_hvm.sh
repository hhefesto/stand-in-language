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
#      TELOMARE_HVM_RUNNER (gen-hvm [default], bend-run-c, or gen-c-big:
#        `hvm gen-c` + gcc, single-threaded, node arena raised to 1<<30 —
#        ~13 GB peak; avoids the C interpreter's small per-thread arena and
#        its OOM print-loop; the compiled binary is cached beside the .bend),
#      TELOMARE_HVM_GCC (gcc binary for gen-c-big, default `gcc`),
#      TELOMARE_HVM_MAX_OUTPUT_BYTES (default 268435456).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
tel_file="${1:?usage: run_telomare_hvm.sh <program.tel> [prelude.tel]}"
prelude="${2:-$(dirname "$here")/Prelude.tel}"
telomare="${TELOMARE_BIN:-telomare}"
emit_flag="${TELOMARE_EMIT_FLAG:---emit-hvm}"
bend="${BEND_BIN:-bend}"
hvm="${HVM_BIN:-hvm}"
budget="${TELOMARE_HVM_TIMEOUT:-1800}"
max_output="${TELOMARE_HVM_MAX_OUTPUT_BYTES:-268435456}"
runner="${TELOMARE_HVM_RUNNER:-gen-hvm}"
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

rm -f "$work/output-capped"
set +e
case "$runner" in
  gen-hvm)
    timeout "$budget" "$bend" gen-hvm "$work/run.bend" > "$work/run.hvm" 2>"$work/stage2.err"
    gen_status=$?
    if [ "$gen_status" -ne 0 ]; then
      set -e
      echo "telomare-hvm: stage 2 (gen-hvm) failed with status $gen_status" >&2
      show_err "$work/stage2.err"
      exit 1
    fi
    run_cmd=(timeout "$budget" "$hvm" run-c "$work/run.hvm")
    ;;
  bend-run-c)
    run_cmd=(timeout "$budget" "$bend" run-c "$work/run.bend")
    ;;
  gen-c-big)
    # hvm gen-c + gcc, single-threaded, arena raised to 1<<30 nodes (~13 GB
    # peak). The interpreter's per-thread slice (G_NODE_LEN/TPC) is what
    # overflows on large programs — and on overflow it loops printing "OOM"
    # instead of exiting. gen-c bakes the inputs into the program, so the
    # binary is cached by the hash of program+inputs (same-input replays are
    # free; new inputs cost one gcc run).
    #
    # CRITICAL for large programs (e.g. tictactoe, ~32k defs): hvm gen-c
    # hardcodes the Book's definition table to `Def defs_buf[0x4000]` (16384).
    # A program with more defs than that overflows the fixed array and the
    # binary SEGFAULTS in ~2s (not an OOM loop — a genuine out-of-bounds
    # crash). We patch it to 0x20000 (131072). TELOMARE_HVM_DEFS_BUF overrides.
    gcc_bin="${TELOMARE_HVM_GCC:-gcc}"
    defs_buf="${TELOMARE_HVM_DEFS_BUF:-0x20000}"
    tpc_l2="${TELOMARE_HVM_TPC_L2:-0}"
    run_hash="$(sha256sum "$work/run.bend" | cut -c1-32)"
    cached_bin="$cache_dir/$run_hash.bin"
    if [ ! -x "$cached_bin" ]; then
      timeout "$budget" "$bend" gen-hvm "$work/run.bend" > "$work/run.hvm" 2>"$work/stage2.err" \
        && timeout "$budget" "$hvm" gen-c "$work/run.hvm" > "$work/run.c" 2>>"$work/stage2.err"
      gen_status=$?
      if [ "$gen_status" -ne 0 ]; then
        set -e
        echo "telomare-hvm: stage 2 (gen-c) failed with status $gen_status" >&2
        show_err "$work/stage2.err"
        exit 1
      fi
      sed "s/#define G_NODE_LEN (1ul << 29)/#define G_NODE_LEN (1ul << 30)/; s/#define G_VARS_LEN (1ul << 29)/#define G_VARS_LEN (1ul << 30)/; s/Def defs_buf\[0x4000\]/Def defs_buf[$defs_buf]/" \
        "$work/run.c" > "$work/run_big.c"
      timeout "$budget" "$gcc_bin" -O2 -DTPC_L2="$tpc_l2" -lm -lpthread "$work/run_big.c" -o "$work/run.bin" 2>"$work/stage2.err"
      cc_status=$?
      if [ "$cc_status" -ne 0 ]; then
        set -e
        echo "telomare-hvm: stage 2 (gcc) failed with status $cc_status" >&2
        show_err "$work/stage2.err"
        exit 1
      fi
      mv "$work/run.bin" "$cached_bin"
    fi
    run_cmd=(timeout "$budget" "$cached_bin")
    ;;
  *)
    set -e
    echo "telomare-hvm: unknown TELOMARE_HVM_RUNNER '$runner'" >&2
    exit 1
    ;;
esac
"${run_cmd[@]}" 2>"$work/stage2.err" \
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
    ' > "$work/stage2.out"
stage2_status=(${PIPESTATUS[@]})
set -e
if [ "${stage2_status[1]}" -ne 0 ]; then
  echo "telomare-hvm: stage 2 (run) output processing failed with status ${stage2_status[1]}" >&2
  show_err "$work/stage2.err"
  [ ! -e "$work/output-capped" ] || exit 99
  exit 1
fi
if [ "${stage2_status[0]}" -ne 0 ]; then
  echo "telomare-hvm: stage 2 (run) failed with status ${stage2_status[0]}" >&2
  show_err "$work/stage2.err"
  exit 1
fi
decode_result < "$work/stage2.out"
