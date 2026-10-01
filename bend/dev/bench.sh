#!/usr/bin/env bash
# bench.sh BENDBIN [NAMES...]: time the Bend telomare (BENDBIN) and
# haskell-final's `--ic` on each program, and compare their output.
#
#   ORACLE=/path/to/haskell-final/telomare bend/dev/bench.sh /tmp/bin/telomare
#   NOHS=1 bend/dev/bench.sh /tmp/bin/telomare tictactoe   # Bend only
#
# Run from anywhere; outputs go to $OUT (default /tmp/telomare-bench).
# Programs: the repo's three goldens' programs, and bend/dev/corpus.
# Build the oracle as HANDOFF.md says (git worktree at haskell-final).
R=$(cd "$(dirname "$0")/../.." && pwd)
B=$(realpath "$1"); shift
H=${ORACLE:-}
OUT=${OUT:-/tmp/telomare-bench}
mkdir -p "$OUT"
declare -A dir inp
for p in tc_ultra_minimal simpleplus tictactoe; do dir[$p]=$R; done
inp[tc_ultra_minimal]=''; inp[simpleplus]='3 4\n'; inp[tictactoe]='1\n9\n2\n8\n3\n'
for p in arith casea casei cases ctall ctign ctprop ctstr natarith natudt nonex patlam qual rat ratarith; do
  dir[$p]=$R/bend/dev/corpus; inp[$p]=''
done
names=("$@"); [ ${#names[@]} -eq 0 ] && names=(tc_ultra_minimal simpleplus tictactoe casea ctprop natarith natudt rat)
for p in "${names[@]}"; do
  cd "${dir[$p]}" || exit 1
  s=$(date +%s%N); printf "${inp[$p]}" | "$B" $p.tel > "$OUT/$p.b" 2>&1; e=$(date +%s%N); tb=$(( (e-s)/1000000 ))
  if [ -n "$NOHS" ] || [ -z "$H" ]; then th=-; same=-; else
    s=$(date +%s%N); printf "${inp[$p]}" | "$H" --ic $p.tel > "$OUT/$p.h" 2>&1; e=$(date +%s%N); th=$(( (e-s)/1000000 ))
    cmp -s "$OUT/$p.b" "$OUT/$p.h" && same=same || same=DIFF
  fi
  printf "%-18s bend %7d ms  haskell %7s ms  %s\n" $p $tb $th $same
done
