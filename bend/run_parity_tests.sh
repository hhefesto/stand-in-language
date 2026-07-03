#!/usr/bin/env bash
# M6 parity harness: pipe the same move scripts through the Haskell
# telomare and the Bend-hosted telomare, diff the transcripts.
# Usage: bend/run_parity_tests.sh <haskell-telomare-bin> [scratch-dir]
# Requires: nix (for the bend runner), timeout.
set -u
ORACLE="${1:?usage: run_parity_tests.sh <telomare-bin> [scratch]}"
SCRATCH="${2:-$(mktemp -d)}"
mkdir -p "$SCRATCH"

declare -A scripts
scripts[p1-row-win]='1
4
2
5
3'
scripts[p2-col-win]='5
1
6
4
9
7'
scripts[tie]='1
2
3
5
4
6
8
7
9'
scripts[invalid-then-quit]='x
0
1
1
q'

fails=0
for name in "${!scripts[@]}"; do
  printf '%s\n' "${scripts[$name]}" > "$SCRATCH/$name.in"
  # Haskell oracle reads stdin lines
  timeout 120 "$ORACLE" tictactoe.tel < "$SCRATCH/$name.in" > "$SCRATCH/$name.oracle" 2>&1
  # Bend compiler (two-stage driver; the compile is cached after the first
  # run, so the suite pays stage-1 once and stage-2 per script)
  timeout 7200 bend/run_telomare_bend.sh tictactoe.tel < "$SCRATCH/$name.in" > "$SCRATCH/$name.bend" 2>&1
  if diff -u "$SCRATCH/$name.oracle" "$SCRATCH/$name.bend" > "$SCRATCH/$name.diff"; then
    echo "PASS $name"
  else
    echo "FAIL $name (see $SCRATCH/$name.diff)"
    fails=$((fails+1))
  fi
done
echo "failures: $fails"
exit "$fails"
