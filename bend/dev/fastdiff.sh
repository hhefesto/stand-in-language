#!/usr/bin/env bash
# fastdiff.sh BIN [SESSIONS [SEED]]: sized runs against --fast ones
# (HANDOFF-sizing-proof.md S0.2). tictactoe and simpleplus are fed generated
# input, once sized and once unbounded, and every session whose displays
# differ is printed with its input. A difference is an over-run (an erased
# bottom reached: an IC stuck error) or a check discharged wrongly. It
# reaches only states a session reaches; the laws cover every state the
# guard admits. Run from anywhere in the repo.
set -uo pipefail
B=${1:?usage: fastdiff.sh BIN [SESSIONS [SEED]]}
N=${2:-100}
RANDOM=${3:-1}
R=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$R"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT

# Lines a player might type, good and bad.
pool=(1 2 3 4 5 6 7 8 9 1 2 3 4 5 6 7 8 9 0 10 11 99 q a z "" " " "1 2" "12"
  "123456789" "999999999999999999999" x9 9x "-1" "%")
digits=(0 1 2 3 4 5 6 7 8 9 a z " " "" 10 99)

diffs=0
run() { # program, input file
  "$B" "$1" < "$2" > "$T/sized" 2>&1
  "$B" "$1" --fast < "$2" > "$T/fast" 2>&1
  if ! diff -q "$T/sized" "$T/fast" > /dev/null; then
    diffs=$((diffs+1))
    echo "== $1 differs on input:"; sed 's/^/  > /' "$2"
    diff "$T/sized" "$T/fast" | head -20
  fi
}

for ((i = 0; i < N; i++)); do
  : > "$T/in"
  for ((k = 0; k < 4 + RANDOM % 9; k++)); do
    printf '%s\n' "${pool[RANDOM % ${#pool[@]}]}" >> "$T/in"
  done
  run tictactoe.tel "$T/in"
  printf '%s %s\n' "${digits[RANDOM % ${#digits[@]}]}" "${digits[RANDOM % ${#digits[@]}]}" > "$T/in"
  run simpleplus.tel "$T/in"
done
echo "sessions: $((2 * N)); differing: $diffs"
