#!/usr/bin/env bash
# M3 test driver: runs bend/test_resolver.bend one case per process.
# Cases 0-11: res=0 means PASS. Case 12 (tictactoe compile): res=100+tokens.
# Usage: bend/run_resolver_tests.sh [bend-binary]
set -u
BEND="${1:-bend}"
names=(lit-num left-pair lambda-apply ite-false prelude-succ prelude-and
       prelude-not church-3 church-plus d2c-compiles map-compiles
       foldr-compiles tictactoe-compiles)
# Cases 0-11 exercise the INLINE resolver path (main2Term3 equivalent,
# kept for tests). Case 12 (tictactoe) runs on the SHARED path
# (test_shared.bend) — the pipeline the compiler actually uses; the inline
# path can't compile all of tictactoe in one net (documented in PORT.md).
fails=0
for i in $(seq 0 12); do
  harness=bend/test_resolver.bend
  [ "$i" -eq 12 ] && harness=bend/test_shared.bend
  out="$(timeout 300 "$BEND" run-c "$harness" "$i" 2>&1 | grep -o 'res=[0-9]*' | head -1)"
  code="${out#res=}"
  if [ "$i" -lt 12 ]; then
    if [ "$code" = "0" ]; then
      echo "PASS ${names[$i]}"
    else
      echo "FAIL ${names[$i]} (res=${code:-timeout})"
      fails=$((fails+1))
    fi
  else
    if [ -n "$code" ] && [ "$code" -ge 100 ] 2>/dev/null; then
      echo "PASS ${names[$i]} (tokens=$((code-100)))"
    else
      echo "FAIL ${names[$i]} (res=${code:-timeout})"
      fails=$((fails+1))
    fi
  fi
done
echo "failures: $fails"
exit "$fails"
