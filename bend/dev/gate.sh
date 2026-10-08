#!/usr/bin/env bash
# gate.sh [build|tests|goldens|corpus|all]...: the handoff's verifying
# checks by hand, as P1-P7 ran them. Binaries go to $GATE/bin and logs to
# $GATE/logs; GATE defaults to /tmp/telomare-gate. Run from anywhere in the
# repo, inside `nix develop`. `nix flake check` is the rest of the gate.
set -uo pipefail
S=${GATE:-/tmp/telomare-gate}
R=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
B=$S/bin
mkdir -p "$B" "$S/logs"
cd "$R"
steps=("$@"); [ ${#steps[@]} -eq 0 ] && steps=(all)
fail=0

build() {
  echo "== build telomare"
  bend bend/Main.bend -o "$B/telomare" || { echo "BUILD FAILED"; fail=1; return; }
}

tests() {
  for t in lexical front size eal ic fast telc ${EXTRA_TESTS:-}; do
    echo "== test $t"
    bend bend/tests/$t.bend -o "$B/test-$t" || { echo "BUILD FAILED $t"; fail=1; continue; }
    "$B/test-$t" > "$S/logs/test-$t.out" 2>&1
    # The expected lines, from nix/bend.nix.
    awk -v n="$t" '$0 ~ "^    "n" = \\[" {on=1; next} on && /\];/ {on=0} on {gsub(/[" ]/,""); print "ok " $0}' nix/bend.nix > "$S/logs/test-$t.exp"
    if diff "$S/logs/test-$t.exp" "$S/logs/test-$t.out" > /dev/null; then
      echo "ok: $(wc -l < "$S/logs/test-$t.out") groups"
    else
      echo "MISMATCH $t"; diff "$S/logs/test-$t.exp" "$S/logs/test-$t.out"; fail=1
    fi
  done
}

goldens() {
  echo "== goldens"
  pats=$(awk '/goldenPatterns = \[/ {on=1; next} on && /\];/ {on=0} on {gsub(/[" ]/,""); print}' nix/bend.nix)
  bash test/golden/run.sh "$B" check $pats > "$S/logs/goldens.out" 2>&1
  tail -3 "$S/logs/goldens.out"
  grep -q FAIL "$S/logs/goldens.out" && { grep FAIL "$S/logs/goldens.out"; fail=1; }
}

corpus() {
  echo "== corpus"
  cd "$R/bend/dev/corpus"
  local m=0 c=0
  # From P4 on, counts differ from haskell-final's by design: the displays
  # must still equal its --ic ones (or its reference evaluator's, P.hs-run,
  # where its IC ran dry), and the whole output the port's record when there
  # is one (P.port-ic-meter; CORPUS_RECORD=1 writes them).
  for f in *.hs-ic-meter; do
    p=${f%.hs-ic-meter}
    o=$S/logs/corpus-$p.meter
    timeout 600 "$B/telomare" $p.tel --meter < /dev/null > $o 2>&1
    [ -n "${CORPUS_RECORD:-}" ] && cp $o $p.port-ic-meter
    want=$f; [ -f $p.port-ic-meter ] && want=$p.port-ic-meter
    ref=$f; [ -f $p.hs-run ] && ref=$p.hs-run
    if ! diff -q <(grep -v '^IC interactions' $o) <(grep -v '^IC interactions' $ref) > /dev/null; then echo "METER DISPLAY DIFF $p"; fail=1
    elif ! diff -q $o $want > /dev/null; then echo "METER DIFF $p"; fail=1
    else m=$((m+1)); fi
  done
  # From P7.2 on, the report has a checks section haskell-final's lacks:
  # without it, the report must equal haskell-final's, and whole, the
  # port's record (P.port-certificate; CORPUS_RECORD=1 writes them).
  for f in *.hs-certificate; do
    p=${f%.hs-certificate}
    o=$S/logs/corpus-$p.certificate
    { timeout 600 "$B/telomare" $p.tel --certificate < /dev/null 2>&1; echo "status $?"; } > $o
    [ -n "${CORPUS_RECORD:-}" ] && cp $o $p.port-certificate
    want=$f; [ -f $p.port-certificate ] && want=$p.port-certificate
    if ! diff -q <(awk '/^refinement checks/ {skip=1} skip && /^$/ {skip=0; next} !skip' $o) $f > /dev/null; then echo "CERT REPORT DIFF $p"; fail=1
    elif ! diff -q $o $want > /dev/null; then echo "CERT DIFF $p"; fail=1
    else c=$((c+1)); fi
  done
  echo "meters same: $m; certificates same: $c"
  cd "$R"
}

for s in "${steps[@]}"; do
  case $s in
    build) build ;;
    tests) tests ;;
    goldens) goldens ;;
    corpus) corpus ;;
    all) build; tests; goldens; corpus ;;
  esac
done
[ $fail -eq 0 ] && echo "GATE OK" || echo "GATE FAILED"
exit $fail
