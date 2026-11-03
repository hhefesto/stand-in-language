#!/bin/sh
# (post.bend built as /tmp/bx/post/pb, master's cert-oracle as /tmp/bx/certm/co; both print the
# post phase: the faithful verdict, the derivation, certifiedProgramFrom's verdict and guidance.)
# Port (pb) vs master (cert-oracle post) on the golden and corpus programs,
# each side in its own unit capped at 8G.
cd /tmp/bx/post
T=/home/hhefesto/src/telomare
cp $T/test/programs/*.tel $T/test/programs/limits/*.tel $T/tictactoe.tel .
for f in $T/bend/dev/corpus/*.tel; do b=$(basename $f); [ "$b" = Prelude.tel ] || cp $f .; done
run() { # unit, out, cmd
  systemd-run --user --wait --collect --unit=$1 --slice=telomare.slice -p WorkingDirectory=/tmp/bx/post -p MemoryMax=8G -p MemorySwapMax=0 /run/current-system/sw/bin/sh -c "$3 > $2 2>&1" 2>&1 | grep -i 'result:\|runtime:\|peak:' | tr -s ' ' | tr '\n' ' '
}
for n in ${ONLY:-tc_ultra_minimal simpleplus testchar over-budget-recursion unbounded-input-recursion casea casei cases ctall ctign ctprop ctstr natarith natudt nonex patlam qual rat ratarith fact arith tictactoe}; do
  echo $n > post.args
  p=$(run tel-pp-$n $n.port "timeout 1200 ./pb")
  m=$(run tel-pm-$n $n.master "timeout 1200 /tmp/bx/certm/co $n $n.tel post")
  echo "$n | port: $p | master: $m | $(python3 /home/hhefesto/src/telomare/bend/dev/ealm/test/post-cmp.py $n.port $n.master 2>&1 | tail -1)"
done
