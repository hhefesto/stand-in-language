#!/bin/sh
# one.sh PROG.tel: run master's telomare and the port on PROG in each mode
# and record a difference (exit, stdout, stderr) under diff/.
P=$1; n=$(basename $P .tel); D=/tmp/bx/fz
M=/tmp/bx/oracle98/telomare; B=${PORT:-/tmp/telomare-gate-1030/bin/telomare}
cd $D/work 2>/dev/null || { mkdir -p $D/work; cd $D/work; }
cp -f $D/Prelude.tel . 2>/dev/null
for mode in run meter fast certificate ic; do
  case $mode in run) a="";; meter) a="--meter";; fast) a="--fast";; certificate) a="--certificate";; ic) a="--ic";; esac
  for who in m b; do
    [ $who = m ] && X=$M || X=$B
    s=$(date +%s%N)
    echo | timeout 60 $X $P $a > $D/out/$n.$mode.$who 2>&1; e=$?
    t=$(( ($(date +%s%N) - s) / 1000000 ))
    echo "exit $e" >> $D/out/$n.$mode.$who
    echo "$n $mode $who $e $t" >> $D/times.log
  done
  if grep -qx 'exit 124' $D/out/$n.$mode.m || grep -qx 'exit 124' $D/out/$n.$mode.b; then
    echo "$n $mode" >> $D/timeouts.log
  elif ! cmp -s $D/out/$n.$mode.m $D/out/$n.$mode.b; then
    echo "$n $mode" >> $D/diffs.log
  fi
done
