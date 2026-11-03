#!/bin/sh
while systemctl --user is-active -q tel-fuzz1; do sleep 30; done
cd /tmp/bx/fz && python3 gen2.py 4 800 progs2 && ls progs2/*.tel | xargs -P 8 -n 1 sh -c './one.sh $PWD/$0'
echo "campaign2 done $(date)" >> /tmp/bx/fz/campaign.log
