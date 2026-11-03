#!/bin/sh
# 8 at a time, in telomare.slice (its cores are 4-7,12-15)
cd /tmp/bx/fz && ls progs/*.tel | xargs -P 8 -n 1 sh -c './one.sh $PWD/$0'
echo "campaign done $(date)" >> /tmp/bx/fz/campaign.log
