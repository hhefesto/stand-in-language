#!/bin/sh
set -e
# gen.sh: assemble bend/EALm.bend from the parts and the generated accessors
cd "$(dirname "$0")"
python3 acc.py s S S 'tb:Array<U32>' 'bp:Array<U32>' 'ci:Array<CI>' 'tp:Array<U32>' 'ts:Array<List<&2, TE>>' 'pr:Array<U32>' 'ap:Array<Ap>' 'tm:Array<Mt>' 'bd:Array<Bd>' 'nv:U32' 'vd:Nat' 'np:U32' 'pd:Nat' 'na:U32' 'ad:Nat' 'eqs:List<&2, SumEq>' 'neq:U32' 'dfs:List<&2, Df>' 'ndf:U32' 'lfs:List<&2, Lp>' 'nlf:U32' 'frame:U32' 'uni:Bool' 'err:Maybe<&2, Err>' 'cn:List<&2, CN>' 'ncn:U32' > acc.bend
python3 acc.py gr GR GR 'vx:Array<U32>' 'nd:Array<U32>' 'g:Array<List<&2, U32>>' 'gt:Array<List<&2, U32>>' 'vis:Array<U32>' 'sc:Array<U32>' 'n:U32' 'po:List<&2, U32>' 'cur:List<&2, U32>' 'trs:List<&2, List<&2, U32>>' 'ntr:U32' 'st:List<&2, DFr>' 'top:List<&2, U32>' 'pass:U32' 'tl:Array<List<&2, String>>' >> acc.bend
{ cat p1.bend; echo; echo '# Accessors (generated: /tmp/bx/eal2/acc.py)'; echo '# ---------'; echo; cat acc.bend; for f in p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13; do if [ -f $f.bdo ]; then python3 bdo.py $f.bdo p1.bend Lc=../../Loc.bend || exit 1; fi; done; } > /tmp/EALm.raw && python3 topo.py /tmp/EALm.raw > ../../EALm.bend
