#!/usr/bin/env bash
# probe.sh PARSE_ORACLE DIR: master's Unicode classes, from its own parser
# (ParseOracle.hs, bend/dev/perr), over every code point above ASCII:
#   letter: the expression `c` parses        (isLetter)
#   alnum:  `a` then c parses, c no space    (isAlphaNum)
#   space:  `if`, c, `1 then 1 else 1` parses (isSpace)
#   wide:   where `x = "c" (` fails, column 10 not 9 (isWideChar)
# then ranges.py writes DIR/ranges.json and emit.py bend/Unicode.bend.
set -euo pipefail
PO=$1; D=$2; H=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$D"; cd "$D"
python3 -I "$H/probe_cases.py"
for t in letter alnum space; do "$PO" expr $t.cases | python3 -I "$H/filt.py" > $t.out; done
"$PO" module wide.cases | python3 -I "$H/filt.py" > wide.out
python3 -I "$H/ranges.py"
python3 -I "$H/emit.py" ranges.json "$H/../../Unicode.bend"
