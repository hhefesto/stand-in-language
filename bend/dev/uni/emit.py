# emit.py RANGES.json OUT.bend: Unicode.bend from the ranges ranges.py
# found by probing master's parser (see probe.sh).
import json, sys

r = json.load(open(sys.argv[1]))

def tree(rs):
    if not rs:
        return "UNil{}"
    m = len(rs) // 2
    lo, hi = rs[m]
    return "UNode{%d, %d, %s, %s}" % (lo, hi, tree(rs[:m]), tree(rs[m + 1:]))

def wrap(s, width=96, indent="  "):
    out, line = [], indent
    for tok in s.replace(", ", ",\x00").split("\x00"):
        if len(line) + len(tok) > width:
            out.append(line.rstrip())
            line = indent + "  "
        line += tok
    out.append(line.rstrip())
    return "\n".join(out)

head = '''import Base

# Unicode as master has it: GHC 9.10's Data.Char (isLetter, isAlphaNum,
# isSpace) and megaparsec 9.7's wide characters (two columns each). The
# ranges are master's own answers: bend/dev/uni/probe.sh runs master's
# parser on every code point above ASCII, ranges.py gathers them, and
# emit.py writes this file. Do not edit it by hand.
#
# A table is a balanced tree of ranges; ASCII never reaches one.

type UT is Data:
  UNil{}
  UNode{+lo: U32, +hi: U32, +l: UT, +r: UT}

# Where c goes from a node: left below it, right above it, a hit inside.
def ut.side(below: Bool, above: Bool, l: Unit -> Bool, r: Unit -> Bool) -> Bool:
  match below above:
    case True{} _:
      l(Unit{})
    case False{} True{}:
      r(Unit{})
    case False{} False{}:
      True{}

def ut.has(t: UT, +c: U32) -> Bool:
  match t:
    case UNil{}:
      False{}
    case UNode{lo, hi, l, r}:
      ut.side(U32.is_lt(c, lo), U32.is_gt(c, hi), u => ut.has(l, c), u => ut.has(r, c))

def ascii(c: U32) -> Bool:
  U32.is_lt(c, 128)

def az(+c: U32) -> Bool:
  U32.is_lt(U32.sub(c, 65), 26) || U32.is_lt(U32.sub(c, 97), 26)

def digit(+c: U32) -> Bool:
  U32.is_lt(U32.sub(c, 48), 10)

def pick(a: Bool, x: Bool, y: Unit -> Bool) -> Bool:
  match a:
    case True{}:
      x
    case False{}:
      y(Unit{})

'''

body = ""
for name, doc in (("letter", "isLetter (an identifier's first character)"),
                  ("alnum", "isAlphaNum (letters, marks and numbers)"),
                  ("space", "isSpace above ASCII"),
                  ("wide", "megaparsec's isWideChar")):
    body += "# %s: %d ranges.\ndef %s.table() -> UT:\n%s\n\n" % (doc, len(r[name]), name, wrap(tree(r[name])))

body += '''# Data.Char.isLetter.
def is_letter(+c: U32) -> Bool:
  pick(ascii(c), az(c), u => ut.has(letter.table(), c))

# Data.Char.isAlphaNum.
def is_alnum(+c: U32) -> Bool:
  pick(ascii(c), az(c) || digit(c), u => ut.has(alnum.table(), c))

# Data.Char.isSpace: tab to carriage return, space, and above ASCII the
# no-break space and Unicode's space separators.
def is_space(+c: U32) -> Bool:
  pick(ascii(c), U32.is_lt(U32.sub(c, 9), 5) || U32.is_eq(c, 32), u => ut.has(space.table(), c))

# The columns c takes: two when megaparsec counts it wide.
def width.of(w: Bool) -> U32:
  match w:
    case True{}:
      2
    case False{}:
      1

def width(+c: U32) -> U32:
  width.of(pick(ascii(c), False{}, u => ut.has(wide.table(), c)))
'''
open(sys.argv[2], "w").write(head + body)
