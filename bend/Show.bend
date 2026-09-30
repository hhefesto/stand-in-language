import Base

# Haskell's `show` for the few types whose shown text reaches a user or a
# hash: strings (quoted, with GHC's escapes) and lists of strings.

# GHC's names for the control characters below a space (asciiTab).
def ascii_names() -> List<&2, String>:
  ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS", "HT", "LF",
   "VT", "FF", "CR", "SO", "SI", "DLE", "DC1", "DC2", "DC3", "DC4", "NAK",
   "SYN", "ETB", "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US"]

def ascii_name.got(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      s
    case None{}:
      "?"

def ascii_name(n: Nat) -> String:
  ascii_name.got(List.get(&2, String, ascii_names(), n))

# c - 48 wraps around below '0', so one comparison bounds both sides.
def is_digit(c: U32) -> Bool:
  U32.is_lt(U32.sub(c, 48), 10)

def is_h(c: U32) -> Bool:
  U32.is_eq(c, 72)

# Whether the string starts with a character satisfying p.
def next_is(~p: U32 -> Bool, s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{Chr{c}, t}:
      p(c)

# GHC's "\&": keeps an escape from running into the character after it.
def gap(g: Bool) -> String:
  match g:
    case True{}:
      "\\&"
    case False{}:
      ""

# A control character (below a space) of a shown string.
def lit.control(n: Nat, +rest: String) -> String:
  match n:
    case 7n:
      "\\a"
    case 8n:
      "\\b"
    case 9n:
      "\\t"
    case 10n:
      "\\n"
    case 11n:
      "\\v"
    case 12n:
      "\\f"
    case 13n:
      "\\r"
    case 14n:
      "\\SO" ++ gap(next_is(~is_h, rest))
    case m:
      "\\" ++ ascii_name(m)

def lit.plain(+c: U32, q: Bool, b: Bool) -> String:
  match q b:
    case True{} _:
      "\\\""
    case _ True{}:
      "\\\\"
    case _ _:
      SCon{Chr{c}, SNil{}}

def lit.pick(+c: U32, +rest: String, low: Bool, ascii: Bool, del: Bool) -> String:
  match low ascii del:
    case True{} _ _:
      lit.control(U32.to_nat(c), rest)
    case False{} True{} _:
      lit.plain(c, U32.is_eq(c, 34), U32.is_eq(c, 92))
    case False{} False{} True{}:
      "\\DEL"
    case False{} False{} False{}:
      "\\" ++ U32.show(c) ++ gap(next_is(~is_digit, rest))

# One character of a shown string, given what follows it (showLitString).
def lit.char(+c: U32, +rest: String) -> String:
  lit.pick(c, rest, U32.is_lt(c, 32), U32.is_lt(c, 127), U32.is_eq(c, 127))

# The characters of a shown string, without the quotes.
def lit(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, +t}:
      lit.char(c, t) ++ lit(t)

# show :: String -> String
def string(s: String) -> String:
  "\"" ++ lit(s) ++ "\""

def strings.go(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      "]"
    case Con{h, t}:
      "," ++ string(h) ++ strings.go(t)

# show :: [String] -> String
def strings(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      "[]"
    case Con{h, t}:
      "[" ++ string(h) ++ strings.go(t)
