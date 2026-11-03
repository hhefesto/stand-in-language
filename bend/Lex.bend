import Base
import ./Loc.bend as L
import ./Lexical.bend as X
import ./Unicode.bend as U

# The tokenizer under the parser (the lexical half of haskell-final's
# megaparsec parser). One character at a time through a state machine, so
# the recursion is structural on the text. Each token records where it
# starts, where the whitespace before it stopped being same-line whitespace
# (`ws`) and whether a newline came before it (`nl`): megaparsec's layout
# rules (an application continues onto a later line only right of its head,
# a let's definitions share a column) and one location depend on those.

type TK is Data:
  KId{+name: String}
  KKw{+word: String}
  KNat{+n: U32}
  KChurch{+n: U32}
  KStr{+s: String, +spaced: Bool}
  KSym{+c: U32}
  KBad{+c: U32}
  KEnd{}

type Tok is Data:
  Tok{+k: TK, +at: L.Pos, +ws: L.Pos, +nl: Bool}

type LexErr is Data:
  LexErr{+at: L.Pos, +msg: String}

# The state between characters. The gap and the comments inside it carry
# the pending token's `ws` and `nl`; a token in progress carries its start
# as well.
type LS is Data:
  LGap{+ws: L.Pos, +nl: Bool}
  LLine{+ws: L.Pos, +nl: Bool}
  LBlock{+ws: L.Pos, +nl: Bool, +depth: Nat, +prev: U32}
  LId{+start: L.Pos, +ws: L.Pos, +nl: Bool, +acc: String}
  LNat{+start: L.Pos, +ws: L.Pos, +nl: Bool, +val: U32, +big: Bool}
  LDollar{+start: L.Pos, +ws: L.Pos, +nl: Bool}
  LChurch{+start: L.Pos, +ws: L.Pos, +nl: Bool, +val: U32, +big: Bool}
  LStr{+start: L.Pos, +ws: L.Pos, +nl: Bool, +acc: String, +left: U32}
  LStrEnd{+start: L.Pos, +ws: L.Pos, +nl: Bool, +s: String}
  LEsc{+start: L.Pos, +ws: L.Pos, +nl: Bool, +acc: String, +left: U32}
  LEscNum{+start: L.Pos, +ws: L.Pos, +nl: Bool, +acc: String, +base: U32, +val: U32, +seen: Bool, +used: U32}
  LEscCtl{+start: L.Pos, +ws: L.Pos, +nl: Bool, +acc: String}
  LEscName{+start: L.Pos, +ws: L.Pos, +nl: Bool, +acc: String, +name: String}
  LDash{+start: L.Pos, +ws: L.Pos, +nl: Bool}
  LBrace{+start: L.Pos, +ws: L.Pos, +nl: Bool}

type LR is Data:
  LOk{+st: LS, +toks: List<&2, Tok>}
  LFail{+e: LexErr}

# Character classes
# -----------------

type Esc is Data:
  Esc{+from: U32, +to: U32}

# `->` is one symbol; every other symbol is its character.
def arrow() -> U32:
  1

def in_range(c: U32, lo: U32, n: U32) -> Bool:
  U32.is_lt(U32.sub(c, lo), n)

def is_digit(c: U32) -> Bool:
  in_range(c, 48, 10)

def is_ident(+c: U32) -> Bool:
  U.is_alnum(c) || U32.is_eq(c, 95) || U32.is_eq(c, 46)

# Space or tab: what the same-line space consumer eats.
def is_blank(+c: U32) -> Bool:
  U32.is_eq(c, 32) || U32.is_eq(c, 9)

# ( ) [ ] } , = : \ # _
def is_sym(+c: U32) -> Bool:
  U32.is_eq(c, 40) || U32.is_eq(c, 41) || U32.is_eq(c, 91) || U32.is_eq(c, 93)
    || U32.is_eq(c, 125) || U32.is_eq(c, 44) || U32.is_eq(c, 61)
    || U32.is_eq(c, 58) || U32.is_eq(c, 92) || U32.is_eq(c, 35)
    || U32.is_eq(c, 95)

# Positions
# ---------

def next.pos.at(nl: Bool, tab: Bool, +c: U32, +line: U32, +col: U32, off: U32) -> L.Pos:
  match nl tab:
    case True{} _:
      L.Pos{(line + 1 : U32), 1, off}
    case False{} True{}:
      L.Pos{line, (((col - 1) / 8 + 1) * 8 + 1 : U32), off}
    case False{} False{}:
      L.Pos{line, (col + U.width(c) : U32), off}

# The position after character c (a tab moves to the next multiple of 8,
# plus 1; a wide character takes two columns).
def next.pos(+c: U32, p: L.Pos) -> L.Pos:
  match p:
    case L.Pos{+line, +col, off}:
      next.pos.at(U32.is_eq(c, 10), U32.is_eq(c, 9), c, line, col, (off + 1 : U32))

# Tokens
# ------

def ident.kind(+s: String, kw: Bool) -> TK:
  match kw:
    case True{}:
      KKw{s}
    case False{}:
      KId{s}

def ident(acc: String) -> TK:
  +s = String.reverse(acc)
  ident.kind(s, X.is_reserved(s))

def tok(k: TK, +at: L.Pos, ws: L.Pos, nl: Bool) -> Tok:
  match nl:
    case True{}:
      Tok{k, at, ws, True{}}
    case False{}:
      Tok{k, at, at, False{}}

# One more decimal digit onto a literal, noting when it no longer fits a
# U32.
def digit(+val: U32, +d: U32, big: Bool) -> U32 & Bool:
  (((val * 10) + d : U32), big || U32.is_gt(val, 429496729)
    || (U32.is_eq(val, 429496729) && U32.is_gt(d, 5)))

def fail(at: L.Pos, msg: String) -> LR:
  LFail{LexErr{at, msg}}

def add.nat(+start: L.Pos, ws: L.Pos, nl: Bool, toks: List<&2, Tok>, r: U32 & Bool) -> LR:
  (val, big) = r
  LOk{LNat{start, ws, nl, val, big}, toks}

def add.church(+start: L.Pos, ws: L.Pos, nl: Bool, toks: List<&2, Tok>, r: U32 & Bool) -> LR:
  (val, big) = r
  LOk{LChurch{start, ws, nl, val, big}, toks}

# The gap between tokens
# ----------------------

# The first character the same-line space consumer does not eat is where
# the whitespace went past the line.
def gap.newline(+p: L.Pos, ws: L.Pos, nl: Bool, toks: List<&2, Tok>) -> LR:
  match nl:
    case True{}:
      LOk{LGap{ws, True{}}, toks}
    case False{}:
      LOk{LGap{p, True{}}, toks}

def gap.open(+c: U32, +p: L.Pos, ws: L.Pos, nl: Bool, toks: List<&2, Tok>,
             quote: Bool, dollar: Bool, dash: Bool, brace: Bool) -> LR:
  match quote dollar dash brace:
    case True{} _ _ _:
      LOk{LStr{p, ws, nl, SNil{}, 0}, toks}
    case False{} True{} _ _:
      LOk{LDollar{p, ws, nl}, toks}
    case False{} False{} True{} _:
      LOk{LDash{p, ws, nl}, toks}
    case False{} False{} False{} True{}:
      LOk{LBrace{p, ws, nl}, toks}
    case False{} False{} False{} False{}:
      LOk{LGap{p, False{}}, tok(KBad{c}, p, ws, nl) <> toks}

def gap.pick(+c: U32, +p: L.Pos, ws: L.Pos, nl: Bool, toks: List<&2, Tok>,
             blank: Bool, space: Bool, alpha: Bool, dig: Bool, sym: Bool) -> LR:
  match blank space alpha dig sym:
    case True{} _ _ _ _:
      LOk{LGap{ws, nl}, toks}
    case False{} True{} _ _ _:
      gap.newline(p, ws, nl, toks)
    case False{} False{} True{} _ _:
      LOk{LId{p, ws, nl, SCon{Chr{c}, SNil{}}}, toks}
    case False{} False{} False{} True{} _:
      LOk{LNat{p, ws, nl, (c - 48 : U32), False{}}, toks}
    case False{} False{} False{} False{} True{}:
      LOk{LGap{p, False{}}, tok(KSym{c}, p, ws, nl) <> toks}
    case False{} False{} False{} False{} False{}:
      gap.open(c, p, ws, nl, toks, U32.is_eq(c, 34), U32.is_eq(c, 36),
               U32.is_eq(c, 45), U32.is_eq(c, 123))

# A character in the gap between tokens.
def gap(+c: U32, +p: L.Pos, ws: L.Pos, nl: Bool, toks: List<&2, Tok>) -> LR:
  gap.pick(c, p, ws, nl, toks, is_blank(c), U.is_space(c), U.is_letter(c),
           is_digit(c), is_sym(c))

# A finished token, then the character that ended it, back in the gap.
def emit(k: TK, start: L.Pos, ws: L.Pos, nl: Bool, +c: U32, +p: L.Pos,
         toks: List<&2, Tok>) -> LR:
  gap(c, p, p, False{}, tok(k, start, ws, nl) <> toks)

def emit.num(~K: U32 -> TK, start: L.Pos, ws: L.Pos, nl: Bool, val: U32,
             big: Bool, +c: U32, +p: L.Pos, toks: List<&2, Tok>) -> LR:
  match big:
    case True{}:
      fail(start, "natural literal exceeds the supported range")
    case False{}:
      emit(K(val), start, ws, nl, c, p, toks)

def mk.nat(n: U32) -> TK:
  KNat{n}

def mk.church(n: U32) -> TK:
  KChurch{n}

# Strings
# -------

# The one-letter escapes of Haskell's character literals.
def escapes() -> List<&2, Esc>:
  [Esc{97, 7}, Esc{98, 8}, Esc{102, 12}, Esc{110, 10}, Esc{114, 13},
   Esc{116, 9}, Esc{118, 11}, Esc{92, 92}, Esc{34, 34}, Esc{39, 39}]

def esc.first(hit: Bool, to: U32, later: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{to}
    case False{}:
      later

def esc.look(+c: U32, es: List<&2, Esc>) -> Maybe<&2, U32>:
  match es:
    case Nil{}:
      None{}
    case Con{Esc{from, to}, rest}:
      esc.first(U32.is_eq(from, c), to, esc.look(c, rest))

def digit.val.raw(+c: U32, dec: Bool, lo: Bool, hi: Bool) -> U32:
  match dec lo hi:
    case True{} _ _:
      (c - 48 : U32)
    case False{} True{} _:
      (c - 87 : U32)
    case False{} False{} True{}:
      (c - 55 : U32)
    case False{} False{} False{}:
      99

def digit.val.fit.go(+base: U32, d: U32, ok: Bool) -> U32:
  match ok:
    case True{}:
      d
    case False{}:
      base

def digit.val.fit(+base: U32, +d: U32) -> U32:
  digit.val.fit.go(base, d, U32.is_lt(d, base))

def digit.val.pick(+c: U32, +base: U32, dec: Bool, lo: Bool, hi: Bool) -> U32:
  digit.val.fit(base, digit.val.raw(c, dec, lo, hi))

# The value of a digit in base 8, 10 or 16, or the base itself when c is
# no such digit.
def digit.val(+c: U32, +base: U32) -> U32:
  digit.val.pick(c, base, is_digit(c), in_range(c, 97, 6), in_range(c, 65, 6))

# Space or a comment after a string literal: a string pattern takes none, so
# a lambda's parameters end there.
def str.spaced(+c: U32) -> Bool:
  U.is_space(c) || U32.is_eq(c, 45) || U32.is_eq(c, 123)

# A character inside a string literal. Master reads one with megaparsec's
# charLiteral: readLitChar on the next ten characters, which takes one
# character and every `\&` after it inside those ten. `left` is how many of
# the ten remain for those `\&`s; a `\&` beyond them, or first in the string,
# is an error, and a numeric escape stops at the tenth.
def str.char.pick(+c: U32, +p: L.Pos, +start: L.Pos, ws: L.Pos, nl: Bool,
                  acc: String, toks: List<&2, Tok>, +left: U32, quote: Bool, slash: Bool) -> LR:
  match quote slash:
    case True{} _:
      LOk{LStrEnd{start, ws, nl, String.reverse(acc)}, toks}
    case False{} True{}:
      LOk{LEsc{start, ws, nl, acc, left}, toks}
    case False{} False{}:
      LOk{LStr{start, ws, nl, SCon{Chr{c}, acc}, 9}, toks}

def str.char(+c: U32, +p: L.Pos, +start: L.Pos, ws: L.Pos, nl: Bool,
             acc: String, toks: List<&2, Tok>, +left: U32) -> LR:
  str.char.pick(c, p, start, ws, nl, acc, toks, left, U32.is_eq(c, 34), U32.is_eq(c, 92))

def esc.num.base(+c: U32, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
                 toks: List<&2, Tok>, dec: Bool, hex: Bool, oct: Bool) -> LR:
  match dec hex oct:
    case True{} _ _:
      LOk{LEscNum{start, ws, nl, acc, 10, (c - 48 : U32), True{}, 2}, toks}
    case False{} True{} _:
      LOk{LEscNum{start, ws, nl, acc, 16, 0, False{}, 2}, toks}
    case False{} False{} True{}:
      LOk{LEscNum{start, ws, nl, acc, 8, 0, False{}, 2}, toks}
    case False{} False{} False{}:
      fail(start, "unsupported escape in string literal")

def esc.char.got(+c: U32, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
                 toks: List<&2, Tok>, m: Maybe<&2, U32>) -> LR:
  match m:
    case Some{x}:
      LOk{LStr{start, ws, nl, SCon{Chr{x}, acc}, 8}, toks}
    case None{}:
      esc.num.base(c, start, ws, nl, acc, toks, is_digit(c),
                   U32.is_eq(c, 120) || U32.is_eq(c, 88),
                   U32.is_eq(c, 111) || U32.is_eq(c, 79))

# The ASCII control names of Haskell's character escapes (`\SOH` and
# `\SO`: the longest name wins).
type Asc is Data:
  Asc{+name: String, +code: U32}

def asc.names() -> List<&2, Asc>:
  [Asc{"NUL", 0}, Asc{"SOH", 1}, Asc{"STX", 2}, Asc{"ETX", 3}, Asc{"EOT", 4},
   Asc{"ENQ", 5}, Asc{"ACK", 6}, Asc{"BEL", 7}, Asc{"BS", 8}, Asc{"HT", 9},
   Asc{"LF", 10}, Asc{"VT", 11}, Asc{"FF", 12}, Asc{"CR", 13}, Asc{"SO", 14},
   Asc{"SI", 15}, Asc{"DLE", 16}, Asc{"DC1", 17}, Asc{"DC2", 18}, Asc{"DC3", 19},
   Asc{"DC4", 20}, Asc{"NAK", 21}, Asc{"SYN", 22}, Asc{"ETB", 23}, Asc{"CAN", 24},
   Asc{"EM", 25}, Asc{"SUB", 26}, Asc{"ESC", 27}, Asc{"FS", 28}, Asc{"GS", 29},
   Asc{"RS", 30}, Asc{"US", 31}, Asc{"SP", 32}, Asc{"DEL", 127}]

# Whether some name starts with `pre`; the code of the name that is `pre`.
def asc.prefix(es: List<&2, Asc>, +pre: String) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{Asc{name, code}, rest}:
      String.starts_with(name, pre) || asc.prefix(rest, pre)

def asc.exact(es: List<&2, Asc>, +pre: String) -> Maybe<&2, U32>:
  match es:
    case Nil{}:
      None{}
    case Con{Asc{name, code}, rest}:
      esc.first(String.eq(name, pre), code, asc.exact(rest, pre))

# `\&` is no character: after one it is skipped (GHC's lexChar takes it
# with the character before); first in a string it is an error.
def esc.empty(+start: L.Pos, ws: L.Pos, nl: Bool, acc: String, toks: List<&2, Tok>,
              +left: U32, fits: Bool) -> LR:
  match fits:
    case True{}:
      LOk{LStr{start, ws, nl, acc, (left - 2 : U32)}, toks}
    case False{}:
      fail(start, "unsupported escape in string literal")

def esc.char.kind(+c: U32, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
                  toks: List<&2, Tok>, +left: U32, amp: Bool, hat: Bool, upper: Bool) -> LR:
  match amp hat upper:
    case True{} _ _:
      esc.empty(start, ws, nl, acc, toks, left, U32.is_gt(left, 1))
    case False{} True{} _:
      LOk{LEscCtl{start, ws, nl, acc}, toks}
    case False{} False{} True{}:
      LOk{LEscName{start, ws, nl, acc, SCon{Chr{c}, SNil{}}}, toks}
    case False{} False{} False{}:
      esc.char.got(c, start, ws, nl, acc, toks, esc.look(c, escapes()))

# The character after a backslash in a string.
def esc.char(+c: U32, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
             toks: List<&2, Tok>, +left: U32) -> LR:
  esc.char.kind(c, start, ws, nl, acc, toks, left, U32.is_eq(c, 38), U32.is_eq(c, 94),
                in_range(c, 65, 26) && U32.is_ne(c, 88) && U32.is_ne(c, 79))

# `\^@` to `\^_`: the control characters 0 to 31.
def esc.ctl(+c: U32, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
            toks: List<&2, Tok>, ok: Bool) -> LR:
  match ok:
    case True{}:
      LOk{LStr{start, ws, nl, SCon{Chr{(c - 64 : U32)}, acc}, 7}, toks}
    case False{}:
      fail(start, "unsupported escape in string literal")

# A name's characters so far, and the next: on while some name goes on so,
# else the name so far, then c as any character of the string.
def esc.name.end(+c: U32, +p: L.Pos, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
                 toks: List<&2, Tok>, +name: String, m: Maybe<&2, U32>) -> LR:
  match m:
    case Some{x}:
      str.char(c, p, start, ws, nl, SCon{Chr{x}, acc}, toks,
               (9 - U32.from_nat(String.length(name)) : U32))
    case None{}:
      fail(start, "unsupported escape in string literal")

def esc.name.on(+c: U32, +p: L.Pos, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
                toks: List<&2, Tok>, +name: String, +longer: String, more: Bool) -> LR:
  match more:
    case True{}:
      LOk{LEscName{start, ws, nl, acc, longer}, toks}
    case False{}:
      esc.name.end(c, p, start, ws, nl, acc, toks, name, asc.exact(asc.names(), name))

def esc.name(+c: U32, +p: L.Pos, +start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
             toks: List<&2, Tok>, +name: String) -> LR:
  +longer = name ++ SCon{Chr{c}, SNil{}}
  esc.name.on(c, p, start, ws, nl, acc, toks, name, longer, asc.prefix(asc.names(), longer))

# The tenth character ends a numeric escape, digits or not: the rest are
# characters of their own.
def esc.num.put(+start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
                toks: List<&2, Tok>, base: U32, +val: U32, +used: U32, over: Bool, full: Bool) -> LR:
  match over full:
    case True{} _:
      fail(start, "character escape out of range")
    case False{} True{}:
      LOk{LStr{start, ws, nl, SCon{Chr{val}, acc}, 0}, toks}
    case False{} False{}:
      LOk{LEscNum{start, ws, nl, acc, base, val, True{}, used}, toks}

def esc.num.next(+start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
                 toks: List<&2, Tok>, base: U32, +val: U32, +used: U32) -> LR:
  esc.num.put(start, ws, nl, acc, toks, base, val, used, U32.is_gt(val, 1114111), U32.is_eq(used, 10))

# A digit of a numeric escape, or the character after it.
def esc.num.more(+c: U32, +p: L.Pos, +start: L.Pos, ws: L.Pos, nl: Bool,
                 acc: String, toks: List<&2, Tok>, +base: U32, +val: U32,
                 seen: Bool, +used: U32, +d: U32, more: Bool) -> LR:
  match seen more:
    case _ True{}:
      esc.num.next(start, ws, nl, acc, toks, base, ((val * base) + d : U32), (used + 1 : U32))
    case True{} False{}:
      str.char(c, p, start, ws, nl, SCon{Chr{val}, acc}, toks, (10 - used : U32))
    case False{} False{}:
      fail(start, "unsupported escape in string literal")

# Comments
# --------

def line.char(+c: U32, +p: L.Pos, ws: L.Pos, nl: Bool, toks: List<&2, Tok>,
              end: Bool) -> LR:
  match end:
    case True{}:
      gap(c, p, ws, nl, toks)
    case False{}:
      LOk{LLine{ws, nl}, toks}

def block.close(ws: L.Pos, nl: Bool, depth: Nat, toks: List<&2, Tok>) -> LR:
  match depth:
    case 1n+0n:
      LOk{LGap{ws, nl}, toks}
    case 1n+d:
      LOk{LBlock{ws, nl, d, 0}, toks}
    case 0n:
      LOk{LGap{ws, nl}, toks}

# Block comments nest: "-}" closes one level (tried first, as megaparsec
# does), "{-" opens another.
def block.char(+c: U32, ws: L.Pos, nl: Bool, depth: Nat, toks: List<&2, Tok>,
               close: Bool, open: Bool) -> LR:
  match close open:
    case True{} _:
      block.close(ws, nl, depth, toks)
    case False{} True{}:
      LOk{LBlock{ws, nl, 1n+depth, 0}, toks}
    case False{} False{}:
      LOk{LBlock{ws, nl, depth, c}, toks}

# Tokens in progress
# ------------------

def id.char(+c: U32, +p: L.Pos, start: L.Pos, ws: L.Pos, nl: Bool, acc: String,
            toks: List<&2, Tok>, more: Bool) -> LR:
  match more:
    case True{}:
      LOk{LId{start, ws, nl, SCon{Chr{c}, acc}}, toks}
    case False{}:
      emit(ident(acc), start, ws, nl, c, p, toks)

def nat.char(+c: U32, +p: L.Pos, start: L.Pos, ws: L.Pos, nl: Bool, val: U32,
             big: Bool, toks: List<&2, Tok>, more: Bool) -> LR:
  match more:
    case True{}:
      add.nat(start, ws, nl, toks, digit(val, (c - 48 : U32), big))
    case False{}:
      emit.num(~mk.nat, start, ws, nl, val, big, c, p, toks)

def church.char(+c: U32, +p: L.Pos, start: L.Pos, ws: L.Pos, nl: Bool, val: U32,
                big: Bool, toks: List<&2, Tok>, more: Bool) -> LR:
  match more:
    case True{}:
      add.church(start, ws, nl, toks, digit(val, (c - 48 : U32), big))
    case False{}:
      emit.num(~mk.church, start, ws, nl, val, big, c, p, toks)

# "$" takes a natural right after it; alone it is no token.
def dollar.char(+c: U32, +p: L.Pos, start: L.Pos, ws: L.Pos, nl: Bool,
                toks: List<&2, Tok>, dig: Bool) -> LR:
  match dig:
    case True{}:
      LOk{LChurch{start, ws, nl, (c - 48 : U32), False{}}, toks}
    case False{}:
      emit(KBad{36}, start, ws, nl, c, p, toks)

# "--" starts a line comment (so "-->" does too), "->" is the arrow, and a
# "-" alone is no token.
def dash.char(+c: U32, +p: L.Pos, start: L.Pos, ws: L.Pos, nl: Bool,
              toks: List<&2, Tok>, dash: Bool, gt: Bool) -> LR:
  match dash gt:
    case True{} _:
      LOk{LLine{ws, nl}, toks}
    case False{} True{}:
      LOk{LGap{p, False{}}, tok(KSym{arrow()}, start, ws, nl) <> toks}
    case False{} False{}:
      emit(KBad{45}, start, ws, nl, c, p, toks)

# "{-" starts a block comment; "{" alone is the brace.
def brace.char(+c: U32, +p: L.Pos, start: L.Pos, ws: L.Pos, nl: Bool,
               toks: List<&2, Tok>, dash: Bool) -> LR:
  match dash:
    case True{}:
      LOk{LBlock{ws, nl, 1n, 0}, toks}
    case False{}:
      emit(KSym{123}, start, ws, nl, c, p, toks)

# The machine
# -----------

# Character c, at position p, in state st.
def step(+c: U32, +p: L.Pos, st: LS, toks: List<&2, Tok>) -> LR:
  match st:
    case LGap{ws, nl}:
      gap(c, p, ws, nl, toks)
    case LLine{ws, nl}:
      line.char(c, p, ws, nl, toks, U32.is_eq(c, 10))
    case LBlock{ws, nl, depth, +prev}:
      block.char(c, ws, nl, depth, toks, U32.is_eq(prev, 45) && U32.is_eq(c, 125),
                 U32.is_eq(prev, 123) && U32.is_eq(c, 45))
    case LId{start, ws, nl, acc}:
      id.char(c, p, start, ws, nl, acc, toks, is_ident(c))
    case LNat{start, ws, nl, val, big}:
      nat.char(c, p, start, ws, nl, val, big, toks, is_digit(c))
    case LDollar{start, ws, nl}:
      dollar.char(c, p, start, ws, nl, toks, is_digit(c))
    case LChurch{start, ws, nl, val, big}:
      church.char(c, p, start, ws, nl, val, big, toks, is_digit(c))
    case LStr{start, ws, nl, acc, left}:
      str.char(c, p, start, ws, nl, acc, toks, left)
    case LStrEnd{start, ws, nl, x}:
      emit(KStr{x, str.spaced(c)}, start, ws, nl, c, p, toks)
    case LEsc{start, ws, nl, acc, left}:
      esc.char(c, start, ws, nl, acc, toks, left)
    case LEscCtl{start, ws, nl, acc}:
      esc.ctl(c, start, ws, nl, acc, toks, in_range(c, 64, 32))
    case LEscName{start, ws, nl, acc, name}:
      esc.name(c, p, start, ws, nl, acc, toks, name)
    case LEscNum{start, ws, nl, acc, +base, val, seen, used}:
      +d = digit.val(c, base)
      esc.num.more(c, p, start, ws, nl, acc, toks, base, val, seen, used, d, U32.is_lt(d, base))
    case LDash{start, ws, nl}:
      dash.char(c, p, start, ws, nl, toks, U32.is_eq(c, 45), U32.is_eq(c, 62))
    case LBrace{start, ws, nl}:
      brace.char(c, p, start, ws, nl, toks, U32.is_eq(c, 45))

def lex.step(+c: U32, +p: L.Pos, r: LR) -> LR:
  match r:
    case LFail{e}:
      LFail{e}
    case LOk{st, toks}:
      step(c, p, st, toks)

def lex.go(s: String, +p: L.Pos, r: LR) -> LR & L.Pos:
  match s:
    case SNil{}:
      (r, p)
    case SCon{Chr{+c}, t}:
      lex.go(t, next.pos(c, p), lex.step(c, p, r))

def lex.end(ws: L.Pos, nl: Bool, +p: L.Pos, toks: List<&2, Tok>) ->
  Result<&2, &2, LexErr, List<&2, Tok>>:
  Done{List.reverse(&2, Tok, tok(KEnd{}, p, ws, nl) <> toks)}

def lex.last(k: TK, start: L.Pos, ws: L.Pos, nl: Bool, +p: L.Pos,
             toks: List<&2, Tok>) -> Result<&2, &2, LexErr, List<&2, Tok>>:
  lex.end(p, False{}, p, tok(k, start, ws, nl) <> toks)

def lex.last.num(k: TK, start: L.Pos, ws: L.Pos, nl: Bool, big: Bool, +p: L.Pos,
                 toks: List<&2, Tok>) -> Result<&2, &2, LexErr, List<&2, Tok>>:
  match big:
    case True{}:
      Fail{LexErr{start, "natural literal exceeds the supported range"}}
    case False{}:
      lex.last(k, start, ws, nl, p, toks)

# The end of the text: finish the token in progress, then the end token.
def flush(st: LS, +p: L.Pos, toks: List<&2, Tok>) -> Result<&2, &2, LexErr, List<&2, Tok>>:
  match st:
    case LGap{ws, nl}:
      lex.end(ws, nl, p, toks)
    case LLine{ws, nl}:
      lex.end(ws, nl, p, toks)
    case LId{start, ws, nl, acc}:
      lex.last(ident(acc), start, ws, nl, p, toks)
    case LNat{start, ws, nl, val, big}:
      lex.last.num(KNat{val}, start, ws, nl, big, p, toks)
    case LChurch{start, ws, nl, val, big}:
      lex.last.num(KChurch{val}, start, ws, nl, big, p, toks)
    case LStrEnd{start, ws, nl, x}:
      lex.last(KStr{x, True{}}, start, ws, nl, p, toks)
    case LDollar{start, ws, nl}:
      lex.last(KBad{36}, start, ws, nl, p, toks)
    case LDash{start, ws, nl}:
      lex.last(KBad{45}, start, ws, nl, p, toks)
    case LBrace{start, ws, nl}:
      lex.last(KSym{123}, start, ws, nl, p, toks)
    case _:
      Fail{LexErr{p, "unexpected end of input"}}

def lex.fin(r: LR & L.Pos) -> Result<&2, &2, LexErr, List<&2, Tok>>:
  (lr, p) = r
  match lr:
    case LFail{e}:
      Fail{e}
    case LOk{st, toks}:
      flush(st, p, toks)

# The tokens of a text, ending in KEnd.
def lex(s: String) -> Result<&2, &2, LexErr, List<&2, Tok>>:
  +p = {L.Pos{1, 1, 0} : L.Pos}
  lex.fin(lex.go(s, p, LOk{LGap{p, False{}}, []}))
