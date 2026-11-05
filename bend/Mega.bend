import Base
import ./Lexical.bend as X
import ./Unicode.bend as U

# Master's parse errors, word for word. Parse.bend decides what parses, on
# one token of lookahead; its errors are its own. When it rejects a text
# (Repl.bend: before it looks, since a line's parse differs), this module
# runs master's grammar (src/Telomare/Parse.hs) the way megaparsec 9.7 runs
# it, and words the error as errorBundlePretty does.
#
# The grammar is data (`gram`). One machine runs it with a stack of frames;
# a parser's outcome is one of megaparsec's four continuations (consumed
# or not, ok or error), with hints, and every combinator handles them as
# Text.Megaparsec.Internal does. The grammar backtracks (try, and the
# application that falls back to an atom), so each rule's outcome at an
# offset is kept (`memo`): without it some 200-character inputs take
# millions of steps. bend/dev/perr/mega.py is the same machine in Python;
# both agree with master on the corpus there.
#
# Known difference: master's REPL expands inside its parser; Repl.bend
# expands after.

# Error items, errors, outcomes
# -----------------------------

# megaparsec's ErrorItem: Tokens, Label, EndOfInput, ordered that way.
type It is Data:
  MgTok{+s: String}
  MgLbl{+s: String}
  MgEof{}

# ErrorFancy: fail's message, or incorrect indentation (should be greater).
type Fan is Data:
  MgFail{+msg: String}
  MgIndent{+lvl: U32, +act: U32}

# ParseError: TrivialError (unexpected item, expected items) or FancyError.
type Er is Data:
  MgTriv{+off: U32, +un: Maybe<&2, It>, +ex: List<&2, It>}
  MgFancy{+off: U32, +fs: List<&2, Fan>}

# The parser's state: the rest of the text, its offset and column.
type At is Data:
  MgAt{+rest: String, +off: U32, +col: U32}

# A parser's outcome: consumed ok, empty ok (with hints), consumed error,
# empty error.
type Out is Data:
  MgCOk{+q: At, +hs: List<&2, It>}
  MgEOk{+q: At, +hs: List<&2, It>}
  MgCErr{+e: Er}
  MgEErr{+e: Er}

def it.rank(i: It) -> U32:
  match i:
    case MgTok{s}:
      0
    case MgLbl{s}:
      1
    case MgEof{}:
      2

def it.text(i: It) -> String:
  match i:
    case MgTok{s}:
      s
    case MgLbl{s}:
      s
    case MgEof{}:
      ""

def it.cmp.at(a: It, b: It, c: Cmp) -> Cmp:
  match c:
    case EQ{}:
      String.order(it.text(a), it.text(b))
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def it.cmp(+a: It, +b: It) -> Cmp:
  it.cmp.at(a, b, U32.cmp(it.rank(a), it.rank(b)))

# Sets of items, as ordered lists.
def its.ins.at(+x: It, y: It, yt: List<&2, It>, more: Unit -> List<&2, It>, c: Cmp) ->
  List<&2, It>:
  match c:
    case LT{}:
      x <> (y <> yt)
    case EQ{}:
      y <> yt
    case GT{}:
      y <> more(Unit{})

def its.ins(ys: List<&2, It>, +x: It) -> List<&2, It>:
  match ys:
    case Nil{}:
      [x]
    case Con{+y, +yt}:
      its.ins.at(x, y, yt, u => its.ins(yt, x), it.cmp(x, y))

def its.union(xs: List<&2, It>, ys: List<&2, It>) -> List<&2, It>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      its.union(xt, its.ins(ys, x))

def fan.cmp.ind(c: Cmp, a: U32, b: U32) -> Cmp:
  match c:
    case EQ{}:
      U32.cmp(a, b)
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def fan.cmp(a: Fan, b: Fan) -> Cmp:
  match a b:
    case MgFail{x} MgFail{y}:
      String.order(x, y)
    case MgFail{x} MgIndent{l, c}:
      LT{}
    case MgIndent{l, c} MgFail{y}:
      GT{}
    case MgIndent{+l1, c1} MgIndent{+l2, c2}:
      fan.cmp.ind(U32.cmp(l1, l2), c1, c2)

def fans.ins.at(+x: Fan, y: Fan, yt: List<&2, Fan>, more: Unit -> List<&2, Fan>, c: Cmp) ->
  List<&2, Fan>:
  match c:
    case LT{}:
      x <> (y <> yt)
    case EQ{}:
      y <> yt
    case GT{}:
      y <> more(Unit{})

def fans.ins(ys: List<&2, Fan>, +x: Fan) -> List<&2, Fan>:
  match ys:
    case Nil{}:
      [x]
    case Con{+y, +yt}:
      fans.ins.at(x, y, yt, u => fans.ins(yt, x), fan.cmp(x, y))

def fans.union(xs: List<&2, Fan>, ys: List<&2, Fan>) -> List<&2, Fan>:
  match xs:
    case Nil{}:
      ys
    case Con{x, xt}:
      fans.union(xt, fans.ins(ys, x))

def er.off(e: Er) -> U32:
  match e:
    case MgTriv{o, u, ps}:
      o
    case MgFancy{o, fs}:
      o

def un.max(x: It, y: It, c: Cmp) -> It:
  match c:
    case LT{}:
      y
    case EQ{}:
      y
    case GT{}:
      x

def un.merge(u1: Maybe<&2, It>, u2: Maybe<&2, It>) -> Maybe<&2, It>:
  match u1 u2:
    case None{} None{}:
      None{}
    case None{} Some{y}:
      Some{y}
    case Some{x} None{}:
      Some{x}
    case Some{+x} Some{+y}:
      Some{un.max(x, y, it.cmp(x, y))}

def er.merge.same(e1: Er, e2: Er) -> Er:
  match e1 e2:
    case MgTriv{o, u1, p1} MgTriv{o2, u2, p2}:
      MgTriv{o, un.merge(u1, u2), its.union(p1, p2)}
    case MgFancy{o, f1} MgTriv{o2, u2, p2}:
      MgFancy{o, f1}
    case MgTriv{o, u1, p1} MgFancy{o2, f2}:
      MgFancy{o2, f2}
    case MgFancy{o, f1} MgFancy{o2, f2}:
      MgFancy{o, fans.union(f1, f2)}

def er.merge.at(e1: Er, e2: Er, c: Cmp) -> Er:
  match c:
    case LT{}:
      e2
    case GT{}:
      e1
    case EQ{}:
      er.merge.same(e1, e2)

# e1 <> e2: the error further on wins; at one offset the two combine.
def er.merge(+e1: Er, +e2: Er) -> Er:
  er.merge.at(e1, e2, U32.cmp(er.off(e1), er.off(e2)))

def hints.at(ps: List<&2, It>, same: Bool) -> List<&2, It>:
  match same:
    case True{}:
      ps
    case False{}:
      []

# toHints: what an error at offset o expected, as hints there.
def to.hints(+o: U32, e: Er) -> List<&2, It>:
  match e:
    case MgTriv{+eo, u, ps}:
      hints.at(ps, U32.is_eq(o, eo))
    case MgFancy{eo, fs}:
      []

# withHints: hints join what a trivial error expected.
def with.hints(hs: List<&2, It>, e: Er) -> Er:
  match e:
    case MgTriv{o, u, ps}:
      MgTriv{o, u, its.union(ps, hs)}
    case MgFancy{o, fs}:
      MgFancy{o, fs}

# Characters
# ----------

def in.range(c: U32, lo: U32, n: U32) -> Bool:
  U32.is_lt(U32.sub(c, lo), n)

def is.digit(c: U32) -> Bool:
  in.range(c, 48, 10)

def is.cont(+c: U32) -> Bool:
  U.is_alnum(c) || U32.is_eq(c, 95) || U32.is_eq(c, 46)

type Cls is Data:
  MgSpace{}
  MgNotNl{}
  MgAny{}
  MgDigit{}
  MgCont{}

def cls.has(k: Cls, +c: U32) -> Bool:
  match k:
    case MgSpace{}:
      U.is_space(c)
    case MgNotNl{}:
      U32.is_ne(c, 10)
    case MgAny{}:
      True{}
    case MgDigit{}:
      is.digit(c)
    case MgCont{}:
      is.cont(c)

def one(c: U32) -> String:
  SCon{Chr{c}, SNil{}}

# The state
# ---------

# The column after a character: a newline starts over at 1, a tab goes to
# the next multiple of 8, plus 1, and a wide character takes two columns.
def col.next.at(nl: Bool, tab: Bool, +c: U32, +col: U32) -> U32:
  match nl tab:
    case True{} _:
      1
    case False{} True{}:
      (((col - 1) / 8 + 1) * 8 + 1 : U32)
    case False{} False{}:
      (col + U.width(c) : U32)

def col.next(+c: U32, col: U32) -> U32:
  col.next.at(U32.is_eq(c, 10), U32.is_eq(c, 9), c, col)

def at.rest(q: At) -> String:
  match q:
    case MgAt{r, o, c}:
      r

def at.off(q: At) -> U32:
  match q:
    case MgAt{r, o, c}:
      o

def at.col(q: At) -> U32:
  match q:
    case MgAt{r, o, c}:
      c

def at.step(q: At) -> At:
  match q:
    case MgAt{rest, off, col}:
      match rest:
        case SNil{}:
          MgAt{SNil{}, off, col}
        case SCon{Chr{+c}, t}:
          MgAt{t, (off + 1 : U32), col.next(c, col)}

# As many characters on as s has.
def at.adv(s: String, q: At) -> At:
  match s:
    case SNil{}:
      q
    case SCon{c, t}:
      at.adv(t, at.step(q))

def tw.if(hit: Bool, +c: U32, more: Unit -> String) -> String:
  match hit:
    case True{}:
      SCon{Chr{c}, more(Unit{})}
    case False{}:
      SNil{}

# The longest prefix of s in class k.
def tw.take(s: String, +k: Cls) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, t}:
      tw.if(cls.has(k, c), c, u => tw.take(t, k))

# Primitive parsers
# -----------------

def eerr(o: U32, u: Maybe<&2, It>, ps: List<&2, It>) -> Out:
  MgEErr{MgTriv{o, u, ps}}

# What a parser found instead: the next character, or the end of input.
def first(s: String) -> Maybe<&2, It>:
  match s:
    case SNil{}:
      Some{MgEof{}}
    case SCon{Chr{c}, t}:
      Some{MgTok{one(c)}}

# char c
def pm.char.at(hit: Bool, +c: U32, +q: At) -> Out:
  match hit:
    case True{}:
      MgCOk{at.step(q), []}
    case False{}:
      eerr(at.off(q), first(at.rest(q)), [MgTok{one(c)}])

def pm.char.peek(s: String, +c: U32, +q: At) -> Out:
  match s:
    case SNil{}:
      eerr(at.off(q), Some{MgEof{}}, [MgTok{one(c)}])
    case SCon{Chr{d}, t}:
      pm.char.at(U32.is_eq(c, d), c, q)

def pm.char(+c: U32, +q: At) -> Out:
  pm.char.peek(at.rest(q), c, q)

# string w: on a mismatch, what was there instead is as long as w.
def pm.str.at(hit: Bool, +w: String, got: String, +q: At) -> Out:
  match hit:
    case True{}:
      MgCOk{at.adv(w, q), []}
    case False{}:
      eerr(at.off(q), Some{MgTok{got}}, [MgTok{w}])

def pm.str.peek(s: String, +w: String, +q: At) -> Out:
  match s:
    case SNil{}:
      eerr(at.off(q), Some{MgEof{}}, [MgTok{w}])
    case SCon{h, t}:
      +got = String.take(SCon{h, t}, String.length(w))
      pm.str.at(String.eq(got, w), w, got, q)

def pm.str(+w: String, +q: At) -> Out:
  pm.str.peek(at.rest(q), w, q)

# satisfy (in a class), with nothing expected.
def pm.sat.at(hit: Bool, +q: At) -> Out:
  match hit:
    case True{}:
      MgCOk{at.step(q), []}
    case False{}:
      eerr(at.off(q), first(at.rest(q)), [])

def pm.sat.peek(s: String, k: Cls, +q: At) -> Out:
  match s:
    case SNil{}:
      eerr(at.off(q), Some{MgEof{}}, [])
    case SCon{Chr{d}, t}:
      pm.sat.at(cls.has(k, d), q)

def pm.sat(k: Cls, +q: At) -> Out:
  pm.sat.peek(at.rest(q), k, q)

# takeWhileP (need False) and takeWhile1P (need True), labelled l.
def pm.tw.none(need: Bool, +l: String, +q: At) -> Out:
  match need:
    case True{}:
      eerr(at.off(q), first(at.rest(q)), [MgLbl{l}])
    case False{}:
      MgEOk{q, [MgLbl{l}]}

def pm.tw.at(taken: String, +l: String, need: Bool, +q: At) -> Out:
  match taken:
    case SNil{}:
      pm.tw.none(need, l, q)
    case SCon{h, t}:
      MgCOk{at.adv(SCon{h, t}, q), [MgLbl{l}]}

def pm.tw(+l: String, k: Cls, need: Bool, +q: At) -> Out:
  pm.tw.at(tw.take(at.rest(q), k), l, need, q)

def pm.eof.peek(s: String, +q: At) -> Out:
  match s:
    case SNil{}:
      MgEOk{q, []}
    case SCon{Chr{d}, t}:
      eerr(at.off(q), Some{MgTok{one(d)}}, [MgEof{}])

# identifierRaw: a letter, then letters, digits, '_' and '.', and not a
# reserved word (inside its try).
def kw.msg(w: String) -> String:
  "keyword \"" ++ w ++ "\" cannot be an identifier"

def pm.ident.kw(kw: Bool, w: String, +q: At) -> Out:
  match kw:
    case True{}:
      MgEErr{MgFancy{at.off(q), [MgFail{kw.msg(w)}]}}
    case False{}:
      MgCOk{q, [MgLbl{"variable"}]}

def pm.ident.word(+w: String, q: At) -> Out:
  pm.ident.kw(X.is_reserved(w), w, at.adv(w, q))

def pm.ident.at(hit: Bool, +c: U32, t: String, +q: At) -> Out:
  match hit:
    case True{}:
      pm.ident.word(SCon{Chr{c}, tw.take(t, MgCont{})}, q)
    case False{}:
      eerr(at.off(q), Some{MgTok{one(c)}}, [MgLbl{"letter"}])

def pm.ident.peek(s: String, +q: At) -> Out:
  match s:
    case SNil{}:
      eerr(at.off(q), Some{MgEof{}}, [MgLbl{"letter"}])
    case SCon{Chr{+c}, t}:
      pm.ident.at(U.is_letter(c), c, t, q)

def pm.ident(+q: At) -> Out:
  pm.ident.peek(at.rest(q), q)

# naturalIntRaw: L.decimal (labelled "integer", its digits "digit"), then
# at most maxBound :: Int.
def strip0.if(zero: Bool, +c: U32, +t: String, more: Unit -> String) -> String:
  match zero:
    case True{}:
      more(Unit{})
    case False{}:
      SCon{Chr{c}, t}

def strip0(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, +t}:
      strip0.if(U32.is_eq(c, 48), c, t, u => strip0(t))

def nat.big(+d: String) -> Bool:
  +n = String.length(d)
  Nat.is_gt(n, 19n) || (Nat.is_eq(n, 19n) && Cmp.is_gt(String.order(d, "9223372036854775807")))

def pm.nat.big(big: Bool, +q: At) -> Out:
  match big:
    case True{}:
      MgCErr{MgFancy{at.off(q), [MgFail{"natural literal exceeds the supported range"}]}}
    case False{}:
      MgCOk{q, [MgLbl{"digit"}]}

def pm.nat.at(taken: String, +q: At) -> Out:
  match taken:
    case SNil{}:
      eerr(at.off(q), first(at.rest(q)), [MgLbl{"integer"}])
    case SCon{+h, +t}:
      pm.nat.big(nat.big(strip0(SCon{h, t})), at.adv(SCon{h, t}, q))

def pm.nat(+q: At) -> Out:
  pm.nat.at(tw.take(at.rest(q), MgDigit{}), q)

# notFollowedBy identifierContinue
def pm.notcont.at(hit: Bool, +c: U32, +q: At) -> Out:
  match hit:
    case True{}:
      eerr(at.off(q), Some{MgTok{one(c)}}, [])
    case False{}:
      MgEOk{q, []}

def pm.notcont.peek(s: String, +q: At) -> Out:
  match s:
    case SNil{}:
      MgEOk{q, []}
    case SCon{Chr{+c}, t}:
      pm.notcont.at(is.cont(c), c, q)

# L.charLiteral: readLitChar on the next ten characters (GHC's lexChar,
# then each "\&" after it). Gives what is left of the window.
def esc.plain(+c: U32) -> Bool:
  U32.is_eq(c, 97) || U32.is_eq(c, 98) || U32.is_eq(c, 102) || U32.is_eq(c, 110)
    || U32.is_eq(c, 114) || U32.is_eq(c, 116) || U32.is_eq(c, 118) || U32.is_eq(c, 92)
    || U32.is_eq(c, 34) || U32.is_eq(c, 39)

def dig.val.at(d: Bool, lo: Bool, up: Bool, +c: U32) -> U32:
  match d lo up:
    case True{} _ _:
      (c - 48 : U32)
    case False{} True{} _:
      (c - 87 : U32)
    case False{} False{} True{}:
      (c - 55 : U32)
    case False{} False{} False{}:
      99

def dig.val(+c: U32) -> U32:
  dig.val.at(is.digit(c), in.range(c, 97, 6), in.range(c, 65, 6), c)

def num.take(s: String, +b: U32) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, t}:
      tw.if(U32.is_lt(dig.val(c), b), c, u => num.take(t, b))

def num.val(s: String, +b: U32, acc: U32) -> U32:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{c}, t}:
      num.val(t, b, (acc * b + dig.val(c) : U32))

def esc.num.ok(ok: Bool, rest: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{rest}
    case False{}:
      None{}

def esc.num.fin(digits: String, rest: String, +b: U32) -> Maybe<&2, String>:
  match digits:
    case SNil{}:
      None{}
    case SCon{h, t}:
      esc.num.ok(U32.is_lt(num.val(SCon{h, t}, b, 0), 1114112), rest)

def esc.num(+s: String, +b: U32) -> Maybe<&2, String>:
  +ds = num.take(s, b)
  esc.num.fin(ds, String.drop(s, String.length(ds)), b)

def esc.ctl.at(ok: Bool, rest: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{rest}
    case False{}:
      None{}

def esc.ctl(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{Chr{d}, t}:
      esc.ctl.at(in.range(d, 64, 32), t)

def asc.names() -> List<&2, String>:
  ["SOH", "NUL", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS", "HT", "LF", "VT",
   "FF", "CR", "SO", "SI", "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
   "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US", "SP", "DEL"]

def asc.if(hit: Bool, +s: String, +w: String, more: Unit -> Maybe<&2, String>) ->
  Maybe<&2, String>:
  match hit:
    case True{}:
      Some{String.drop(s, String.length(w))}
    case False{}:
      more(Unit{})

def asc.go(ws: List<&2, String>, +s: String) -> Maybe<&2, String>:
  match ws:
    case Nil{}:
      None{}
    case Con{+w, t}:
      asc.if(String.starts_with(s, w), s, w, u => asc.go(t, s))

def esc.kind(e: Bool, o: Bool, x: Bool, d: Bool, ctl: Bool, +c: U32, +t: String) ->
  Maybe<&2, String>:
  match e o x d ctl:
    case True{} _ _ _ _:
      Some{t}
    case False{} True{} _ _ _:
      esc.num(t, 8)
    case False{} False{} True{} _ _:
      esc.num(t, 16)
    case False{} False{} False{} True{} _:
      esc.num(SCon{Chr{c}, t}, 10)
    case False{} False{} False{} False{} True{}:
      esc.ctl(t)
    case False{} False{} False{} False{} False{}:
      asc.go(asc.names(), SCon{Chr{c}, t})

# After a backslash.
def esc.at(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{Chr{+c}, +t}:
      esc.kind(esc.plain(c), U32.is_eq(c, 111) || U32.is_eq(c, 79),
               U32.is_eq(c, 120) || U32.is_eq(c, 88), is.digit(c),
               U32.is_eq(c, 94), c, t)

def lit.emp.if(hit: Bool, +s: String, more: Unit -> String) -> String:
  match hit:
    case True{}:
      more(Unit{})
    case False{}:
      s

# Each "\&" that follows.
def lit.empties(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, +t}:
      match t:
        case SNil{}:
          SCon{Chr{c}, SNil{}}
        case SCon{Chr{+d}, +u}:
          lit.emp.if(U32.is_eq(c, 92) && U32.is_eq(d, 38), SCon{Chr{c}, SCon{Chr{d}, u}},
                     v => lit.empties(u))

def lit.after(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{rest}:
      Some{lit.empties(rest)}

def lit.read.at(bs: Bool, t: String) -> Maybe<&2, String>:
  match bs:
    case True{}:
      lit.after(esc.at(t))
    case False{}:
      Some{lit.empties(t)}

def lit.read(r: String) -> Maybe<&2, String>:
  match r:
    case SNil{}:
      None{}
    case SCon{Chr{c}, t}:
      lit.read.at(U32.is_eq(c, 92), t)

def pm.lit.got(m: Maybe<&2, String>, +w: String, +q: At) -> Out:
  match m:
    case None{}:
      eerr(at.off(q), first(w), [MgLbl{"literal character"}])
    case Some{left}:
      MgCOk{at.adv(String.take(w, Nat.sub(String.length(w), String.length(left))), q), []}

def pm.lit.peek(s: String, +q: At) -> Out:
  match s:
    case SNil{}:
      eerr(at.off(q), Some{MgEof{}}, [MgLbl{"literal character"}])
    case SCon{h, t}:
      +w = String.take(SCon{h, t}, 10n)
      pm.lit.got(lit.read(w), w, q)

def pm.lit(+q: At) -> Out:
  pm.lit.peek(at.rest(q), q)

# lineFold's guard: after the space, a column right of the fold's.
def pm.guard.at(ok: Bool, +lf: U32, +q: At) -> Out:
  match ok:
    case True{}:
      MgEOk{q, []}
    case False{}:
      MgEErr{MgFancy{at.off(q), [MgIndent{lf, at.col(q)}]}}

def pm.guard(+lf: U32, +q: At) -> Out:
  pm.guard.at(U32.is_gt(at.col(q), lf), lf, q)

# The grammar
# -----------

# The rules (master's parsers, one each).
type Rf is Data:
  RfSc{}
  RfScn{}
  RfLineC{}
  RfBlockC{}
  RfBcTill{}
  RfLocId{}
  RfLitTill{}
  RfString{}
  RfNumber{}
  RfPair{}
  RfUrec{}
  RfList{}
  RfIte{}
  RfListDef{}
  RfCase{}
  RfSCase{}
  RfPattern{}
  RfLPattern{}
  RfPPair{}
  RfPInt{}
  RfPString{}
  RfPVar{}
  RfPIgnore{}
  RfPAnnot{}
  RfSingle{}
  RfApplied{}
  RfApplication{}
  RfLambda{}
  RfLet{}
  RfLetTill{}
  RfLong{}
  RfChurch{}
  RfSDef{}
  RfImport{}
  RfDefinition{}

def rf.id(x: Rf) -> U32:
  match x:
    case RfSc{}:
      0
    case RfScn{}:
      1
    case RfLineC{}:
      2
    case RfBlockC{}:
      3
    case RfBcTill{}:
      4
    case RfLocId{}:
      5
    case RfLitTill{}:
      6
    case RfString{}:
      7
    case RfNumber{}:
      8
    case RfPair{}:
      9
    case RfUrec{}:
      10
    case RfList{}:
      11
    case RfIte{}:
      12
    case RfListDef{}:
      14
    case RfCase{}:
      15
    case RfSCase{}:
      16
    case RfPattern{}:
      17
    case RfLPattern{}:
      18
    case RfPPair{}:
      19
    case RfPInt{}:
      20
    case RfPString{}:
      21
    case RfPVar{}:
      22
    case RfPIgnore{}:
      23
    case RfPAnnot{}:
      24
    case RfSingle{}:
      25
    case RfApplied{}:
      26
    case RfApplication{}:
      27
    case RfLambda{}:
      28
    case RfLet{}:
      29
    case RfLetTill{}:
      30
    case RfLong{}:
      31
    case RfChurch{}:
      32
    case RfSDef{}:
      33
    case RfImport{}:
      34
    case RfDefinition{}:
      35

# A parser as data: megaparsec's combinators, master's primitives, and a
# rule by name. NdCol and NdFold note the column (a let's indentLevel,
# lineFold's), NdSame and NdGuard test against it.
type Nd is Data:
  NdSeq{+a: Nd, +b: Nd}
  NdAlt{+a: Nd, +b: Nd}
  NdTry{+a: Nd}
  NdLbl{+l: String, +a: Nd}
  NdHid{+a: Nd}
  NdMany{+a: Nd}
  NdOpt{+a: Nd, +y: Nd, +n: Nd}
  NdRef{+r: Rf}
  NdCol{+a: Nd}
  NdFold{+a: Nd}
  NdSame{+a: Nd}
  NdChar{+c: U32}
  NdStr{+w: String}
  NdSat{+k: Cls}
  NdTw{+l: String, +k: Cls}
  NdTw1{+l: String, +k: Cls}
  NdEof{}
  NdZero{}
  NdPure{}
  NdIdent{}
  NdNat{}
  NdNotCont{}
  NdLit{}
  NdGuard{}

def rf(x: Rf) -> Nd:
  NdRef{x}

def sc() -> Nd:
  NdRef{RfSc{}}

def scn() -> Nd:
  NdRef{RfScn{}}

def expr() -> Nd:
  NdRef{RfLong{}}

# a >> b >> ...
def sq(xs: List<&2, Nd>) -> Nd:
  match xs:
    case Nil{}:
      NdPure{}
    case Con{x, +t}:
      match t:
        case Nil{}:
          x
        case Con{y, u}:
          NdSeq{x, sq(t)}

# choice: a <|> (b <|> ... <|> empty)
def ch(xs: List<&2, Nd>) -> Nd:
  match xs:
    case Nil{}:
      NdZero{}
    case Con{x, t}:
      NdAlt{x, ch(t)}

def sym(w: String) -> Nd:
  NdSeq{NdStr{w}, sc()}

def kw(w: String) -> Nd:
  NdSeq{NdTry{NdSeq{NdStr{w}, NdNotCont{}}}, sc()}

def some(+a: Nd) -> Nd:
  NdSeq{a, NdMany{a}}

def sep.by1(+p: Nd, s: Nd) -> Nd:
  NdSeq{p, NdMany{NdSeq{s, p}}}

def sep.by(+p: Nd, s: Nd) -> Nd:
  NdOpt{p, NdMany{NdSeq{s, p}}, NdPure{}}

def blank() -> Nd:
  NdAlt{NdChar{32}, NdChar{9}}

def gram(x: Rf) -> Nd:
  match x:
    case RfSc{}:
      NdMany{ch([NdHid{some(blank())}, NdHid{rf(RfLineC{})}, NdHid{rf(RfBlockC{})}])}
    case RfScn{}:
      NdMany{ch([NdHid{NdTw1{"white space", MgSpace{}}}, NdHid{rf(RfLineC{})},
                 NdHid{rf(RfBlockC{})}])}
    case RfLineC{}:
      NdSeq{NdStr{"--"}, NdTw{"character", MgNotNl{}}}
    case RfBlockC{}:
      NdSeq{NdStr{"{-"}, rf(RfBcTill{})}
    case RfBcTill{}:
      NdOpt{NdStr{"-}"}, NdPure{}, NdSeq{NdAlt{rf(RfBlockC{}), NdSat{MgAny{}}}, rf(RfBcTill{})}}
    case RfLocId{}:
      sq([NdIdent{}, sc(), sc()])
    case RfLitTill{}:
      NdOpt{NdChar{34}, NdPure{}, NdSeq{NdLit{}, rf(RfLitTill{})}}
    case RfString{}:
      sq([NdChar{34}, rf(RfLitTill{}), sc()])
    case RfNumber{}:
      NdSeq{NdNat{}, sc()}
    case RfPair{}:
      sq([sym("("), scn(), expr(), scn(), sym(","), scn(), expr(), scn(), sym(")")])
    case RfUrec{}:
      sq([sym("{"), scn(), expr(), scn(), sym(","), scn(), expr(), scn(), sym(","), scn(),
          expr(), scn(), sym("}")])
    case RfList{}:
      sq([sym("["), sep.by(sq([scn(), expr(), scn()]), sym(",")), sym("]")])
    case RfIte{}:
      sq([kw("if"), scn(), expr(), scn(), kw("then"), scn(), expr(), scn(), kw("else"), scn(),
          expr(), scn()])
    case RfListDef{}:
      sq([NdLbl{"list assignment names",
                sq([sym("["), sep.by1(sq([scn(), rf(RfLocId{}), scn()]), sym(",")), sym("]"),
                    scn()])},
          NdLbl{"list assignment =", NdSeq{scn(), sym("=")}},
          NdLbl{"list assignment body", sq([scn(), expr(), scn()])}])
    case RfCase{}:
      sq([kw("case"), scn(), expr(), scn(), kw("of"), scn(),
          some(NdSeq{NdTry{rf(RfSCase{})}, scn()})])
    case RfSCase{}:
      sq([rf(RfPattern{}), scn(), kw("->"), scn(), expr(), scn()])
    case RfPattern{}:
      ch([NdTry{rf(RfPIgnore{})}, NdTry{rf(RfPVar{})}, NdTry{rf(RfPAnnot{})},
          NdTry{rf(RfPString{})}, NdTry{rf(RfPInt{})}, NdTry{rf(RfPPair{})}])
    case RfLPattern{}:
      ch([NdTry{NdSeq{rf(RfLocId{}), scn()}},
          NdTry{ch([NdTry{rf(RfPIgnore{})}, NdTry{rf(RfPAnnot{})}, NdTry{rf(RfPString{})},
                    NdTry{rf(RfPInt{})}, NdTry{rf(RfPPair{})}])}])
    case RfPPair{}:
      sq([sym("("), scn(), rf(RfPattern{}), scn(), sym(","), scn(), rf(RfPattern{}), scn(),
          sym(")")])
    case RfPInt{}:
      NdSeq{NdNat{}, sc()}
    case RfPString{}:
      NdSeq{NdChar{34}, rf(RfLitTill{})}
    case RfPVar{}:
      NdSeq{rf(RfLocId{}), scn()}
    case RfPIgnore{}:
      sym("_")
    case RfPAnnot{}:
      NdLbl{"annotated pattern",
            sq([sym("("), NdLbl{"pattern before ':'", sq([scn(), rf(RfPattern{}), scn()])},
                sym(":"), scn(), NdLbl{"type expression after ':'", NdSeq{expr(), scn()}},
                sym(")")])}
    case RfSingle{}:
      ch([NdTry{rf(RfString{})}, NdTry{rf(RfNumber{})},
          NdTry{rf(RfPair{})}, NdTry{rf(RfUrec{})}, NdTry{rf(RfList{})},
          NdTry{rf(RfChurch{})}, NdTry{NdSeq{NdIdent{}, sc()}},
          NdTry{sq([sym("("), scn(), expr(), scn(), sym(")")])}])
    case RfApplied{}:
      NdSeq{scn(), NdFold{sep.by1(rf(RfSingle{}), NdTry{NdSeq{scn(), NdGuard{}}})}}
    case RfApplication{}:
      NdAlt{NdTry{rf(RfApplied{})}, rf(RfSingle{})}
    case RfLambda{}:
      sq([sym("\\"), scn(), some(rf(RfLPattern{})), scn(), sym("->"), scn(), expr(), scn()])
    case RfLet{}:
      sq([kw("let"), scn(), NdCol{sq([rf(RfLetTill{}), scn(), expr(), scn()])}])
    case RfLetTill{}:
      NdOpt{kw("in"), NdPure{}, NdSeq{NdSame{rf(RfDefinition{})}, rf(RfLetTill{})}}
    case RfLong{}:
      ch([rf(RfLet{}), rf(RfIte{}), rf(RfLambda{}), rf(RfCase{}), rf(RfApplication{})])
    case RfChurch{}:
      sq([NdChar{36}, NdNat{}, sc()])
    case RfSDef{}:
      sq([rf(RfLocId{}), scn(), NdAlt{NdTry{NdSeq{sym(":"), expr()}}, NdPure{}},
          NdLbl{"assignment =", NdSeq{scn(), sym("=")}}, scn(), expr(), scn()])
    case RfImport{}:
      sq([kw("import"), scn(),
          NdOpt{NdTry{NdSeq{kw("qualified"), scn()}},
                sq([rf(RfLocId{}), scn(), kw("as"), scn(), rf(RfLocId{})]),
                NdSeq{rf(RfLocId{}), scn()}}])
    case RfDefinition{}:
      NdAlt{rf(RfSDef{}), rf(RfListDef{})}

# What is parsed: master's runParseModule, runParseDefinitions,
# runParseExpression, its REPL's step (a definition, else an expression,
# each to the end), and parseOneExprOrDefinitions (eval2IExpr's, for the
# LSP's evaluation: definitions, else an expression).
type Top is Data:
  MgModule{}
  MgDefs{}
  MgExpr{}
  MgRepl{}
  MgOneOf{}

def defs.node() -> Nd:
  sq([scn(), NdMany{rf(RfDefinition{})}, scn(), NdEof{}])

def expr.node() -> Nd:
  sq([scn(), expr(), scn(), NdEof{}])

def top.node(t: Top) -> Nd:
  match t:
    case MgModule{}:
      sq([scn(), NdMany{sq([scn(), NdAlt{NdTry{rf(RfImport{})}, rf(RfDefinition{})}, scn()])},
          NdEof{}])
    case MgDefs{}:
      defs.node()
    case MgExpr{}:
      expr.node()
    case MgRepl{}:
      NdAlt{NdTry{NdSeq{rf(RfSDef{}), NdEof{}}}, NdSeq{expr(), NdEof{}}}
    case MgOneOf{}:
      NdAlt{NdTry{defs.node()}, expr.node()}

# The machine
# -----------

# What to do with an outcome: megaparsec's continuations, as frames.
type Fm is Data:
  FmSeq{+b: Nd}
  FmSeqC{+hs: List<&2, It>}
  FmSeqE{+hs: List<&2, It>}
  FmAlt{+n: Nd, +q: At}
  FmAltB{+e: Er}
  FmTry{}
  FmLbl{+l: String}
  FmHid{}
  FmOpt{+y: Nd, +n: Nd, +q: At}
  FmLv{+lc: U32, +lf: U32}
  FmMemo{+id: U32, +off: U32, +lc: U32, +lf: U32}

type Md is Data:
  MgEval{+n: Nd, +q: At}
  MgRet{+o: Out}

# A rule's outcome at an offset, under a let's and a fold's column.
type Me is Data:
  MgMemo{+id: U32, +off: U32, +lc: U32, +lf: U32, +o: Out}

type Mc is Type:
  MgMc{memo: Array<List<&2, Me>>, lc: U32, lf: U32, md: Md, stack: List<&2, Fm>}

# a >>= b: b's hints join a's when b consumes nothing.
def seqc(hs: List<&2, It>, o: Out) -> Out:
  match o:
    case MgCOk{q, h2}:
      MgCOk{q, h2}
    case MgEOk{q, h2}:
      MgCOk{q, its.union(hs, h2)}
    case MgCErr{e}:
      MgCErr{e}
    case MgEErr{e}:
      MgCErr{with.hints(hs, e)}

def seqe(hs: List<&2, It>, o: Out) -> Out:
  match o:
    case MgCOk{q, h2}:
      MgCOk{q, h2}
    case MgEOk{q, h2}:
      MgEOk{q, its.union(hs, h2)}
    case MgCErr{e}:
      MgCErr{e}
    case MgEErr{e}:
      MgEErr{with.hints(hs, e)}

# m <|> n, n's outcome after m failed with err.
def altb(err: Er, o: Out) -> Out:
  match o:
    case MgCOk{q, hs}:
      MgCOk{q, hs}
    case MgEOk{+q, hs}:
      MgEOk{q, its.union(to.hints(at.off(q), err), hs)}
    case MgCErr{e}:
      MgCErr{er.merge(e, err)}
    case MgEErr{e}:
      MgEErr{er.merge(e, err)}

def try.out(o: Out) -> Out:
  match o:
    case MgCErr{e}:
      MgEErr{e}
    case MgCOk{q, hs}:
      MgCOk{q, hs}
    case MgEOk{q, hs}:
      MgEOk{q, hs}
    case MgEErr{e}:
      MgEErr{e}

def lbl.hints(hs: List<&2, It>, +l: String) -> List<&2, It>:
  match hs:
    case Nil{}:
      []
    case Con{h, t}:
      [MgLbl{l}]

def lbl.err(e: Er, l: String) -> Er:
  match e:
    case MgTriv{o, u, ps}:
      MgTriv{o, u, [MgLbl{l}]}
    case MgFancy{o, fs}:
      MgFancy{o, fs}

# p <?> l
def lbl.out(l: String, o: Out) -> Out:
  match o:
    case MgCOk{q, hs}:
      MgCOk{q, hs}
    case MgEOk{q, hs}:
      MgEOk{q, lbl.hints(hs, l)}
    case MgCErr{e}:
      MgCErr{e}
    case MgEErr{e}:
      MgEErr{lbl.err(e, l)}

def hid.err(e: Er) -> Er:
  match e:
    case MgTriv{o, u, ps}:
      MgTriv{o, u, []}
    case MgFancy{o, fs}:
      MgFancy{o, fs}

# hidden p
def hid.out(o: Out) -> Out:
  match o:
    case MgCOk{q, hs}:
      MgCOk{q, []}
    case MgEOk{q, hs}:
      MgEOk{q, []}
    case MgCErr{e}:
      MgCErr{e}
    case MgEErr{e}:
      MgEErr{hid.err(e)}

def memo.if(hit: Bool, o: Out, more: Unit -> Maybe<&2, Out>) -> Maybe<&2, Out>:
  match hit:
    case True{}:
      Some{o}
    case False{}:
      more(Unit{})

def memo.find(xs: List<&2, Me>, +id: U32, +off: U32, +lc: U32, +lf: U32) -> Maybe<&2, Out>:
  match xs:
    case Nil{}:
      None{}
    case Con{MgMemo{i, o, c, f, out}, t}:
      memo.if(U32.is_eq(i, id) && U32.is_eq(o, off) && U32.is_eq(c, lc) && U32.is_eq(f, lf),
              out, u => memo.find(t, id, off, lc, lf))

def ret.prim(o: Out, memo: Array<List<&2, Me>>, lc: U32, lf: U32, stack: List<&2, Fm>) -> Mc:
  MgMc{memo, lc, lf, MgRet{o}, stack}

def ref.hit(m: Maybe<&2, Out>, x: Rf, +id: U32, memo: Array<List<&2, Me>>, +q: At,
            +lc: U32, +lf: U32, stack: List<&2, Fm>) -> Mc:
  match m:
    case Some{o}:
      MgMc{memo, lc, lf, MgRet{o}, stack}
    case None{}:
      MgMc{memo, lc, lf, MgEval{gram(x), q}, FmMemo{id, at.off(q), lc, lf} <> stack}

def ref.got(r: Array<List<&2, Me>> & List<&2, Me>, x: Rf, +id: U32, +q: At, +lc: U32,
            +lf: U32, stack: List<&2, Fm>) -> Mc:
  (memo, xs) = r
  ref.hit(memo.find(xs, id, at.off(q), lc, lf), x, id, memo, q, lc, lf, stack)

def ref.go(+x: Rf, memo: Array<List<&2, Me>>, +q: At, +lc: U32, +lf: U32,
           stack: List<&2, Fm>) -> Mc:
  ref.got(Array.get(List<&2, Me>, memo, at.off(q)), x, rf.id(x), q, lc, lf, stack)

def same.at(ok: Bool, a: Nd, +q: At, memo: Array<List<&2, Me>>, lc: U32, lf: U32,
            stack: List<&2, Fm>) -> Mc:
  match ok:
    case True{}:
      MgMc{memo, lc, lf, MgEval{a, q}, stack}
    case False{}:
      MgMc{memo, lc, lf, MgRet{MgEErr{MgFancy{at.off(q), [MgFail{"Expected same indentation."}]}}},
           stack}

def eval(n: Nd, +q: At, memo: Array<List<&2, Me>>, +lc: U32, +lf: U32,
         stack: List<&2, Fm>) -> Mc:
  match n:
    case NdSeq{a, b}:
      MgMc{memo, lc, lf, MgEval{a, q}, FmSeq{b} <> stack}
    case NdAlt{a, b}:
      MgMc{memo, lc, lf, MgEval{a, q}, FmAlt{b, q} <> stack}
    case NdTry{a}:
      MgMc{memo, lc, lf, MgEval{a, q}, FmTry{} <> stack}
    case NdLbl{l, a}:
      MgMc{memo, lc, lf, MgEval{a, q}, FmLbl{l} <> stack}
    case NdHid{a}:
      MgMc{memo, lc, lf, MgEval{a, q}, FmHid{} <> stack}
    case NdMany{+a}:
      MgMc{memo, lc, lf, MgEval{a, q}, FmSeq{NdMany{a}} <> (FmAlt{NdPure{}, q} <> stack)}
    case NdOpt{a, y, z}:
      MgMc{memo, lc, lf, MgEval{a, q}, FmOpt{y, z, q} <> stack}
    case NdRef{x}:
      ref.go(x, memo, q, lc, lf, stack)
    case NdCol{a}:
      MgMc{memo, at.col(q), lf, MgEval{a, q}, FmLv{lc, lf} <> stack}
    case NdFold{a}:
      MgMc{memo, lc, at.col(q), MgEval{a, q}, FmLv{lc, lf} <> stack}
    case NdSame{a}:
      same.at(U32.is_eq(at.col(q), lc), a, q, memo, lc, lf, stack)
    case NdChar{c}:
      ret.prim(pm.char(c, q), memo, lc, lf, stack)
    case NdStr{w}:
      ret.prim(pm.str(w, q), memo, lc, lf, stack)
    case NdSat{k}:
      ret.prim(pm.sat(k, q), memo, lc, lf, stack)
    case NdTw{l, k}:
      ret.prim(pm.tw(l, k, False{}, q), memo, lc, lf, stack)
    case NdTw1{l, k}:
      ret.prim(pm.tw(l, k, True{}, q), memo, lc, lf, stack)
    case NdEof{}:
      ret.prim(pm.eof.peek(at.rest(q), q), memo, lc, lf, stack)
    case NdZero{}:
      ret.prim(eerr(at.off(q), None{}, []), memo, lc, lf, stack)
    case NdPure{}:
      ret.prim(MgEOk{q, []}, memo, lc, lf, stack)
    case NdIdent{}:
      ret.prim(pm.ident(q), memo, lc, lf, stack)
    case NdNat{}:
      ret.prim(pm.nat(q), memo, lc, lf, stack)
    case NdNotCont{}:
      ret.prim(pm.notcont.peek(at.rest(q), q), memo, lc, lf, stack)
    case NdLit{}:
      ret.prim(pm.lit(q), memo, lc, lf, stack)
    case NdGuard{}:
      ret.prim(pm.guard(lf, q), memo, lc, lf, stack)

def ret.seq(o: Out, b: Nd, memo: Array<List<&2, Me>>, lc: U32, lf: U32,
            stack: List<&2, Fm>) -> Mc:
  match o:
    case MgCOk{q, hs}:
      MgMc{memo, lc, lf, MgEval{b, q}, FmSeqC{hs} <> stack}
    case MgEOk{q, hs}:
      MgMc{memo, lc, lf, MgEval{b, q}, FmSeqE{hs} <> stack}
    case MgCErr{e}:
      MgMc{memo, lc, lf, MgRet{MgCErr{e}}, stack}
    case MgEErr{e}:
      MgMc{memo, lc, lf, MgRet{MgEErr{e}}, stack}

def ret.alt(o: Out, n: Nd, q0: At, memo: Array<List<&2, Me>>, lc: U32, lf: U32,
            stack: List<&2, Fm>) -> Mc:
  match o:
    case MgEErr{e}:
      MgMc{memo, lc, lf, MgEval{n, q0}, FmAltB{e} <> stack}
    case MgCOk{q, hs}:
      MgMc{memo, lc, lf, MgRet{MgCOk{q, hs}}, stack}
    case MgEOk{q, hs}:
      MgMc{memo, lc, lf, MgRet{MgEOk{q, hs}}, stack}
    case MgCErr{e}:
      MgMc{memo, lc, lf, MgRet{MgCErr{e}}, stack}

# optional a >>= (y on Just, n on Nothing)
def ret.opt(o: Out, y: Nd, n: Nd, +q0: At, memo: Array<List<&2, Me>>, lc: U32, lf: U32,
            stack: List<&2, Fm>) -> Mc:
  match o:
    case MgCOk{q, hs}:
      MgMc{memo, lc, lf, MgEval{y, q}, FmSeqC{hs} <> stack}
    case MgEOk{q, hs}:
      MgMc{memo, lc, lf, MgEval{y, q}, FmSeqE{hs} <> stack}
    case MgEErr{e}:
      MgMc{memo, lc, lf, MgEval{n, q0}, FmSeqE{to.hints(at.off(q0), e)} <> stack}
    case MgCErr{e}:
      MgMc{memo, lc, lf, MgRet{MgCErr{e}}, stack}

def ret.memo(r: Array<List<&2, Me>> & List<&2, Me>, e: Me, o: Out, off: U32, lc: U32,
             lf: U32, stack: List<&2, Fm>) -> Mc:
  (memo, xs) = r
  MgMc{Array.set(List<&2, Me>, memo, off, e <> xs), lc, lf, MgRet{o}, stack}

def ret(fr: Fm, +o: Out, memo: Array<List<&2, Me>>, +lc: U32, +lf: U32,
        stack: List<&2, Fm>) -> Mc:
  match fr:
    case FmSeq{b}:
      ret.seq(o, b, memo, lc, lf, stack)
    case FmSeqC{hs}:
      MgMc{memo, lc, lf, MgRet{seqc(hs, o)}, stack}
    case FmSeqE{hs}:
      MgMc{memo, lc, lf, MgRet{seqe(hs, o)}, stack}
    case FmAlt{n, q0}:
      ret.alt(o, n, q0, memo, lc, lf, stack)
    case FmAltB{e}:
      MgMc{memo, lc, lf, MgRet{altb(e, o)}, stack}
    case FmTry{}:
      MgMc{memo, lc, lf, MgRet{try.out(o)}, stack}
    case FmLbl{l}:
      MgMc{memo, lc, lf, MgRet{lbl.out(l, o)}, stack}
    case FmHid{}:
      MgMc{memo, lc, lf, MgRet{hid.out(o)}, stack}
    case FmOpt{y, n, q0}:
      ret.opt(o, y, n, q0, memo, lc, lf, stack)
    case FmLv{c, f}:
      MgMc{memo, c, f, MgRet{o}, stack}
    case FmMemo{+id, +off, +c, +f}:
      ret.memo(Array.swap(List<&2, Me>, memo, off, []), MgMemo{id, off, c, f, o}, o, off, lc,
               lf, stack)

def run(fuel: Nat, m: Mc) -> Out:
  match fuel:
    case 0n:
      MgEErr{MgFancy{0, [MgFail{"the error checker ran out of fuel"}]}}
    case 1n+f:
      match m:
        case MgMc{memo, lc, lf, md, stack}:
          match md:
            case MgEval{n, q}:
              run(f, eval(n, q, memo, lc, lf, stack))
            case MgRet{o}:
              match stack:
                case Nil{}:
                  o
                case Con{fr, rest}:
                  run(f, ret(fr, o, memo, lc, lf, rest))

# errorBundlePretty
# -----------------

# Line, column, and the text from the line's start, at offset o.
type PosR is Data:
  MgPos{+line: U32, +col: U32, +ls: String}

def pos.ls(nl: Bool, t: String, ls: String) -> String:
  match nl:
    case True{}:
      t
    case False{}:
      ls

def pos.line(nl: Bool, +line: U32) -> U32:
  match nl:
    case True{}:
      (line + 1 : U32)
    case False{}:
      line

def pos.if(stop: Bool, more: Unit -> PosR, +line: U32, +col: U32, +ls: String) -> PosR:
  match stop:
    case True{}:
      MgPos{line, col, ls}
    case False{}:
      more(Unit{})

def pos.go(s: String, +ls: String, +i: U32, +o: U32, +line: U32, +col: U32) -> PosR:
  match s:
    case SNil{}:
      MgPos{line, col, ls}
    case SCon{Chr{+c}, +t}:
      pos.if(U32.is_eq(i, o),
             u => pos.go(t, pos.ls(U32.is_eq(c, 10), t, ls), (i + 1 : U32), o,
                         pos.line(U32.is_eq(c, 10), line), col.next(c, col)),
             line, col, ls)

def expand.w(tab: Bool, +i: U32) -> U32:
  match tab:
    case True{}:
      (8 - U32.mod(i, 8) : U32)
    case False{}:
      1

def expand.piece(tab: Bool, c: U32, n: U32) -> String:
  match tab:
    case True{}:
      String.repeat(" ", U32.to_nat(n))
    case False{}:
      one(c)

# expandTab: tabs to the next multiple of 8.
def expand(s: String, +i: U32) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{Chr{+c}, t}:
      +tab = U32.is_eq(c, 9)
      +n = expand.w(tab, i)
      expand.piece(tab, c, n) ++ expand(t, (i + n : U32))

def or.empty(s: String) -> String:
  match s:
    case SNil{}:
      "<empty line>"
    case SCon{h, t}:
      SCon{h, t}

# megaparsec's stringLength: wide characters count twice.
def str.width(s: String, +n: U32) -> U32:
  match s:
    case SNil{}:
      n
    case SCon{Chr{+c}, t}:
      str.width(t, (n + U.width(c) : U32))

def it.len(i: It) -> U32:
  match i:
    case MgTok{s}:
      str.width(s, 0)
    case MgLbl{s}:
      1
    case MgEof{}:
      1

def un.len(u: Maybe<&2, It>) -> U32:
  match u:
    case None{}:
      1
    case Some{i}:
      it.len(i)

def er.elen(e: Er) -> U32:
  match e:
    case MgTriv{o, u, ps}:
      un.len(u)
    case MgFancy{o, fs}:
      1

def ptr.len(over: Bool, +sl: U32, +shift: U32, elen: U32) -> U32:
  match over:
    case True{}:
      (sl - shift + 1 : U32)
    case False{}:
      elen

def char.names() -> List<&2, String>:
  ["null", "start of heading", "start of text", "end of text", "end of transmission",
   "enquiry", "acknowledge", "bell", "backspace", "tab", "newline", "vertical tab",
   "form feed", "carriage return", "shift out", "shift in", "data link escape",
   "device control one", "device control two", "device control three",
   "device control four", "negative acknowledge", "synchronous idle",
   "end of transmission block", "cancel", "end of medium", "substitute", "escape",
   "file separator", "group separator", "record separator", "unit separator"]

def char.name.at(lo: Bool, del: Bool, nb: Bool, c: U32) -> Maybe<&2, String>:
  match lo del nb:
    case True{} _ _:
      List.get(&2, String, char.names(), U32.to_nat(c))
    case False{} True{} _:
      Some{"delete"}
    case False{} False{} True{}:
      Some{"non-breaking space"}
    case False{} False{} False{}:
      None{}

# megaparsec's charPretty': the names of control characters.
def char.name(+c: U32) -> Maybe<&2, String>:
  char.name.at(U32.is_lt(c, 32), U32.is_eq(c, 127), U32.is_eq(c, 160), c)

def show.one.at(sp: Bool, m: Maybe<&2, String>, c: U32) -> String:
  match sp m:
    case True{} _:
      "space"
    case False{} Some{n}:
      n
    case False{} None{}:
      "'" ++ one(c) ++ "'"

def quote.piece(m: Maybe<&2, String>, c: U32) -> String:
  match m:
    case Some{n}:
      "<" ++ n ++ ">"
    case None{}:
      one(c)

def quote(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{+c}, t}:
      quote.piece(char.name(c), c) ++ quote(t)

def show.tok.crlf(crlf: Bool, s: String) -> String:
  match crlf:
    case True{}:
      "crlf newline"
    case False{}:
      "\"" ++ quote(s) ++ "\""

def show.tok.rest(t: String, +c: U32) -> String:
  match t:
    case SNil{}:
      show.one.at(U32.is_eq(c, 32), char.name(c), c)
    case SCon{+h, +u}:
      show.tok.crlf(U32.is_eq(c, 13) && String.eq(SCon{h, u}, "\n"), SCon{Chr{c}, SCon{h, u}})

# showErrorItem
def show.item(i: It) -> String:
  match i:
    case MgTok{s}:
      match s:
        case SNil{}:
          "\"\""
        case SCon{Chr{+c}, t}:
          show.tok.rest(t, c)
    case MgLbl{s}:
      s
    case MgEof{}:
      "end of input"

def strs.ins.at(+x: String, y: String, yt: List<&2, String>, more: Unit -> List<&2, String>,
                c: Cmp) -> List<&2, String>:
  match c:
    case LT{}:
      x <> (y <> yt)
    case EQ{}:
      y <> yt
    case GT{}:
      y <> more(Unit{})

def strs.ins(ys: List<&2, String>, +x: String) -> List<&2, String>:
  match ys:
    case Nil{}:
      [x]
    case Con{+y, +yt}:
      strs.ins.at(x, y, yt, u => strs.ins(yt, x), String.order(x, y))

# The items as shown, sorted and without repeats (a Set String).
def shown.items(xs: List<&2, It>, acc: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      shown.items(t, strs.ins(acc, show.item(x)))

# "a, b, or c" from two or more
def or.tail(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, +t}:
      match t:
        case Nil{}:
          "or " ++ x
        case Con{y, u}:
          x ++ ", " ++ or.tail(t)

# orList
def or.list(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +t}:
      match t:
        case Nil{}:
          x
        case Con{+y, u}:
          match u:
            case Nil{}:
              x ++ " or " ++ y
            case Con{z, v}:
              or.tail(Con{x, t})

def items.at(prefix: String, ss: List<&2, String>) -> String:
  match ss:
    case Nil{}:
      ""
    case Con{h, t}:
      prefix ++ or.list(Con{h, t}) ++ "\n"

# messageItemsPretty
def items.pretty(prefix: String, xs: List<&2, It>) -> String:
  items.at(prefix, shown.items(xs, []))

def un.items(u: Maybe<&2, It>) -> List<&2, It>:
  match u:
    case None{}:
      []
    case Some{i}:
      [i]

def or.unknown(s: String) -> String:
  match s:
    case SNil{}:
      "unknown parse error\n"
    case SCon{h, t}:
      SCon{h, t}

def fan.show(f: Fan) -> String:
  match f:
    case MgFail{m}:
      m
    case MgIndent{l, a}:
      "incorrect indentation (got " ++ U32.show(a) ++ ", should be greater than "
        ++ U32.show(l) ++ ")"

def fans.pretty(fs: List<&2, Fan>) -> String:
  match fs:
    case Nil{}:
      ""
    case Con{f, t}:
      fan.show(f) ++ "\n" ++ fans.pretty(t)

# parseErrorTextPretty
def er.pretty(e: Er) -> String:
  match e:
    case MgTriv{o, u, ps}:
      or.unknown(items.pretty("unexpected ", un.items(u)) ++ items.pretty("expecting ", ps))
    case MgFancy{o, fs}:
      fans.pretty(fs)

def head.name(name: String) -> String:
  match name:
    case SNil{}:
      ""
    case SCon{h, t}:
      SCon{h, t} ++ ":"

def pretty.at(name: String, pr: PosR, +e: Er) -> String:
  match pr:
    case MgPos{+line, +col, ls}:
      +sline = or.empty(expand(tw.take(ls, MgNotNl{}), 0))
      +sl = str.width(sline, 0)
      +shift = (col - 1 : U32)
      +elen = er.elen(e)
      +plen = ptr.len(U32.is_gt((shift + elen : U32), sl), sl, shift, elen)
      +num = U32.show(line)
      +pad = String.repeat(" ", (String.length(num) + 1n : Nat))
      head.name(name) ++ num ++ ":" ++ U32.show(col) ++ ":\n" ++ pad ++ "|\n" ++ num ++ " | "
        ++ sline ++ "\n" ++ pad ++ "| " ++ String.repeat(" ", U32.to_nat(shift))
        ++ String.repeat("^", U32.to_nat(plen)) ++ "\n" ++ er.pretty(e)

# The interface
# -------------

# An error as master shows it, and its offset (for an editor's range).
type Shown is Data:
  MgShown{+off: U32, +text: String}

def pretty(name: String, +text: String, +e: Er) -> Shown:
  MgShown{er.off(e), pretty.at(name, pos.go(text, text, 0, er.off(e), 1, 1), e)}

def done(name: String, +text: String, o: Out) -> Maybe<&2, Shown>:
  match o:
    case MgCErr{e}:
      Some{pretty(name, text, e)}
    case MgEErr{e}:
      Some{pretty(name, text, e)}
    case MgCOk{q, hs}:
      None{}
    case MgEOk{q, hs}:
      None{}

def depth.if(stop: Bool, more: Unit -> Nat, d: Nat) -> Nat:
  match stop:
    case True{}:
      d
    case False{}:
      more(Unit{})

# The memo's depth: one slot per offset, up to 2^20 of them.
def depth(fuel: Nat, +x: U32, +d: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      depth.if(U32.is_eq(x, 0), u => depth(f, U32.shr(x), (d + 1n : Nat)), d)

def fuel() -> Nat:
  U32.to_nat(4294967295)

# Master's error for a text it rejects, by name (the file shown before
# line:column, "" for none); None when master's grammar accepts it.
def check(t: Top, name: String, +text: String) -> Maybe<&2, Shown>:
  +d = depth(20n, U32.from_nat(String.length(text)), 0n)
  done(name, text, run(fuel(), MgMc{Array.new(List<&2, Me>, d, []), 0, 0,
                                    MgEval{top.node(t), MgAt{text, 0, 1}}, []}))

# Master's text for a rejected text, else the port's own.
def shown.or(m: Maybe<&2, Shown>, own: String) -> String:
  match m:
    case Some{s}:
      match s:
        case MgShown{o, x}:
          x
    case None{}:
      own

def message(t: Top, name: String, +text: String, own: String) -> String:
  shown.or(check(t, name, text), own)
