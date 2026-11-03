import Base

# JSON for the language server (Lsp.bend), from mugen (github.com/hhefesto/mugen,
# bend/Json.bend at c3275ba, Apache-2.0, by the same author).
#
# Json: JSON values, read and written as JavaScript's JSON.parse and
# JSON.stringify do (every log record, view.json and API body goes through
# these, so the bytes match UniiChat's). Numbers stay as their text: Bend's
# numbers are U32 and Nat, and a number is only ever passed on or read as
# one of those.
#
# Bend has no mutual recursion, so both directions are loops over a stack:
# the reader over the arrays and objects open, the writer over the items
# still to write. Fuel bounds each loop (every step eats input or output).
#
# Every def is prefixed `js.` (a program's defs share one namespace).

type Json is Data:
  JNull{}
  JBool{v: Bool}
  JNum{raw: String}
  JStr{s: String}
  JArr{xs: List<&2, Json>}
  JObj{kvs: List<&2, JKv>}

type JKv is Data:
  JKv{k: String, v: Json}

def js.fuel() -> Nat:
  U32.to_nat(4294967295)

# Building and reading values -----------------------------------------------

def js.nat(+n: Nat) -> Json:
  JNum{Nat.show(n)}

def js.u32(+n: U32) -> Json:
  JNum{U32.show(n)}

def js.kv(k: String, v: Json) -> JKv:
  JKv{k, v}

# the value under key k (the first), if any
def js.get(kvs: List<&2, JKv>, +k: String) -> Maybe<&2, Json>:
  match kvs:
    case []:
      None{}
    case JKv{+k2, +v} <> t:
      Bool.pick(Maybe<&2, Json>, String.eq(k, k2), Some{v}, js.get(t, k))

def js.field(+j: Json, +k: String) -> Maybe<&2, Json>:
  match j:
    case JObj{kvs}:
      js.get(kvs, k)
    case _:
      None{}

def js.as_str(j: Maybe<&2, Json>) -> Maybe<&2, String>:
  match j:
    case Some{JStr{s}}:
      Some{s}
    case _:
      None{}

def js.as_nat(j: Maybe<&2, Json>) -> Maybe<&2, Nat>:
  match j:
    case Some{JNum{raw}}:
      Nat.read(raw)
    case _:
      None{}

def js.as_bool(j: Maybe<&2, Json>) -> Maybe<&2, Bool>:
  match j:
    case Some{JBool{b}}:
      Some{b}
    case _:
      None{}

def js.as_arr(j: Maybe<&2, Json>) -> List<&2, Json>:
  match j:
    case Some{JArr{xs}}:
      xs
    case _:
      []

def js.str(+j: Json, +k: String) -> Maybe<&2, String>:
  js.as_str(js.field(j, k))

def js.num(+j: Json, +k: String) -> Maybe<&2, Nat>:
  js.as_nat(js.field(j, k))

def js.bool(+j: Json, +k: String) -> Maybe<&2, Bool>:
  js.as_bool(js.field(j, k))

def js.arr(+j: Json, +k: String) -> List<&2, Json>:
  js.as_arr(js.field(j, k))

# Writing (JSON.stringify) --------------------------------------------------

def js.hex(+n: U32) -> U32:
  Bool.pick(U32, U32.is_lt(n, 10), (n + 48 : U32), (n + 87 : U32))

# \uXXXX (lowercase hex), reversed onto out
def js.u4.onto(+c: U32, out: String) -> String:
  SCon{Chr{js.hex(U32.and(c, 15))}, SCon{Chr{js.hex(U32.and(U32.shrn(c, 4n), 15))},
    SCon{Chr{js.hex(U32.and(U32.shrn(c, 8n), 15))}, SCon{Chr{js.hex(U32.and(U32.shrn(c, 12n), 15))},
      SCon{Chr{117}, SCon{Chr{92}, out}}}}}}

# How JSON.stringify writes one scalar: 0 raw, 1 a two-char escape, 2 \u.
def js.esc.kind(+c: U32) -> U32:
  Bool.pick(U32, Bool.or(U32.is_eq(c, 34), U32.is_eq(c, 92)), 1,
    Bool.pick(U32, Bool.or(U32.is_eq(c, 8), Bool.or(U32.is_eq(c, 12), Bool.or(U32.is_eq(c, 10), Bool.or(U32.is_eq(c, 13), U32.is_eq(c, 9))))), 1,
      Bool.pick(U32, Bool.or(U32.is_lt(c, 32), Bool.and(U32.is_ge(c, 55296), U32.is_le(c, 57343))), 2, 0)))

# the letter after the backslash of a two-char escape
def js.esc.letter(+c: U32) -> U32:
  Bool.pick(U32, U32.is_eq(c, 8), 98, Bool.pick(U32, U32.is_eq(c, 12), 102,
    Bool.pick(U32, U32.is_eq(c, 10), 110, Bool.pick(U32, U32.is_eq(c, 13), 114,
      Bool.pick(U32, U32.is_eq(c, 9), 116, c)))))

def js.esc.one(k: Nat, +c: U32, out: String) -> String:
  match k:
    case 0n:
      SCon{Chr{c}, out}
    case 1n:
      SCon{Chr{js.esc.letter(c)}, SCon{Chr{92}, out}}
    case _:
      js.u4.onto(c, out)

# a string's escaped scalars, reversed onto out
def js.esc.onto(s: String, out: String) -> String:
  match s:
    case SNil{}:
      out
    case SCon{Chr{+c}, t}:
      js.esc.onto(t, js.esc.one(U32.to_nat(js.esc.kind(c)), c, out))

# a quoted string, reversed onto out
def js.quote.onto(s: String, out: String) -> String:
  SCon{Chr{34}, js.esc.onto(s, SCon{Chr{34}, out})}

# JSON.stringify of a string
def js.quote(s: String) -> String:
  String.reverse(js.quote.onto(s, ""))

# An item still to write: a value, punctuation, or a key with its colon.
type js.W is Data:
  js.WVal{j: Json}
  js.WLit{c: U32}
  js.WKey{k: String}

def js.item.put(first: Bool, x: js.W, more: List<&2, js.W>) -> List<&2, js.W>:
  match first:
    case True{}:
      x <> more
    case False{}:
      js.WLit{44} <> x <> more

# xs as items, a comma between each, in front of rest
def js.items(xs: List<&2, Json>, first: Bool, rest: List<&2, js.W>) -> List<&2, js.W>:
  match xs:
    case []:
      rest
    case x <> t:
      js.item.put(first, js.WVal{x}, js.items(t, False{}, rest))

def js.pairs(kvs: List<&2, JKv>, first: Bool, rest: List<&2, js.W>) -> List<&2, js.W>:
  match kvs:
    case []:
      rest
    case JKv{k, v} <> t:
      js.item.put(first, js.WKey{k}, js.WVal{v} <> js.pairs(t, False{}, rest))

def js.bool.text(b: Bool) -> String:
  match b:
    case True{}:
      "eurt"
    case False{}:
      "eslaf"

# one value: what it writes now (reversed onto out), what it leaves to write
def js.val(j: Json, ws: List<&2, js.W>, out: String) -> List<&2, js.W> & String:
  match j:
    case JNull{}:
      (ws, String.append("llun", out))
    case JBool{b}:
      (ws, String.append(js.bool.text(b), out))
    case JNum{raw}:
      (ws, String.reverse.go(raw, out))
    case JStr{s}:
      (ws, js.quote.onto(s, out))
    case JArr{xs}:
      (js.items(xs, True{}, js.WLit{93} <> ws), SCon{Chr{91}, out})
    case JObj{kvs}:
      (js.pairs(kvs, True{}, js.WLit{125} <> ws), SCon{Chr{123}, out})

def js.write.go(fuel: Nat, st: List<&2, js.W> & String) -> String:
  match fuel st:
    case _ Tuple{[], out}:
      String.reverse(out)
    case 0n Tuple{ws, out}:
      String.reverse(out)
    case 1n+f Tuple{js.WLit{c} <> ws, out}:
      js.write.go(f, (ws, SCon{Chr{c}, out}))
    case 1n+f Tuple{js.WKey{k} <> ws, out}:
      js.write.go(f, (ws, SCon{Chr{58}, js.quote.onto(k, out)}))
    case 1n+f Tuple{js.WVal{j} <> ws, out}:
      js.write.go(f, js.val(j, ws, out))

# JSON.stringify(j)
def js.write(j: Json) -> String:
  js.write.go(js.fuel(), ([js.WVal{j}], ""))

# Written as Haskell's aeson writes it: every object's keys in order (by
# code point), the rest as js.write. (Added for telomare's language
# server, whose answers master's telomare-lsp writes so.)
def js.kv.le(a: JKv, b: JKv) -> Bool:
  match a:
    case JKv{ka, va}:
      match b:
        case JKv{kb, vb}:
          String.is_le(ka, kb)

def js.val.sorted(j: Json, ws: List<&2, js.W>, out: String) -> List<&2, js.W> & String:
  match j:
    case JObj{kvs}:
      (js.pairs(List.sort(~JKv, ~js.kv.le, kvs), True{}, js.WLit{125} <> ws), SCon{Chr{123}, out})
    case other:
      js.val(other, ws, out)

def js.write.sorted.go(fuel: Nat, st: List<&2, js.W> & String) -> String:
  match fuel st:
    case _ Tuple{[], out}:
      String.reverse(out)
    case 0n Tuple{ws, out}:
      String.reverse(out)
    case 1n+f Tuple{js.WLit{c} <> ws, out}:
      js.write.sorted.go(f, (ws, SCon{Chr{c}, out}))
    case 1n+f Tuple{js.WKey{k} <> ws, out}:
      js.write.sorted.go(f, (ws, SCon{Chr{58}, js.quote.onto(k, out)}))
    case 1n+f Tuple{js.WVal{j} <> ws, out}:
      js.write.sorted.go(f, js.val.sorted(j, ws, out))

def js.write.sorted(j: Json) -> String:
  js.write.sorted.go(js.fuel(), ([js.WVal{j}], ""))

# Reading (JSON.parse) ------------------------------------------------------

# What a scalar starts: an object, an array, a string, a number, a literal.
type js.C is Data:
  js.CObj{}
  js.CArr{}
  js.CStr{}
  js.CNum{}
  js.CTrue{}
  js.CFalse{}
  js.CNull{}
  js.CBad{}

def js.class(+c: U32) -> js.C:
  Bool.pick(js.C, U32.is_eq(c, 123), js.CObj{}, Bool.pick(js.C, U32.is_eq(c, 91), js.CArr{},
    Bool.pick(js.C, U32.is_eq(c, 34), js.CStr{}, Bool.pick(js.C, Bool.or(U32.is_eq(c, 45), Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57))), js.CNum{},
      Bool.pick(js.C, U32.is_eq(c, 116), js.CTrue{}, Bool.pick(js.C, U32.is_eq(c, 102), js.CFalse{},
        Bool.pick(js.C, U32.is_eq(c, 110), js.CNull{}, js.CBad{})))))))

def js.ws.is(+c: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(c, 32), U32.is_eq(c, 10)), Bool.or(U32.is_eq(c, 13), U32.is_eq(c, 9)))

def js.head(+s: String) -> U32:
  match s:
    case SNil{}:
      4294967295
    case SCon{Chr{c}, t}:
      c

def js.head.ws(+s: String) -> Bool:
  js.ws.is(js.head(s))

def js.ws.go(s: String, sp: Bool) -> String:
  match s sp:
    case SCon{h, +t} True{}:
      js.ws.go(t, js.head.ws(t))
    case SNil{} _:
      SNil{}
    case SCon{h, t} False{}:
      SCon{h, t}

# s past its leading JSON whitespace
def js.ws(+s: String) -> String:
  js.ws.go(s, js.head.ws(s))

def js.tail(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      t

# Strings: a scalar of a string's body is a quote (its end), a backslash
# (an escape), or itself.
type js.S is Data:
  js.SEnd{}
  js.SEsc{}
  js.SChr{}
  js.SBad{}

def js.s.class(+c: U32) -> js.S:
  Bool.pick(js.S, U32.is_eq(c, 34), js.SEnd{}, Bool.pick(js.S, U32.is_eq(c, 92), js.SEsc{},
    Bool.pick(js.S, U32.is_lt(c, 32), js.SBad{}, js.SChr{})))

def js.s.class.of(+s: String) -> js.S:
  match s:
    case SNil{}:
      js.SBad{}
    case SCon{Chr{+c}, t}:
      js.s.class(c)

# a hex digit's value, or 16
def js.hexv(+c: U32) -> U32:
  Bool.pick(U32, Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)), (c - 48 : U32),
    Bool.pick(U32, Bool.and(U32.is_ge(c, 97), U32.is_le(c, 102)), (c - 87 : U32),
      Bool.pick(U32, Bool.and(U32.is_ge(c, 65), U32.is_le(c, 70)), (c - 55 : U32), 16)))

# the four hex digits at the front of s, as a code unit (65536 if not hex)
def js.hex4(+s: String) -> U32:
  match s:
    case SCon{Chr{+a}, SCon{Chr{+b}, SCon{Chr{+c}, SCon{Chr{+d}, t}}}}:
      Bool.pick(U32, Bool.or(Bool.or(U32.is_eq(js.hexv(a), 16), U32.is_eq(js.hexv(b), 16)), Bool.or(U32.is_eq(js.hexv(c), 16), U32.is_eq(js.hexv(d), 16))), 65536,
        U32.or(U32.or(U32.shln(js.hexv(a), 12n), U32.shln(js.hexv(b), 8n)), U32.or(U32.shln(js.hexv(c), 4n), js.hexv(d))))
    case _:
      65536

# A \u escape: the scalar it makes and how many chars past the backslash
# it eats: 5 (\uXXXX), or 11 for a surrogate pair (\uD8xx\uDCxx). A lone
# surrogate reads as U+FFFD (Bend's strings hold scalars only; UniiChat
# makes every message well-formed anyway: toWellFormed).
type js.U is Data:
  js.U{c: U32, eat: Nat}

def js.u.low(+hi: U32, +lo: U32) -> js.U:
  Bool.pick(js.U, Bool.and(U32.is_ge(lo, 56320), U32.is_le(lo, 57343)),
    js.U{(65536 + (U32.shln((hi - 55296 : U32), 10n) + (lo - 56320 : U32) : U32) : U32), 11n}, js.U{65533, 5n})

def js.u.pair(+hi: U32, +s: String) -> js.U:
  match s:
    case SCon{Chr{+b}, SCon{Chr{+u}, +r}}:
      Bool.pick(js.U, Bool.and(U32.is_eq(b, 92), U32.is_eq(u, 117)), js.u.low(hi, js.hex4(r)), js.U{65533, 5n})
    case _:
      js.U{65533, 5n}

def js.u.got(+hi: U32, +r: String) -> js.U:
  Bool.pick(js.U, Bool.and(U32.is_ge(hi, 55296), U32.is_le(hi, 56319)), js.u.pair(hi, String.drop(r, 4n)),
    Bool.pick(js.U, Bool.and(U32.is_ge(hi, 56320), U32.is_le(hi, 57343)), js.U{65533, 5n}, js.U{hi, 5n}))

# s starts after the backslash: u, the four digits, maybe \u and four more
def js.u.read(+s: String) -> js.U:
  match s:
    case SCon{u1, +r}:
      js.u.got(js.hex4(r), r)
    case _:
      js.U{65536, 1n}

# A string's body read: the scalars (reversed) and the rest past the quote,
# or nothing (ill-formed).
type js.R is Data:
  js.ROk{s: String, rest: String}
  js.RBad{}

def js.esc.simple(+c: U32) -> U32:
  Bool.pick(U32, U32.is_eq(c, 98), 8, Bool.pick(U32, U32.is_eq(c, 102), 12,
    Bool.pick(U32, U32.is_eq(c, 110), 10, Bool.pick(U32, U32.is_eq(c, 114), 13,
      Bool.pick(U32, U32.is_eq(c, 116), 9, Bool.pick(U32, Bool.or(U32.is_eq(c, 34), Bool.or(U32.is_eq(c, 92), U32.is_eq(c, 47))), c, 65536))))))

# An escape read (t starts after the backslash): its scalar (65536 if
# ill-formed) and the rest.
type js.E is Data:
  js.E{c: U32, rest: String}

def js.esc.u(u: js.U, t: String) -> js.E:
  match u:
    case js.U{c, eat}:
      js.E{c, String.drop(t, eat)}

def js.esc.next(+t: String) -> js.E:
  Bool.pick(js.E, U32.is_eq(js.head(t), 117), js.esc.u(js.u.read(t), t), js.E{js.esc.simple(js.head(t)), js.tail(t)})

def js.e.c(e: js.E) -> U32:
  match e:
    case js.E{c, rest}:
      c

def js.e.rest(e: js.E) -> String:
  match e:
    case js.E{c, rest}:
      rest

# the class of what follows an escape, SBad when the escape was ill-formed
def js.e.class(e: js.E) -> js.S:
  match e:
    case js.E{+c, +rest}:
      Bool.pick(js.S, U32.is_eq(c, 65536), js.SBad{}, js.s.class.of(rest))

def js.str.go(fuel: Nat, s: String, k: js.S, acc: String) -> js.R:
  match fuel s k:
    case 0n _ _:
      js.RBad{}
    case 1n+f SCon{q, t} js.SEnd{}:
      js.ROk{acc, t}
    case 1n+f SCon{c, +t} js.SChr{}:
      js.str.go(f, t, js.s.class.of(t), SCon{c, acc})
    case 1n+f SCon{b, +t} js.SEsc{}:
      +e = js.esc.next(t)
      js.str.go(f, js.e.rest(e), js.e.class(e), SCon{Chr{js.e.c(e)}, acc})
    case _ _ _:
      js.RBad{}

# the string at the front of s (s at its quote), its scalars reversed
def js.str.read(+s: String) -> js.R:
  js.str.go(js.fuel(), js.tail(s), js.s.class.of(js.tail(s)), "")

# Numbers: their text as it is (the chars a JSON number may hold).
def js.num.is(+c: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(c, 48), U32.is_le(c, 57)),
    Bool.or(Bool.or(U32.is_eq(c, 45), U32.is_eq(c, 43)), Bool.or(U32.is_eq(c, 46), Bool.or(U32.is_eq(c, 101), U32.is_eq(c, 69)))))

def js.num.go(s: String, more: Bool, acc: String) -> String & String:
  match s more:
    case SCon{c, +t} True{}:
      js.num.go(t, js.num.is(js.head(t)), SCon{c, acc})
    case SNil{} _:
      (String.reverse(acc), SNil{})
    case SCon{h, t} False{}:
      (String.reverse(acc), SCon{h, t})

# Punctuation after a value: a comma, a closing bracket or brace, a colon.
type js.Q is Data:
  js.QComma{}
  js.QArr{}
  js.QObj{}
  js.QBad{}

def js.punct(+c: U32) -> js.Q:
  Bool.pick(js.Q, U32.is_eq(c, 44), js.QComma{}, Bool.pick(js.Q, U32.is_eq(c, 93), js.QArr{},
    Bool.pick(js.Q, U32.is_eq(c, 125), js.QObj{}, js.QBad{})))

# An open container: an array's items so far, or an object's pairs so far
# and the key whose value comes next (both reversed).
type js.F is Data:
  js.FArr{acc: List<&2, Json>}
  js.FObj{acc: List<&2, JKv>, key: String}

# The reader: a value starts at s, or one was just read and s follows it.
type js.P is Data:
  js.PVal{s: String, stack: List<&2, js.F>}
  js.PGot{v: Json, s: String, stack: List<&2, js.F>}
  js.PDone{v: Json}
  js.PBad{}

# A key read: it, and the rest past its colon.
type js.K is Data:
  js.KOk{key: String, rest: String}
  js.KBad{}

def js.key.fin(key: String, +s: String) -> js.K:
  Bool.pick(js.K, U32.is_eq(js.head(s), 58), js.KOk{key, js.tail(s)}, js.KBad{})

def js.key.colon(r: js.R) -> js.K:
  match r:
    case js.RBad{}:
      js.KBad{}
    case js.ROk{rev, rest}:
      js.key.fin(String.reverse(rev), js.ws(rest))

def js.key.at(q: Bool, +s: String) -> js.K:
  match q:
    case True{}:
      js.key.colon(js.str.read(s))
    case False{}:
      js.KBad{}

# a key and its colon at the front of s (s at the key's quote)
def js.key(+s: String) -> js.K:
  js.key.at(U32.is_eq(js.head(s), 34), s)

def js.p.key(k: js.K, acc: List<&2, JKv>, stack: List<&2, js.F>) -> js.P:
  match k:
    case js.KBad{}:
      js.PBad{}
    case js.KOk{key, rest}:
      js.PVal{rest, js.FObj{acc, key} <> stack}

def js.p.str(r: js.R, stack: List<&2, js.F>) -> js.P:
  match r:
    case js.RBad{}:
      js.PBad{}
    case js.ROk{rev, rest}:
      js.PGot{JStr{String.reverse(rev)}, rest, stack}

def js.p.lit(ok: Bool, v: Json, +s: String, +n: Nat, stack: List<&2, js.F>) -> js.P:
  match ok:
    case True{}:
      js.PGot{v, String.drop(s, n), stack}
    case False{}:
      js.PBad{}

def js.p.num(p: String & String, stack: List<&2, js.F>) -> js.P:
  match p:
    case (raw, rest):
      js.PGot{JNum{raw}, rest, stack}

# an object or array opened at s: empty, or its first key or item next
def js.p.obj.at(empty: Bool, +s: String, stack: List<&2, js.F>) -> js.P:
  match empty:
    case True{}:
      js.PGot{JObj{[]}, js.tail(s), stack}
    case False{}:
      js.p.key(js.key(s), [], stack)

def js.p.obj(+s: String, stack: List<&2, js.F>) -> js.P:
  js.p.obj.at(U32.is_eq(js.head(s), 125), s, stack)

def js.p.arr.at(empty: Bool, +s: String, stack: List<&2, js.F>) -> js.P:
  match empty:
    case True{}:
      js.PGot{JArr{[]}, js.tail(s), stack}
    case False{}:
      js.PVal{s, js.FArr{[]} <> stack}

def js.p.arr(+s: String, stack: List<&2, js.F>) -> js.P:
  js.p.arr.at(U32.is_eq(js.head(s), 93), s, stack)

# a value starts at s (past its whitespace)
def js.p.val(k: js.C, +s: String, stack: List<&2, js.F>) -> js.P:
  match k:
    case js.CObj{}:
      js.p.obj(js.ws(js.tail(s)), stack)
    case js.CArr{}:
      js.p.arr(js.ws(js.tail(s)), stack)
    case js.CStr{}:
      js.p.str(js.str.read(s), stack)
    case js.CNum{}:
      js.p.num(js.num.go(s, True{}, ""), stack)
    case js.CTrue{}:
      js.p.lit(String.starts_with(s, "true"), JBool{True{}}, s, 4n, stack)
    case js.CFalse{}:
      js.p.lit(String.starts_with(s, "false"), JBool{False{}}, s, 5n, stack)
    case js.CNull{}:
      js.p.lit(String.starts_with(s, "null"), JNull{}, s, 4n, stack)
    case js.CBad{}:
      js.PBad{}

# a value v was read, and s (past its whitespace) follows it
def js.p.arr.on(q: js.Q, v: Json, s: String, acc: List<&2, Json>, stack: List<&2, js.F>) -> js.P:
  match q:
    case js.QComma{}:
      js.PVal{js.tail(s), js.FArr{v <> acc} <> stack}
    case js.QArr{}:
      js.PGot{JArr{List.reverse(&2, Json, v <> acc)}, js.tail(s), stack}
    case _:
      js.PBad{}

def js.p.obj.on(q: js.Q, kv: JKv, s: String, acc: List<&2, JKv>, stack: List<&2, js.F>) -> js.P:
  match q:
    case js.QComma{}:
      js.p.key(js.key(js.ws(js.tail(s))), kv <> acc, stack)
    case js.QObj{}:
      js.PGot{JObj{List.reverse(&2, JKv, kv <> acc)}, js.tail(s), stack}
    case _:
      js.PBad{}

def js.p.got(v: Json, +s: String, stack: List<&2, js.F>) -> js.P:
  match stack:
    case []:
      js.PDone{v}
    case js.FArr{acc} <> rest:
      js.p.arr.on(js.punct(js.head(s)), v, s, acc, rest)
    case js.FObj{acc, key} <> rest:
      js.p.obj.on(js.punct(js.head(s)), JKv{key, v}, s, acc, rest)

def js.read.go(fuel: Nat, p: js.P) -> Maybe<&2, Json>:
  match fuel p:
    case _ js.PDone{v}:
      Some{v}
    case _ js.PBad{}:
      None{}
    case 0n _:
      None{}
    case 1n+f js.PVal{s, stack}:
      +w = js.ws(s)
      js.read.go(f, js.p.val(js.class(js.head(w)), w, stack))
    case 1n+f js.PGot{v, s, stack}:
      js.read.go(f, js.p.got(v, js.ws(s), stack))

# JSON.parse(s), or None{} if s is not JSON
def js.read(s: String) -> Maybe<&2, Json>:
  js.read.go(js.fuel(), js.PVal{s, []})
