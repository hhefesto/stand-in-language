import Base
import ./Loc.bend as L
import ./Core.bend as Co
import ./Text.bend as Tx
import ./Sha256.bend as Sha

# The bytes of a compiled program: the writers and the readers Telc.bend and
# IC.bend share. Integers are int64 little-endian; a string is its UTF-8
# length, then its UTF-8. IC.bend reads a program back when a result holds a
# closure, so these sit below it.

# Writing
# -------
#
# Each writer puts its bytes before rest.

# An int64, little-endian, from a U32. One from 2^31 up is negative (a
# reserved function index), so its high word is all ones.
def put.int(+n: U32, rest: List<&2, U32>) -> List<&2, U32>:
  +hi = Bool.pick(U32, U32.is_ge(n, 2147483648), 255, 0)
  U32.and(n, 255) <> U32.and(U32.shrn(n, 8n), 255) <> U32.and(U32.shrn(n, 16n), 255) <> U32.shrn(n, 24n)
    <> hi <> hi <> hi <> hi <> rest

def put.string(s: String, rest: List<&2, U32>) -> List<&2, U32>:
  +bs = Sha.utf8(s)
  put.int(U32.from_nat(List.length(&2, U32, bs)), List.append(&2, U32, bs, rest))

def put.file(file: String, rest: List<&2, U32>) -> List<&2, U32>:
  match file:
    case SNil{}:
      0 <> rest
    case SCon{c, t}:
      1 <> put.string(SCon{c, t}, rest)

def put.pos(p: L.Pos, rest: List<&2, U32>) -> List<&2, U32>:
  match p:
    case L.Pos{line, col, off}:
      put.int(line, put.int(col, put.int(off, rest)))

def put.loc(l: L.Loc, rest: List<&2, U32>) -> List<&2, U32>:
  match l:
    case L.Src{file, start, stop}:
      0 <> put.file(file, put.pos(start, put.pos(stop, rest)))
    case L.GenIn{reason, parent}:
      1 <> put.string(reason, 1 <> put.loc(parent, rest))
    case L.Gen{reason}:
      1 <> put.string(reason, 0 <> rest)
    case L.Builtin{name}:
      2 <> put.string(name, rest)
    case L.RuntimeLoc{}:
      3 <> rest
    case L.DecompiledLoc{}:
      4 <> rest
    case L.Unknown{}:
      5 <> rest

def put.origin(o: L.Origin, rest: List<&2, U32>) -> List<&2, U32>:
  match o:
    case L.Origin{k, l}:
      L.kind.tag(k) <> put.loc(l, rest)

def put.basic(d: Co.D, rest: List<&2, U32>) -> List<&2, U32>:
  match d:
    case Co.DZero{}:
      0 <> rest
    case Co.DPair{a, b}:
      1 <> put.basic(a, put.basic(b, rest))

def put.expr(v: Co.V, rest: List<&2, U32>) -> List<&2, U32>:
  match v:
    case Co.VZero{}:
      0 <> rest
    case Co.VPair{a, b}:
      1 <> put.expr(a, put.expr(b, rest))
    case Co.VEnv{}:
      2 <> rest
    case Co.VSetEnv{x}:
      3 <> put.expr(x, rest)
    case Co.VDefer{fi, x}:
      4 <> put.int(fi, put.expr(x, rest))
    case Co.VGate{}:
      5 <> rest
    case Co.VLeft{x}:
      6 <> put.expr(x, rest)
    case Co.VRight{x}:
      7 <> put.expr(x, rest)
    case Co.VAbort{o, m}:
      8 <> put.origin(o, put.expr(m, rest))

# Reading
# -------

def fuel() -> Nat:
  U32.to_nat(4294967295)

# A reader's result: the value and the bytes after it, or why the bytes
# ran short or made no sense.
type Got<-A: Data> is Data:
  Got{+x: A, +rest: List<&2, U32>}
  Bad{+why: String}

def G(-A: Data) -> Type:
  List<&2, U32> -> Got<A>

def G.pure(-A: Data, x: A) -> G(A):
  bs => Got{x, bs}

def G.fail(-A: Data, why: String) -> G(A):
  bs => Bad{why}

def G.run(-A: Data, -B: Data, f: A -> G(B), r: Got<A>) -> Got<B>:
  match r:
    case Got{x, rest}:
      f(x)(rest)
    case Bad{why}:
      Bad{why}

def G.bind(-A: Data, -B: Data, m: G(A), f: A -> G(B)) -> G(B):
  bs => G.run(A, B, f, m(bs))

def byte.of(bs: List<&2, U32>) -> Got<U32>:
  match bs:
    case Nil{}:
      Bad{"not enough bytes"}
    case Con{b, rest}:
      Got{b, rest}

def byte() -> G(U32):
  bs => byte.of(bs)

def take(n: Nat) -> G(List<&2, U32>):
  match n:
    case 0n:
      G.pure(List<&2, U32>, [])
    case 1n+k:
      do G<List<&2, U32>>:
        b : U32 <- byte()
        bs : List<&2, U32> <- take(k)
        return b <> bs

# An int64, little-endian; its low word.
def int() -> G(U32):
  do G<U32>:
    b0 : U32 <- byte()
    b1 : U32 <- byte()
    b2 : U32 <- byte()
    b3 : U32 <- byte()
    hi : List<&2, U32> <- take(4n)
    return (b0 + U32.shln(b1, 8n) + U32.shln(b2, 16n) + U32.shln(b3, 24n) : U32)

# An int64, big-endian (Data.Binary's); its low word.
def int.be() -> G(U32):
  do G<U32>:
    hi : List<&2, U32> <- take(4n)
    b3 : U32 <- byte()
    b2 : U32 <- byte()
    b1 : U32 <- byte()
    b0 : U32 <- byte()
    return (b0 + U32.shln(b1, 8n) + U32.shln(b2, 16n) + U32.shln(b3, 24n) : U32)

def string() -> G(String):
  do G<String>:
    n : U32 <- int()
    bs : List<&2, U32> <- take(U32.to_nat(n))
    return Tx.utf8(bs)

def maybe.int(+m: U32) -> G(Maybe<&2, U32>):
  match m:
    case 0:
      G.pure(Maybe<&2, U32>, None{})
    case _:
      G.bind(U32, Maybe<&2, U32>, int(), n => G.pure(Maybe<&2, U32>, Some{n}))

def file.of(+m: U32) -> G(String):
  match m:
    case 0:
      G.pure(String, "")
    case _:
      string()

def pos() -> G(L.Pos):
  do G<L.Pos>:
    line : U32 <- int()
    col : U32 <- int()
    off : U32 <- int()
    return L.Pos{line, col, off}

def span() -> G(L.Loc):
  do G<L.Loc>:
    m : U32 <- byte()
    file : String <- file.of(m)
    start : L.Pos <- pos()
    stop : L.Pos <- pos()
    return L.Src{file, start, stop}

def generated(+m: U32, +reason: String, parent: G(L.Loc)) -> G(L.Loc):
  match m:
    case 0:
      G.pure(L.Loc, L.Gen{reason})
    case _:
      G.bind(L.Loc, L.Loc, parent, p => G.pure(L.Loc, L.GenIn{reason, p}))

def loc.node(+t: U32, parent: G(L.Loc)) -> G(L.Loc):
  match t:
    case 0:
      span()
    case 1:
      do G<L.Loc>:
        reason : String <- string()
        m : U32 <- byte()
        generated(m, reason, parent)
    case 2:
      G.bind(String, L.Loc, string(), name => G.pure(L.Loc, L.Builtin{name}))
    case 3:
      G.pure(L.Loc, L.RuntimeLoc{})
    case 4:
      G.pure(L.Loc, L.DecompiledLoc{})
    case 5:
      G.pure(L.Loc, L.Unknown{})
    case _:
      G.fail(L.Loc, "unknown location tag " ++ U32.show(t))

def loc(+fuel: Nat) -> G(L.Loc):
  match fuel:
    case 0n:
      G.fail(L.Loc, "nesting too deep")
    case 1n+f:
      G.bind(U32, L.Loc, byte(), t => loc.node(t, loc(f)))

def basic.node(+t: U32, a: G(Co.D), b: G(Co.D)) -> G(Co.D):
  match t:
    case 0:
      G.pure(Co.D, Co.DZero{})
    case 1:
      do G<Co.D>:
        x : Co.D <- a
        y : Co.D <- b
        return Co.DPair{x, y}
    case _:
      G.fail(Co.D, "unknown basic node tag " ++ U32.show(t))

def basic(+fuel: Nat) -> G(Co.D):
  match fuel:
    case 0n:
      G.fail(Co.D, "nesting too deep")
    case 1n+f:
      G.bind(U32, Co.D, byte(), t => basic.node(t, basic(f), basic(f)))

def defer(+fi: U32, x: G(Co.V)) -> G(Co.V):
  G.bind(Co.V, Co.V, x, b => G.pure(Co.V, Co.VDefer{fi, b}))

def origin.kind(m: Maybe<&2, L.AbortKind>, +t: U32) -> G(L.AbortKind):
  match m:
    case Some{k}:
      G.pure(L.AbortKind, k)
    case None{}:
      G.fail(L.AbortKind, "unknown abort kind " ++ U32.show(t))

def origin(+fuel: Nat) -> G(L.Origin):
  do G<L.Origin>:
    +t : U32 <- byte()
    k : L.AbortKind <- origin.kind(L.kind.of.tag(t), t)
    l : L.Loc <- loc(fuel)
    return L.Origin{k, l}

def expr.node(+t: U32, a: G(Co.V), b: G(Co.V), +fuel: Nat) -> G(Co.V):
  match t:
    case 0:
      G.pure(Co.V, Co.VZero{})
    case 1:
      do G<Co.V>:
        x : Co.V <- a
        y : Co.V <- b
        return Co.VPair{x, y}
    case 2:
      G.pure(Co.V, Co.VEnv{})
    case 3:
      G.bind(Co.V, Co.V, a, x => G.pure(Co.V, Co.VSetEnv{x}))
    case 4:
      G.bind(U32, Co.V, int(), fi => defer(fi, a))
    case 5:
      G.pure(Co.V, Co.VGate{})
    case 6:
      G.bind(Co.V, Co.V, a, x => G.pure(Co.V, Co.VLeft{x}))
    case 7:
      G.bind(Co.V, Co.V, a, x => G.pure(Co.V, Co.VRight{x}))
    case 8:
      do G<Co.V>:
        o : L.Origin <- origin(fuel)
        m : Co.V <- a
        return Co.VAbort{o, m}
    case _:
      G.fail(Co.V, "unknown compiled node tag " ++ U32.show(t))

def expr(+fuel: Nat) -> G(Co.V):
  match fuel:
    case 0n:
      G.fail(Co.V, "nesting too deep")
    case 1n+f:
      G.bind(U32, Co.V, byte(), t => expr.node(t, expr(f), expr(f), f))

# The bytes from here on, left in place.
def here.of(+bs: List<&2, U32>) -> Got<List<&2, U32>>:
  Got{bs, bs}

def here() -> G(List<&2, U32>):
  bs => here.of(bs)

def skip.of(n: Nat, bs: List<&2, U32>) -> Got<Unit>:
  match n:
    case 0n:
      Got{Unit{}, bs}
    case 1n+k:
      match bs:
        case Nil{}:
          Bad{"not enough bytes"}
        case Con{b, rest}:
          skip.of(k, rest)

# n bytes passed over.
def skip(n: Nat) -> G(Unit):
  bs => skip.of(n, bs)

def got.value(r: Got<Co.V>) -> Maybe<&2, Co.V>:
  match r:
    case Got{x, rest}:
      Some{x}
    case Bad{why}:
      None{}

# The program at the start of these bytes.
def expr.of(bs: List<&2, U32>) -> Maybe<&2, Co.V>:
  got.value(expr(fuel())(bs))
