import Base
import ./Loc.bend as L
import ./Core.bend as Co
import ./Lift.bend as Lf
import ./Text.bend as Tx
import ./Sha256.bend as Sha
import ./Front.bend as Fr
import ./Term.bend as T
import ./Expr.bend as E
import ./Certificate.bend as Ct

# Compiled programs (haskell-final's Telomare.Artifact): a sized program
# with what a run and `--certificate` need, so neither needs the sources
# again. The bytes are haskell-final's version 4: "TELC", the version, the
# entry module, the sources' hash, the static report as rendered, the
# sizing report (each site's count and location, and the budget), the
# sized program, haskell-final's IC certificate (the port writes none, and
# skips one it reads), and the capture layouts the program runs under.
# Integers are int64 little-endian; a string is its UTF-8 length, then its
# UTF-8; a Maybe is byte 0, or 1 and the value; a map is its length, then
# its entries in ascending key order.

# A site's count (None: not sized) and a site's location, by token.
type Count is Data:
  Count{+tok: U32, +n: Maybe<&2, U32>}

type Place is Data:
  Place{+tok: U32, +loc: L.Loc}

# A capture layout, by its code's hash.
type Layout is Data:
  Layout{+digest: String, +shape: Lf.Shape}

type Telc is Data:
  Telc{+entry: String, +hash: String, +cert: String, +counts: List<&2, Count>, +places: List<&2, Place>,
       +budget: U32, +expr: Co.V, +layouts: List<&2, Layout>}

def version() -> U32:
  4

# The sources' hash (sourcesHash): SHA-256 of every module's name and text
# with their lengths, the modules sorted by name, in lowercase hex.
def src.le(a: Fr.Src, b: Fr.Src) -> Bool:
  match a:
    case Fr.Src{na, ta}:
      match b:
        case Fr.Src{nb, tb}:
          String.is_le(na, nb)

def chunks(srcs: List<&2, Fr.Src>) -> String:
  match srcs:
    case Nil{}:
      ""
    case Con{s, rest}:
      match s:
        case Fr.Src{+name, +text}:
          Nat.show(String.length(name)) ++ ":" ++ name ++ Nat.show(String.length(text)) ++ ":" ++ text ++ chunks(rest)

def sources.hash(srcs: List<&2, Fr.Src>) -> String:
  Sha.string(chunks(List.sort(~Fr.Src, ~src.le, srcs)))

# How many nodes a program has (nodeCount).
def nodes(v: Co.V) -> U32:
  match v:
    case Co.VPair{a, b}:
      (1 + nodes(a) + nodes(b) : U32)
    case Co.VSetEnv{x}:
      (1 + nodes(x) : U32)
    case Co.VDefer{fi, x}:
      (1 + nodes(x) : U32)
    case Co.VLeft{x}:
      (1 + nodes(x) : U32)
    case Co.VRight{x}:
      (1 + nodes(x) : U32)
    case _:
      1

# An artifact of a sized program
# -------------------------------

def counted(cs: List<&2, E.TS>) -> List<&2, Count>:
  match cs:
    case Nil{}:
      []
    case Con{c, rest}:
      match c:
        case E.TS{tok, n}:
          Count{tok, Some{n}} <> counted(rest)

def placed.at(+tok: U32, r: Map<&2, L.Loc> & Maybe<&2, L.Loc>, rest: List<&2, Place>) -> List<&2, Place>:
  (m, l) = r
  match l:
    case Some{loc}:
      Place{tok, loc} <> rest
    case None{}:
      rest

# Each sized site's location, by token.
def placed(cs: List<&2, E.TS>, +ls: Map<&2, L.Loc>) -> List<&2, Place>:
  match cs:
    case Nil{}:
      []
    case Con{c, rest}:
      match c:
        case E.TS{+tok, n}:
          placed.at(tok, Map.pop(&2, L.Loc, ls, U32.show(tok)), placed(rest, ls))

def layout.le(a: Sigma<&2, &2, String, _ => Lf.Shape>, b: Sigma<&2, &2, String, _ => Lf.Shape>) -> Bool:
  match a:
    case (ka, x):
      match b:
        case (kb, y):
          String.is_le(ka, kb)

def laid(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Shape>>) -> List<&2, Layout>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (k, shape):
          Layout{k, shape} <> laid(rest)

# The capture layouts, by hash, in ascending order.
def layouts.of(m: Map<&2, Lf.Shape>) -> List<&2, Layout>:
  laid(List.sort(~Sigma<&2, &2, String, _ => Lf.Shape>, ~layout.le, Map.to_list(&2, Lf.Shape, m)))

# A sized program as an artifact: its entry, the sources' hash, the static
# report as rendered, each site's count and location, the budget, the
# program and its capture layouts.
def of(+entry: String, srcs: List<&2, Fr.Src>, +counts: List<&2, E.TS>, run: T.C, expr: Co.V, cert: String, +budget: U32, ls: Map<&2, Lf.Shape>) -> Telc:
  Telc{entry, sources.hash(srcs), cert, counted(counts), placed(counts, Ct.locs(run, Map.new(&2, L.Loc))), budget, expr, layouts.of(ls)}

# The layouts as the IC looks them up.
def shapes(ls: List<&2, Layout>, acc: Map<&2, Lf.Shape>) -> Map<&2, Lf.Shape>:
  match ls:
    case Nil{}:
      acc
    case Con{l, rest}:
      match l:
        case Layout{digest, shape}:
          shapes(rest, Map.set(&2, Lf.Shape, acc, digest, shape))

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
    case Co.VAbort{}:
      8 <> rest
    case Co.VAborted{m}:
      9 <> put.basic(m, rest)

def put.shape(s: Lf.Shape, rest: List<&2, U32>) -> List<&2, U32>:
  match s:
    case Lf.CapData{}:
      0 <> rest
    case Lf.CapCode{}:
      1 <> rest
    case Lf.CapOther{}:
      2 <> rest
    case Lf.CapPair{a, b}:
      3 <> put.shape(a, put.shape(b, rest))

def put.counts(cs: List<&2, Count>, rest: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      rest
    case Con{c, more}:
      match c:
        case Count{tok, n}:
          match n:
            case None{}:
              put.int(tok, 0 <> put.counts(more, rest))
            case Some{k}:
              put.int(tok, 1 <> put.int(k, put.counts(more, rest)))

def put.places(ps: List<&2, Place>, rest: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      rest
    case Con{p, more}:
      match p:
        case Place{tok, loc}:
          put.int(tok, put.loc(loc, put.places(more, rest)))

def put.layouts(ls: List<&2, Layout>, rest: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      rest
    case Con{l, more}:
      match l:
        case Layout{digest, shape}:
          put.string(digest, put.shape(shape, put.layouts(more, rest)))

def count(-A: Data, xs: List<&2, A>) -> U32:
  U32.from_nat(List.length(&2, A, xs))

# The sizing report: the counts, the places and the budget.
def put.report(+cs: List<&2, Count>, +ps: List<&2, Place>, +budget: U32, rest: List<&2, U32>) -> List<&2, U32>:
  put.int(count(Count, cs), put.counts(cs, put.int(count(Place, ps), put.places(ps, put.int(budget, rest)))))

# The program, no IC certificate, and the layouts.
def put.program(expr: Co.V, +ls: List<&2, Layout>) -> List<&2, U32>:
  put.expr(expr, 0 <> put.int(count(Layout, ls), put.layouts(ls, [])))

def encode(t: Telc) -> List<&2, U32>:
  match t:
    case Telc{entry, hash, cert, counts, places, budget, expr, layouts}:
      84 <> 69 <> 76 <> 67 <> put.int(version(),
        put.string(entry, put.string(hash, put.string(cert,
          put.report(counts, places, budget, put.program(expr, layouts))))))

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
      G.pure(Co.V, Co.VAbort{})
    case 9:
      G.bind(Co.D, Co.V, basic(fuel), m => G.pure(Co.V, Co.VAborted{m}))
    case _:
      G.fail(Co.V, "unknown compiled node tag " ++ U32.show(t))

def expr(+fuel: Nat) -> G(Co.V):
  match fuel:
    case 0n:
      G.fail(Co.V, "nesting too deep")
    case 1n+f:
      G.bind(U32, Co.V, byte(), t => expr.node(t, expr(f), expr(f), f))

def shape.node(+t: U32, a: G(Lf.Shape), b: G(Lf.Shape)) -> G(Lf.Shape):
  match t:
    case 0:
      G.pure(Lf.Shape, Lf.CapData{})
    case 1:
      G.pure(Lf.Shape, Lf.CapCode{})
    case 2:
      G.pure(Lf.Shape, Lf.CapOther{})
    case 3:
      do G<Lf.Shape>:
        x : Lf.Shape <- a
        y : Lf.Shape <- b
        return Lf.CapPair{x, y}
    case _:
      G.fail(Lf.Shape, "unknown capture shape tag " ++ U32.show(t))

def shape(+fuel: Nat) -> G(Lf.Shape):
  match fuel:
    case 0n:
      G.fail(Lf.Shape, "nesting too deep")
    case 1n+f:
      G.bind(U32, Lf.Shape, byte(), t => shape.node(t, shape(f), shape(f)))

def counts(n: Nat) -> G(List<&2, Count>):
  match n:
    case 0n:
      G.pure(List<&2, Count>, [])
    case 1n+k:
      do G<List<&2, Count>>:
        tok : U32 <- int()
        m : U32 <- byte()
        c : Maybe<&2, U32> <- maybe.int(m)
        rest : List<&2, Count> <- counts(k)
        return Count{tok, c} <> rest

def places(n: Nat) -> G(List<&2, Place>):
  match n:
    case 0n:
      G.pure(List<&2, Place>, [])
    case 1n+k:
      do G<List<&2, Place>>:
        tok : U32 <- int()
        l : L.Loc <- loc(fuel())
        rest : List<&2, Place> <- places(k)
        return Place{tok, l} <> rest

def layouts(n: Nat) -> G(List<&2, Layout>):
  match n:
    case 0n:
      G.pure(List<&2, Layout>, [])
    case 1n+k:
      do G<List<&2, Layout>>:
        digest : String <- string()
        s : Lf.Shape <- shape(fuel())
        rest : List<&2, Layout> <- layouts(k)
        return Layout{digest, s} <> rest

# haskell-final's IC certificate, skipped: its method, then three bounds,
# each a list of affine forms (a map of Data.Binary Integers to Naturals,
# and a Natural).
def big.bytes(+t: U32, +small: Nat) -> G(Unit):
  match t:
    case 0:
      G.bind(List<&2, U32>, Unit, take(small), bs => G.pure(Unit, Unit{}))
    case _:
      G.bind(U32, Unit, int.be(), n => G.bind(List<&2, U32>, Unit, take(U32.to_nat(n)), bs => G.pure(Unit, Unit{})))

def natural() -> G(Unit):
  G.bind(U32, Unit, byte(), t => big.bytes(t, 8n))

def integer.large(+t: U32) -> G(Unit):
  match t:
    case 0:
      G.bind(List<&2, U32>, Unit, take(4n), bs => G.pure(Unit, Unit{}))
    case _:
      G.bind(U32, Unit, byte(), sign => big.bytes(1, 0n))

def integer() -> G(Unit):
  G.bind(U32, Unit, byte(), t => integer.large(t))

def terms(n: Nat) -> G(Unit):
  match n:
    case 0n:
      G.pure(Unit, Unit{})
    case 1n+k:
      do G<Unit>:
        i : Unit <- integer()
        j : Unit <- natural()
        terms(k)

def affines(n: Nat) -> G(Unit):
  match n:
    case 0n:
      G.pure(Unit, Unit{})
    case 1n+k:
      do G<Unit>:
        m : U32 <- int()
        c : Unit <- terms(U32.to_nat(m))
        d : Unit <- natural()
        affines(k)

def bound() -> G(Unit):
  G.bind(U32, Unit, int(), n => affines(U32.to_nat(n)))

def method(+m: U32) -> G(Unit):
  match m:
    case 0:
      G.pure(Unit, Unit{})
    case 1:
      G.pure(Unit, Unit{})
    case _:
      G.fail(Unit, "unknown certificate method " ++ U32.show(m))

def ic.cert(+m: U32) -> G(Unit):
  match m:
    case 0:
      G.pure(Unit, Unit{})
    case _:
      do G<Unit>:
        k : U32 <- byte()
        a : Unit <- method(k)
        b0 : Unit <- bound()
        b1 : Unit <- bound()
        bound()

def fields(+entry: String) -> G(Telc):
  do G<Telc>:
    hash : String <- string()
    cert : String <- string()
    nc : U32 <- int()
    cs : List<&2, Count> <- counts(U32.to_nat(nc))
    np : U32 <- int()
    ps : List<&2, Place> <- places(U32.to_nat(np))
    budget : U32 <- int()
    x : Co.V <- expr(fuel())
    m : U32 <- byte()
    c : Unit <- ic.cert(m)
    nl : U32 <- int()
    ls : List<&2, Layout> <- layouts(U32.to_nat(nl))
    return Telc{entry, hash, cert, cs, ps, budget, x, ls}

# What a file holds: an artifact, or why it is none (the magic or the
# version, said as is; anything else is unreadable).
type Read is Data:
  Read{+t: Telc}
  Refused{+msg: String}

def versioned.if(ok: Bool, +v: U32) -> G(Read):
  match ok:
    case True{}:
      G.bind(String, Read, string(), entry => G.bind(Telc, Read, fields(entry), t => G.pure(Read, Read{t})))
    case False{}:
      G.pure(Read, Refused{"this artifact is version " ++ U32.show(v) ++ ", but this telomare reads version "
        ++ U32.show(version()) ++ "; recompile it from source"})

def versioned(+v: U32) -> G(Read):
  versioned.if(U32.is_eq(v, version()), v)

def magic(bs: List<&2, U32>) -> Bool:
  match bs:
    case 84 <> 69 <> 76 <> 67 <> rest:
      True{}
    case _:
      False{}

def magic.ok(ok: Bool) -> G(Read):
  match ok:
    case True{}:
      G.bind(U32, Read, int(), v => versioned(v))
    case False{}:
      G.pure(Read, Refused{"not a telomare artifact (bad magic number)"})

def artifact() -> G(Read):
  G.bind(List<&2, U32>, Read, take(4n), m => magic.ok(magic(m)))

def decoded(r: Got<Read>) -> Result<&2, &2, String, Telc>:
  match r:
    case Got{x, rest}:
      match x:
        case Read{t}:
          Done{t}
        case Refused{msg}:
          Fail{msg}
    case Bad{why}:
      Fail{"not a readable telomare artifact: " ++ why}

# An artifact from its bytes, or what haskell-final says of them.
def decode(bs: List<&2, U32>) -> Result<&2, &2, String, Telc>:
  decoded(artifact()(bs))
