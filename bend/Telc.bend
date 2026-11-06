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
import ./Wire.bend as W
import ./IC.bend as IC

# Compiled programs (master's Telomare.Artifact): a sized program with what a
# run and `--certificate` need, so neither needs the sources again. The bytes
# are master's layout up to its report, so the port numbers its own version,
# 10 (master's is 8): "TELC", the version, the entry module, the sources' hash,
# the static report as rendered, the sizing report (each site's count and
# location, and the budget), then four sections, each its length and its
# bytes: the net's programs as IC.prepare left them (main and, after a Maybe
# byte, the input prologue: each an entry, largest template, template store
# and aborts' origins); master's input prologue, if main has one; the program
# the net runs, haskell-final's IC certificate (the port writes none, and
# skips one it reads) and the capture layouts it runs under; and master's
# program, which a plain run evaluates. A run reads the head and the sections
# it needs, in that order so the net's run reads the fewest bytes (P8 N2: most
# of a run from a .telc went on preparing). Integers are int64 little-endian,
# the store's words 4 bytes little-endian; a string is its UTF-8 length, then
# its UTF-8; a Maybe is byte 0, or 1 and the value; a map is its length, then
# its entries in ascending key order. A Haskell telomare refuses it by its
# version.

# A site's count (None: not sized) and a site's location, by token.
type Count is Data:
  Count{+tok: U32, +n: Maybe<&2, U32>}

type Place is Data:
  Place{+tok: U32, +loc: L.Loc}

# A capture layout, by its code's hash.
type Layout is Data:
  Layout{+digest: String, +shape: Lf.Shape}

# A program and its capture layouts.
type Stored is Data:
  Stored{+expr: Co.V, +layouts: List<&2, Layout>}

type Telc is Data:
  Telc{+entry: String, +hash: String, +cert: String, +counts: List<&2, Count>, +places: List<&2, Place>,
       +budget: U32, +expr: Co.V, +layouts: List<&2, Layout>, +plain: Co.V, +prologue: Maybe<&2, Co.V>}

# The port's version.
def version() -> U32:
  10

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
    case Co.VAbort{o, m}:
      (1 + nodes(m) : U32)
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
def of(+entry: String, srcs: List<&2, Fr.Src>, +counts: List<&2, E.TS>, run: T.C, expr: Co.V, cert: String, +budget: U32, ls: Map<&2, Lf.Shape>, plain: Co.V, prologue: Maybe<&2, Co.V>) -> Telc:
  Telc{entry, sources.hash(srcs), cert, counted(counts), placed(counts, Ct.locs(run, Map.new(&2, L.Loc))), budget, expr, layouts.of(ls), plain, prologue}

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
              W.put.int(tok, 0 <> put.counts(more, rest))
            case Some{k}:
              W.put.int(tok, 1 <> W.put.int(k, put.counts(more, rest)))

def put.places(ps: List<&2, Place>, rest: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      rest
    case Con{p, more}:
      match p:
        case Place{tok, loc}:
          W.put.int(tok, W.put.loc(loc, put.places(more, rest)))

def put.layouts(ls: List<&2, Layout>, rest: List<&2, U32>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      rest
    case Con{l, more}:
      match l:
        case Layout{digest, shape}:
          W.put.string(digest, put.shape(shape, put.layouts(more, rest)))

def count(-A: Data, xs: List<&2, A>) -> U32:
  U32.from_nat(List.length(&2, A, xs))

# The sizing report: the counts, the places and the budget.
def put.report(+cs: List<&2, Count>, +ps: List<&2, Place>, +budget: U32, rest: List<&2, U32>) -> List<&2, U32>:
  W.put.int(count(Count, cs), put.counts(cs, W.put.int(count(Place, ps), put.places(ps, W.put.int(budget, rest)))))

# The program, no IC certificate, and the layouts.
def put.program(expr: Co.V, +ls: List<&2, Layout>, rest: List<&2, U32>) -> List<&2, U32>:
  W.put.expr(expr, 0 <> W.put.int(count(Layout, ls), put.layouts(ls, rest)))

def put.prologue(g: Maybe<&2, Co.V>) -> List<&2, U32>:
  match g:
    case None{}:
      [0]
    case Some{v}:
      1 <> W.put.expr(v, [])

# The net's programs, prepared: what IC.prepare makes of the program and its
# prologue, so a run spends nothing on collecting and compiling them. The
# templates' bodies stay out: IC.BodiesIn has a run collect them from the
# program's bytes if a result holds a closure.
def put.u32(+n: U32, rest: List<&2, U32>) -> List<&2, U32>:
  U32.and(n, 255) <> U32.and(U32.shrn(n, 8n), 255) <> U32.and(U32.shrn(n, 16n), 255) <> U32.shrn(n, 24n) <> rest

def put.words(ws: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      rest
    case Con{w, more}:
      put.u32(w, put.words(more, rest))

def put.code(c: IC.Code, rest: List<&2, U32>) -> List<&2, U32>:
  match c:
    case IC.CdZero{}:
      0 <> rest
    case IC.CdPair{a, b}:
      1 <> put.code(a, put.code(b, rest))
    case IC.CdEnv{}:
      2 <> rest
    case IC.CdSetEnv{x}:
      3 <> put.code(x, rest)
    case IC.CdGate{}:
      4 <> rest
    case IC.CdLeft{x}:
      5 <> put.code(x, rest)
    case IC.CdRight{x}:
      6 <> put.code(x, rest)
    case IC.CdAbort{o, m}:
      7 <> W.put.int(o, put.code(m, rest))
    case IC.CdRef{tid, fi}:
      8 <> W.put.int(tid, W.put.int(fi, rest))
    case IC.CdIte{s, l, r, el, er, cap}:
      9 <> put.code(s, put.code(l, put.code(r, put.code(el, put.code(er, put.code(cap, rest))))))
    case IC.CdConst{at}:
      10 <> W.put.int(at, rest)

def put.origins(kvs: List<&2, Sigma<&2, &2, String, _ => L.Origin>>, rest: List<&2, U32>) -> List<&2, U32>:
  match kvs:
    case Nil{}:
      rest
    case Con{kv, more}:
      match kv:
        case (k, o):
          W.put.string(k, W.put.origin(o, put.origins(more, rest)))

def put.prog(p: IC.Prog, rest: List<&2, U32>) -> List<&2, U32>:
  match p:
    case IC.Prog{entry, bodies, +words, +maxk, +os}:
      put.code(entry, W.put.int(maxk, W.put.int(count(U32, words), put.words(words,
        W.put.int(U32.from_nat(Map.size(&2, L.Origin, os)), put.origins(Map.to_list(&2, L.Origin, os), rest))))))

def put.prog.maybe(g: Maybe<&2, IC.Prog>) -> List<&2, U32>:
  match g:
    case None{}:
      [0]
    case Some{p}:
      1 <> put.prog(p, [])

def prologue.prepared(g: Maybe<&2, Co.V>, +ls: Map<&2, Lf.Shape>) -> Maybe<&2, IC.Prog>:
  match g:
    case None{}:
      None{}
    case Some{+v}:
      Some{IC.prepare(v, ls)}

def put.ready(+expr: Co.V, +prologue: Maybe<&2, Co.V>, ls: List<&2, Layout>, rest: List<&2, U32>) -> List<&2, U32>:
  +m = shapes(ls, Map.new(&2, Lf.Shape))
  put.prog(IC.prepare(expr, m), List.append(&2, U32, put.prog.maybe(prologue.prepared(prologue, m)), rest))

# A section: its length, then its bytes.
def section(+bs: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  W.put.int(count(U32, bs), List.append(&2, U32, bs, rest))

def encode(t: Telc) -> List<&2, U32>:
  match t:
    case Telc{entry, hash, cert, counts, places, budget, +expr, +layouts, plain, +prologue}:
      84 <> 69 <> 76 <> 67 <> W.put.int(version(),
        W.put.string(entry, W.put.string(hash, W.put.string(cert,
          put.report(counts, places, budget,
            section(put.ready(expr, prologue, layouts, []),
              section(put.prologue(prologue),
                section(put.program(expr, layouts, []),
                  section(W.put.expr(plain, []), [])))))))))

# Reading
# -------

def G(-A: Data) -> Type:
  W.G(A)

def G.pure(-A: Data, x: A) -> G(A):
  W.G.pure(A, x)

def G.fail(-A: Data, why: String) -> G(A):
  W.G.fail(A, why)

def G.bind(-A: Data, -B: Data, m: G(A), f: A -> G(B)) -> G(B):
  W.G.bind(A, B, m, f)

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
      G.bind(U32, Lf.Shape, W.byte(), t => shape.node(t, shape(f), shape(f)))

def counts(n: Nat) -> G(List<&2, Count>):
  match n:
    case 0n:
      G.pure(List<&2, Count>, [])
    case 1n+k:
      do G<List<&2, Count>>:
        tok : U32 <- W.int()
        m : U32 <- W.byte()
        c : Maybe<&2, U32> <- W.maybe.int(m)
        rest : List<&2, Count> <- counts(k)
        return Count{tok, c} <> rest

def places(n: Nat) -> G(List<&2, Place>):
  match n:
    case 0n:
      G.pure(List<&2, Place>, [])
    case 1n+k:
      do G<List<&2, Place>>:
        tok : U32 <- W.int()
        l : L.Loc <- W.loc(W.fuel())
        rest : List<&2, Place> <- places(k)
        return Place{tok, l} <> rest

def layouts(n: Nat) -> G(List<&2, Layout>):
  match n:
    case 0n:
      G.pure(List<&2, Layout>, [])
    case 1n+k:
      do G<List<&2, Layout>>:
        digest : String <- W.string()
        s : Lf.Shape <- shape(W.fuel())
        rest : List<&2, Layout> <- layouts(k)
        return Layout{digest, s} <> rest

# haskell-final's IC certificate, skipped: its method, then three bounds,
# each a list of affine forms (a map of Data.Binary Integers to Naturals,
# and a Natural).
def big.bytes(+t: U32, +small: Nat) -> G(Unit):
  match t:
    case 0:
      G.bind(List<&2, U32>, Unit, W.take(small), bs => G.pure(Unit, Unit{}))
    case _:
      G.bind(U32, Unit, W.int.be(), n => G.bind(List<&2, U32>, Unit, W.take(U32.to_nat(n)), bs => G.pure(Unit, Unit{})))

def natural() -> G(Unit):
  G.bind(U32, Unit, W.byte(), t => big.bytes(t, 8n))

def integer.large(+t: U32) -> G(Unit):
  match t:
    case 0:
      G.bind(List<&2, U32>, Unit, W.take(4n), bs => G.pure(Unit, Unit{}))
    case _:
      G.bind(U32, Unit, W.byte(), sign => big.bytes(1, 0n))

def integer() -> G(Unit):
  G.bind(U32, Unit, W.byte(), t => integer.large(t))

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
        m : U32 <- W.int()
        c : Unit <- terms(U32.to_nat(m))
        d : Unit <- natural()
        affines(k)

def bound() -> G(Unit):
  G.bind(U32, Unit, W.int(), n => affines(U32.to_nat(n)))

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
        k : U32 <- W.byte()
        a : Unit <- method(k)
        b0 : Unit <- bound()
        b1 : Unit <- bound()
        bound()

# The prepared programs
# ---------------------

type Prepared is Data:
  Prepared{+main: IC.Prog, +prologue: Maybe<&2, IC.Prog>}

def code.node(+t: U32, a: G(IC.Code), b: G(IC.Code), c: G(IC.Code), d: G(IC.Code), e: G(IC.Code), f: G(IC.Code)) -> G(IC.Code):
  match t:
    case 0:
      G.pure(IC.Code, IC.CdZero{})
    case 1:
      do G<IC.Code>:
        x : IC.Code <- a
        y : IC.Code <- b
        return IC.CdPair{x, y}
    case 2:
      G.pure(IC.Code, IC.CdEnv{})
    case 3:
      G.bind(IC.Code, IC.Code, a, x => G.pure(IC.Code, IC.CdSetEnv{x}))
    case 4:
      G.pure(IC.Code, IC.CdGate{})
    case 5:
      G.bind(IC.Code, IC.Code, a, x => G.pure(IC.Code, IC.CdLeft{x}))
    case 6:
      G.bind(IC.Code, IC.Code, a, x => G.pure(IC.Code, IC.CdRight{x}))
    case 7:
      do G<IC.Code>:
        o : U32 <- W.int()
        m : IC.Code <- a
        return IC.CdAbort{o, m}
    case 8:
      do G<IC.Code>:
        tid : U32 <- W.int()
        fi : U32 <- W.int()
        return IC.CdRef{tid, fi}
    case 9:
      do G<IC.Code>:
        s : IC.Code <- a
        l : IC.Code <- b
        r : IC.Code <- c
        el : IC.Code <- d
        er : IC.Code <- e
        cap : IC.Code <- f
        return IC.CdIte{s, l, r, el, er, cap}
    case 10:
      G.bind(U32, IC.Code, W.int(), at => G.pure(IC.Code, IC.CdConst{at}))
    case _:
      G.fail(IC.Code, "unknown code tag " ++ U32.show(t))

def code(+fuel: Nat) -> G(IC.Code):
  match fuel:
    case 0n:
      G.fail(IC.Code, "nesting too deep")
    case 1n+f:
      G.bind(U32, IC.Code, W.byte(), t => code.node(t, code(f), code(f), code(f), code(f), code(f), code(f)))

# A run's words, without a closure per byte: they are most of the file.
def words.of(n: Nat, bs: List<&2, U32>, acc: List<&2, U32>) -> W.Got<List<&2, U32>>:
  match n:
    case 0n:
      W.Got{List.reverse(&2, U32, acc), bs}
    case 1n+k:
      match bs:
        case b0 <> b1 <> b2 <> b3 <> rest:
          words.of(k, rest, (b0 + U32.shln(b1, 8n) + U32.shln(b2, 16n) + U32.shln(b3, 24n) : U32) <> acc)
        case _:
          W.Bad{"not enough bytes"}

def words(n: Nat) -> G(List<&2, U32>):
  bs => words.of(n, bs, [])

def origins(n: Nat, acc: Map<&2, L.Origin>) -> G(Map<&2, L.Origin>):
  match n:
    case 0n:
      G.pure(Map<&2, L.Origin>, acc)
    case 1n+k:
      do G<Map<&2, L.Origin>>:
        +key : String <- W.string()
        o : L.Origin <- W.origin(W.fuel())
        origins(k, Map.set(&2, L.Origin, acc, key, o))

def prog() -> G(IC.Prog):
  do G<IC.Prog>:
    e : IC.Code <- code(W.fuel())
    maxk : U32 <- W.int()
    n : U32 <- W.int()
    ws : List<&2, U32> <- words(U32.to_nat(n))
    no : U32 <- W.int()
    os : Map<&2, L.Origin> <- origins(U32.to_nat(no), Map.new(&2, L.Origin))
    return IC.Prog{e, IC.BodiesAt{Map.new(&2, Co.V)}, ws, maxk, os}

def prog.if(none: Bool) -> G(Maybe<&2, IC.Prog>):
  match none:
    case True{}:
      G.pure(Maybe<&2, IC.Prog>, None{})
    case False{}:
      G.bind(IC.Prog, Maybe<&2, IC.Prog>, prog(), p => G.pure(Maybe<&2, IC.Prog>, Some{p}))

def prologue.if(none: Bool) -> G(Maybe<&2, Co.V>):
  match none:
    case True{}:
      G.pure(Maybe<&2, Co.V>, None{})
    case False{}:
      G.bind(Co.V, Maybe<&2, Co.V>, W.expr(W.fuel()), v => G.pure(Maybe<&2, Co.V>, Some{v}))

# What every use of a file reads: all but the sections, which are the bytes
# after the report. A run goes on to the ones it needs.
type Head is Data:
  Head{+entry: String, +hash: String, +cert: String, +counts: List<&2, Count>, +places: List<&2, Place>,
       +budget: U32, +body: List<&2, U32>}

def fields(+entry: String) -> G(Head):
  do G<Head>:
    hash : String <- W.string()
    cert : String <- W.string()
    nc : U32 <- W.int()
    cs : List<&2, Count> <- counts(U32.to_nat(nc))
    np : U32 <- W.int()
    ps : List<&2, Place> <- places(U32.to_nat(np))
    budget : U32 <- W.int()
    body : List<&2, U32> <- W.here()
    return Head{entry, hash, cert, cs, ps, budget, body}

# What a file holds: an artifact, or why it is none (the magic or the
# version, said as is; anything else is unreadable).
type Read is Data:
  Read{+h: Head}
  Refused{+msg: String}

def versioned.if(ok: Bool, +v: U32) -> G(Read):
  match ok:
    case True{}:
      G.bind(String, Read, W.string(), entry => G.bind(Head, Read, fields(entry), h => G.pure(Read, Read{h})))
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
      G.bind(U32, Read, W.int(), v => versioned(v))
    case False{}:
      G.pure(Read, Refused{"not a telomare artifact (bad magic number)"})

def artifact() -> G(Read):
  G.bind(List<&2, U32>, Read, W.take(4n), m => magic.ok(magic(m)))

def unreadable(+why: String) -> String:
  "not a readable telomare artifact: " ++ why

def loaded(r: W.Got<Read>) -> Result<&2, &2, String, Head>:
  match r:
    case W.Got{x, rest}:
      match x:
        case Read{h}:
          Done{h}
        case Refused{msg}:
          Fail{msg}
    case W.Bad{why}:
      Fail{unreadable(why)}

# An artifact's head from its bytes, or what haskell-final says of them.
def load(bs: List<&2, U32>) -> Result<&2, &2, String, Head>:
  loaded(artifact()(bs))

def read.section(-A: Data, r: W.Got<A>) -> Result<&2, &2, String, A>:
  match r:
    case W.Got{x, rest}:
      Done{x}
    case W.Bad{why}:
      Fail{unreadable(why)}

# Past a section, its length read.
def passed() -> G(Unit):
  G.bind(U32, Unit, W.int(), n => W.skip(U32.to_nat(n)))

# What a run on the net reads: the programs as prepared, each able to find
# its bytes if a result holds a closure.
def prog.at(p: IC.Prog, +bs: List<&2, U32>) -> IC.Prog:
  match p:
    case IC.Prog{entry, bodies, words, maxk, os}:
      IC.Prog{entry, IC.BodiesIn{bs}, words, maxk, os}

def prog.maybe.at(g: Maybe<&2, IC.Prog>, +bs: List<&2, U32>) -> Maybe<&2, IC.Prog>:
  match g:
    case None{}:
      None{}
    case Some{p}:
      Some{prog.at(p, bs)}

def ready.fields() -> G(Prepared):
  do G<Prepared>:
    nr : U32 <- W.int()
    m : IC.Prog <- prog()
    b : U32 <- W.byte()
    g : Maybe<&2, IC.Prog> <- prog.if(U32.is_zero(b))
    ng : U32 <- W.int()
    flag : U32 <- W.byte()
    pro : List<&2, U32> <- W.here()
    u : Unit <- W.skip(U32.to_nat((ng - 1 : U32)))
    nx : U32 <- W.int()
    src : List<&2, U32> <- W.here()
    return Prepared{prog.at(m, src), prog.maybe.at(g, pro)}

def ready.of(h: Head) -> Result<&2, &2, String, Prepared>:
  match h:
    case Head{entry, hash, cert, counts, places, budget, body}:
      read.section(Prepared, ready.fields()(body))

# What a plain run reads: master's program and its input prologue.
type Plain is Data:
  Plain{+plain: Co.V, +prologue: Maybe<&2, Co.V>}

def plain.fields() -> G(Plain):
  do G<Plain>:
    a : Unit <- passed()
    ng : U32 <- W.int()
    b : U32 <- W.byte()
    g : Maybe<&2, Co.V> <- prologue.if(U32.is_zero(b))
    c : Unit <- passed()
    np : U32 <- W.int()
    p : Co.V <- W.expr(W.fuel())
    return Plain{p, g}

def plain.of(h: Head) -> Result<&2, &2, String, Plain>:
  match h:
    case Head{entry, hash, cert, counts, places, budget, body}:
      read.section(Plain, plain.fields()(body))

# The whole artifact, as the tests compare it.
type Rest is Data:
  Rest{+expr: Co.V, +layouts: List<&2, Layout>, +plain: Co.V, +prologue: Maybe<&2, Co.V>}

def rest.fields() -> G(Rest):
  do G<Rest>:
    a : Unit <- passed()
    ng : U32 <- W.int()
    b : U32 <- W.byte()
    g : Maybe<&2, Co.V> <- prologue.if(U32.is_zero(b))
    nx : U32 <- W.int()
    x : Co.V <- W.expr(W.fuel())
    m : U32 <- W.byte()
    c : Unit <- ic.cert(m)
    nl : U32 <- W.int()
    ls : List<&2, Layout> <- layouts(U32.to_nat(nl))
    np : U32 <- W.int()
    p : Co.V <- W.expr(W.fuel())
    return Rest{x, ls, p, g}

def whole.of(+entry: String, +hash: String, +cert: String, +cs: List<&2, Count>, +ps: List<&2, Place>, +budget: U32, r: Result<&2, &2, String, Rest>) -> Result<&2, &2, String, Telc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      match x:
        case Rest{e, ls, p, g}:
          Done{Telc{entry, hash, cert, cs, ps, budget, e, ls, p, g}}

def whole(r: Result<&2, &2, String, Head>) -> Result<&2, &2, String, Telc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{h}:
      match h:
        case Head{entry, hash, cert, cs, ps, budget, body}:
          whole.of(entry, hash, cert, cs, ps, budget, read.section(Rest, rest.fields()(body)))

# The whole artifact from its bytes, or what haskell-final says of them.
def decode(bs: List<&2, U32>) -> Result<&2, &2, String, Telc>:
  whole(load(bs))
