import Base
import ./Loc.bend as L
import ./Term.bend as T
import ./Resolve.bend as Rs

# Closure conversion, Term2 to Term3 (haskell-final's Resolve.splitExpr and
# IR.Builder). An open lambda becomes (Defer body, captured variables), a
# closed one (Defer body, 0), an application SetEnv (SetEnv (twiddle,
# (argument, function))), and each recursion placeholder a closure over a
# fresh token. Function indices and tokens come from one counter pair,
# allocated in the builder's order: a pair builds left then right, an
# application its twiddle, then its argument, then its function, and a
# lambda its body before its own index. Sizing reports tokens by that
# order, so it must be exact.

# Pass 1: each open lambda's captured variables
# ----------------------------------------------

type F is Data:
  FZero{+loc: L.Loc}
  FPair{+loc: L.Loc, +a: F, +b: F}
  FIdx{+loc: L.Loc, +i: Nat}
  FApp{+loc: L.Loc, +f: F, +x: F}
  FOpen{+loc: L.Loc, +outer: List<&2, Nat>, +body: F}
  FClosed{+loc: L.Loc, +body: F}
  FCheck{+loc: L.Loc, +tc: F, +c: F}
  FIte{+loc: L.Loc, +i: F, +t: F, +e: F}
  FLeft{+loc: L.Loc, +x: F}
  FRight{+loc: L.Loc, +x: F}
  FTrace{+loc: L.Loc, +x: F}
  FChurch{+loc: L.Loc, +n: U32}
  FRec{+loc: L.Loc, +t: F, +r: F, +b: F}
  FRep{+loc: L.Loc}

type FR is Data:
  FR{+t: F, +fv: List<&2, Nat>}

type BS is Data:
  BS{+fi: U32, +tok: U32}

# The renaming of de Bruijn indices under an open lambda: 0 stays the
# argument, n its captured variable's position.
type Ren is Data:
  RTop{}
  RId{}
  ROuter{+outer: List<&2, Nat>}

def insert.pick(c: Cmp, +x: Nat, y: Nat, rest: List<&2, Nat>, later: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case LT{}:
      x <> y <> rest
    case EQ{}:
      y <> rest
    case GT{}:
      y <> later

# x into an ascending list of distinct indices.
def insert(ys: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      [x]
    case Con{+y, +rest}:
      insert.pick(Nat.cmp(x, y), x, y, rest, insert(rest, x))

# The union of two ascending lists of distinct indices.
def union(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{x, rest}:
      union(rest, insert(ys, x))

# The captured variables of an open lambda with body frees `fs`: every
# free index but the argument, one level out (Set.map (subtract 1) .
# Set.filter (>= 1)).
def outer(fs: List<&2, Nat>) -> List<&2, Nat>:
  match fs:
    case Nil{}:
      []
    case Con{i, rest}:
      match i:
        case 0n:
          outer(rest)
        case 1n+k:
          k <> outer(rest)

def fr.t(r: FR) -> F:
  match r:
    case FR{t, fv}:
      t

def fr.frees(r: FR) -> List<&2, Nat>:
  match r:
    case FR{t, fv}:
      fv

def fr2(~k: L.Loc -> F -> F -> F, +a: L.Loc, +x: FR, +y: FR) -> FR:
  FR{k(a, fr.t(x), fr.t(y)), union(fr.frees(x), fr.frees(y))}

def fr3(~k: L.Loc -> F -> F -> F -> F, +a: L.Loc, +x: FR, +y: FR, +z: FR) -> FR:
  FR{k(a, fr.t(x), fr.t(y), fr.t(z)), union(fr.frees(x), union(fr.frees(y), fr.frees(z)))}

def fr1(~k: L.Loc -> F -> F, +a: L.Loc, +x: FR) -> FR:
  FR{k(a, fr.t(x)), fr.frees(x)}

def mk.pair(a: L.Loc, x: F, y: F) -> F:
  FPair{a, x, y}

def mk.app(a: L.Loc, x: F, y: F) -> F:
  FApp{a, x, y}

def mk.check(a: L.Loc, x: F, y: F) -> F:
  FCheck{a, x, y}

def mk.ite(a: L.Loc, x: F, y: F, z: F) -> F:
  FIte{a, x, y, z}

def mk.rec(a: L.Loc, x: F, y: F, z: F) -> F:
  FRec{a, x, y, z}

def mk.left(a: L.Loc, x: F) -> F:
  FLeft{a, x}

def mk.right(a: L.Loc, x: F) -> F:
  FRight{a, x}

def mk.trace(a: L.Loc, x: F) -> F:
  FTrace{a, x}

def open.fr(+a: L.Loc, +b: FR) -> FR:
  +o = outer(fr.frees(b))
  FR{FOpen{a, o, fr.t(b)}, o}

def frees(+fuel: Nat, t: T.T) -> FR:
  match fuel:
    case 0n:
      FR{FZero{L.Unknown{}}, []}
    case 1n+f:
      match t:
        case T.TZero{a}:
          FR{FZero{a}, []}
        case T.TPair{a, x, y}:
          fr2(~mk.pair, a, frees(f, x), frees(f, y))
        case T.TIdx{a, +i}:
          FR{FIdx{a, i}, [i]}
        case T.TApp{a, x, y}:
          fr2(~mk.app, a, frees(f, x), frees(f, y))
        case T.TLam{a, k, name, body}:
          match k:
            case T.Closed{}:
              FR{FClosed{a, fr.t(frees(f, body))}, []}
            case _:
              open.fr(a, frees(f, body))
        case T.TCheck{a, x, y}:
          fr2(~mk.check, a, frees(f, x), frees(f, y))
        case T.TIte{a, x, y, z}:
          fr3(~mk.ite, a, frees(f, x), frees(f, y), frees(f, z))
        case T.TLeft{a, x}:
          fr1(~mk.left, a, frees(f, x))
        case T.TRight{a, x}:
          fr1(~mk.right, a, frees(f, x))
        case T.TTrace{a, x}:
          fr1(~mk.trace, a, frees(f, x))
        case T.TChurch{a, n}:
          FR{FChurch{a, n}, []}
        case T.TRec{a, x, y, z}:
          fr3(~mk.rec, a, frees(f, x), frees(f, y), frees(f, z))
        case T.TRep{a}:
          FR{FRep{a}, []}
        case _:
          FR{FZero{L.Unknown{}}, []}

# Pass 2: the builder
# -------------------

def B(-A: Data) -> Type:
  BS -> A & BS

def B.pure(-A: Data, x: A) -> B(A):
  s => (x, s)

def B.run(-A: Data, -X: Data, f: A -> B(X), r: A & BS) -> X & BS:
  (a, s) = r
  f(a)(s)

def B.bind(-A: Data, -X: Data, m: B(A), f: A -> B(X)) -> B(X):
  s => B.run(A, X, f, m(s))

def next.fi.go(s: BS) -> U32 & BS:
  match s:
    case BS{+fi, tok}:
      (fi, BS{(fi + 1 : U32), tok})

# The next function index (deferS).
def next.fi() -> B(U32):
  s => next.fi.go(s)

def next.tok.go(s: BS) -> U32 & BS:
  match s:
    case BS{fi, +tok}:
      (tok, BS{fi, (tok + 1 : U32)})

# The next recursion token.
def next.tok() -> B(U32):
  s => next.tok.go(s)

def gs() -> L.Loc:
  L.Gen{"StuckBase Cofree instance"}

def gb() -> L.Loc:
  L.Gen{"BasicBase Cofree instance"}

def rights(n: Nat, t: T.C) -> T.C:
  match n:
    case 0n:
      t
    case 1n+k:
      T.CRight{gs(), rights(k, t)}

# Variable n: Left (Right^n Env) (varB).
def var.b(n: Nat) -> T.C:
  T.CLeft{gs(), rights(n, T.CEnv{gs()})}

# The twiddle's body: (env's function, (argument, captured)) from
# (argument, (function, captured)).
def twiddle.body() -> T.C:
  T.CPair{gs(), T.CLeft{gs(), T.CRight{gs(), T.CEnv{gs()}}},
    T.CPair{gs(), T.CLeft{gs(), T.CEnv{gs()}}, T.CRight{gs(), T.CRight{gs(), T.CEnv{gs()}}}}}

# SetEnv (SetEnv (Defer twiddle, (i, c))) (appS), the twiddle's index given.
def app.of(fi: U32, +i: T.C, c: T.C) -> T.C:
  T.CSetEnv{gs(), T.CSetEnv{gs(), T.CPair{gs(), T.CDefer{gs(), fi, twiddle.body()}, T.CPair{T.C.loc(i), i, c}}}}

def position.pick(hit: Bool, i: Nat, later: Nat) -> Nat:
  match hit:
    case True{}:
      i
    case False{}:
      later

def position(xs: List<&2, Nat>, +n: Nat, +i: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      position.pick(Nat.is_eq(x, n), i, position(rest, n, 1n+i))

def ren.apply(r: Ren, +n: Nat) -> Nat:
  match r:
    case RTop{}:
      n
    case RId{}:
      n
    case ROuter{outer}:
      match n:
        case 0n:
          0n
        case 1n+k:
          position(outer, k, 1n)

# The captured variables' values, as renamed outside the lambda.
def capture(outer: List<&2, Nat>, +ren: Ren) -> T.C:
  match outer:
    case Nil{}:
      T.CZero{gb()}
    case Con{o, rest}:
      T.CPair{gs(), var.b(ren.apply(ren, o)), capture(rest, ren)}

# The body of $n: f applied n times to x (i2CB), its twiddles allocated
# outermost first.
def church.body(n: Nat) -> B(T.C):
  match n:
    case 0n:
      B.pure(T.C, var.b(0n))
    case 1n+k:
      do B<T.C>:
        fi : U32 <- next.fi()
        i : T.C <- church.body(k)
        return app.of(fi, i, var.b(1n))

# \f x -> f (f ... x), closed ($n).
def church(+a: L.Loc, n: Nat) -> B(T.C):
  do B<T.C>:
    body : T.C <- church.body(n)
    fi1 : U32 <- next.fi()
    fi2 : U32 <- next.fi()
    return T.CPair{a, T.CDefer{gs(), fi2, T.CPair{gs(), T.CDefer{gs(), fi1, body}, T.CEnv{gs()}}}, T.CZero{gb()}}

# (Defer main, (tWrap, (r, (b, 0)))) for {t, r, b}
# (unsizedRecursionWrapper); the recursion's closures and the test's
# wrapper, the indices in the builder's order.
def rec.shell(+a: L.Loc, fi1: U32, fi2: U32, fiInner: U32, fiMain: U32, fi3: U32, fiTest: U32,
              +t: T.C, +r: T.C, +b: T.C) -> T.C:
  +inner = {app.of(fi1, var.b(0n), app.of(fi2, T.CRight{gs(), T.CRight{gs(), T.CEnv{gs()}}}, var.b(1n))) : T.C}
  +main = {T.CDefer{gs(), fiMain, T.CPair{gs(), T.CDefer{gs(), fiInner, inner}, T.CEnv{gs()}}} : T.C}
  +twrap = {T.CPair{gs(), T.CDefer{gs(), fiTest, app.of(fi3, var.b(0n), var.b(1n))}, T.CPair{T.C.loc(t), t, T.CZero{gb()}}} : T.C}
  T.CPair{a, main, T.CPair{gs(), twrap, T.CPair{T.C.loc(r), r, T.CPair{T.C.loc(b), b, T.CZero{gb()}}}}}

# if i then t else e, both branches built (iteB_).
def ite.of(a: L.Loc, i: T.C, t: T.C, +e: T.C) -> T.C:
  T.CSetEnv{a, T.CPair{gs(), T.CSetEnv{gs(), T.CPair{gs(), T.CGate{gs()}, i}}, T.CPair{T.C.loc(e), e, t}}}

def build(+fuel: Nat, +ren: Ren, t: F) -> B(T.C):
  match fuel:
    case 0n:
      B.pure(T.C, T.CZero{L.Unknown{}})
    case 1n+f:
      match t:
        case FZero{a}:
          B.pure(T.C, T.CZero{a})
        case FPair{a, x, y}:
          do B<T.C>:
            x2 : T.C <- build(f, ren, x)
            y2 : T.C <- build(f, ren, y)
            return T.CPair{a, x2, y2}
        case FIdx{a, i}:
          B.pure(T.C, T.C.retag(a, var.b(ren.apply(ren, i))))
        case FApp{a, c, i}:
          do B<T.C>:
            fi : U32 <- next.fi()
            i2 : T.C <- build(f, ren, i)
            c2 : T.C <- build(f, ren, c)
            return T.C.retag(a, app.of(fi, i2, c2))
        case FOpen{a, +outer, body}:
          do B<T.C>:
            b2 : T.C <- build(f, ROuter{outer}, body)
            fi : U32 <- next.fi()
            return T.CPair{a, T.CDefer{gs(), fi, b2}, capture(outer, ren)}
        case FClosed{a, body}:
          do B<T.C>:
            b2 : T.C <- build(f, RId{}, body)
            fi : U32 <- next.fi()
            return T.CPair{a, T.CDefer{gs(), fi, b2}, T.CZero{gb()}}
        case FCheck{+a, x, y}:
          do B<T.C>:
            x2 : T.C <- build(f, ren, x)
            y2 : T.C <- build(f, ren, y)
            return T.CCheck{a, a, x2, y2}
        case FIte{a, x, y, z}:
          do B<T.C>:
            x2 : T.C <- build(f, ren, x)
            y2 : T.C <- build(f, ren, y)
            z2 : T.C <- build(f, ren, z)
            return ite.of(a, x2, y2, z2)
        case FLeft{a, x}:
          do B<T.C>:
            x2 : T.C <- build(f, ren, x)
            return T.CLeft{a, x2}
        case FRight{a, x}:
          do B<T.C>:
            x2 : T.C <- build(f, ren, x)
            return T.CRight{a, x2}
        case FTrace{a, x}:
          do B<T.C>:
            x2 : T.C <- build(f, ren, x)
            return T.C.retag(a, x2)
        case FChurch{a, n}:
          church(a, U32.to_nat(n))
        case FRec{a, x, y, z}:
          do B<T.C>:
            fi1 : U32 <- next.fi()
            fi2 : U32 <- next.fi()
            fiInner : U32 <- next.fi()
            fiMain : U32 <- next.fi()
            fi3 : U32 <- next.fi()
            fiTest : U32 <- next.fi()
            x2 : T.C <- build(f, ren, x)
            y2 : T.C <- build(f, ren, y)
            z2 : T.C <- build(f, ren, z)
            return rec.shell(a, fi1, fi2, fiInner, fiMain, fi3, fiTest, x2, y2, z2)
        case FRep{+a}:
          do B<T.C>:
            tok : U32 <- next.tok()
            fi : U32 <- next.fi()
            return T.CPair{a, T.CDefer{gs(), fi, T.CUnsized{a, tok}}, T.CZero{gb()}}

def fuel() -> Nat:
  U32.to_nat(4294967295)

def first(r: T.C & BS) -> T.C:
  (t, s) = r
  t

# splitExpr
def split(t: T.T) -> T.C:
  first(build(fuel(), RTop{}, fr.t(frees(fuel(), t)))(BS{0, 0}))
