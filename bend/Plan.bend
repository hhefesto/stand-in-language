import Base
import ./Core.bend as Co
import ./Loc.bend as L

# Where a sized main's refinement checks go (master's Size.checkPlan,
# analyzeChecks, checkVerdicts and inputPrologue, with Machine.exactSuperStepM
# and mergeExact). One exact run of the sized main over a symbolic input
# records every run of a check that may fail, with the path that reached it
# and its result, and main's symbolic result. Then:
#
# - a check missing from the record can never fail: it is erased;
# - a check whose every run reads only the input becomes a decision tree: its
#   result's own decisions down to where it fails, then main's result split on
#   its superpositions. Where the run surely aborts and the input is surely a
#   pair (so not the input-less first call), the failure is decided before
#   main, in the input prologue. Where it is abort-free, the failure is never
#   seen. Anything else keeps the check in main, entirely;
# - any other check stays in main.
#
# Superpositions are exact: VlSuper{Some{n}, a, b} is a when input position n
# is 0 and b when it is a pair, and VlSuper{None{}, a, b} an unknown choice. A
# branch remembers the path that led to it, and a superposition or input gate
# it uses is decided by that path when the path knows its position. So two
# uses of one superposed value pick matching branches.
#
# An input position is its path from the root, 'L' and 'R', as Expr.bend has
# it. Master numbers them 2n+1 and 2n+2, so numeric order is shortest first,
# then 'L' before 'R' (pos.le).
#
# Master tells shared values by pointer (exactEq): branches share what they did
# not change, so the same node is recognized without a walk. Here every value
# carries a 64-bit digest of its structure instead, built as it is, and two
# values with the same digest are the same value.

type H is Data:
  PH{+x: U32, +y: U32}

# One step of the digest's two lanes.
def lane(+h: U32, +v: U32, +k: U32) -> U32:
  +m = (U32.xor(h, (v * 2654435761 : U32)) * k : U32)
  U32.xor(m, U32.shrn(m, 15n))

def mix(a: H, +v: U32) -> H:
  match a:
    case PH{+x, +y}:
      PH{lane(x, v, 2246822519), lane(y, v, 3266489917)}

def mix.h(a: H, b: H) -> H:
  match b:
    case PH{+x, +y}:
      mix(mix(a, x), y)

def hash.str(s: String, h: H) -> H:
  match s:
    case SNil{}:
      h
    case SCon{c, rest}:
      match c:
        case Chr{+k}:
          hash.str(rest, mix(h, k))

# The program, each closure's body digested once.
type Cd is Data:
  GZero{}
  GPair{+a: Cd, +b: Cd}
  GEnv{}
  GSet{+x: Cd}
  GDefer{+h: H, +fi: U32, +x: Cd}
  GGate{}
  GLeft{+x: Cd}
  GRight{+x: Cd}
  GAbort{+o: L.Origin, +m: Cd}

type PCH is Data:
  PCH{+h: H, +c: Cd}

def ch.pair(a: PCH, b: PCH) -> PCH:
  match a:
    case PCH{ha, ca}:
      match b:
        case PCH{hb, cb}:
          PCH{mix.h(mix(ha, 2), hb), GPair{ca, cb}}

def ch.set(a: PCH) -> PCH:
  match a:
    case PCH{h, c}:
      PCH{mix(h, 3), GSet{c}}

def ch.left(a: PCH) -> PCH:
  match a:
    case PCH{h, c}:
      PCH{mix(h, 4), GLeft{c}}

def ch.right(a: PCH) -> PCH:
  match a:
    case PCH{h, c}:
      PCH{mix(h, 5), GRight{c}}

def ch.defer(+fi: U32, a: PCH) -> PCH:
  match a:
    case PCH{+h, c}:
      +d = mix(mix(h, 6), fi)
      PCH{d, GDefer{d, fi, c}}

def ch.abort(+o: L.Origin, a: PCH) -> PCH:
  match a:
    case PCH{h, c}:
      PCH{hash.str(L.origin.key(o), mix(h, 7)), GAbort{o, c}}

def code(v: Co.V) -> PCH:
  match v:
    case Co.VZero{}:
      PCH{PH{11, 13}, GZero{}}
    case Co.VPair{a, b}:
      ch.pair(code(a), code(b))
    case Co.VEnv{}:
      PCH{PH{17, 19}, GEnv{}}
    case Co.VSetEnv{x}:
      ch.set(code(x))
    case Co.VDefer{+fi, x}:
      ch.defer(fi, code(x))
    case Co.VGate{}:
      PCH{PH{23, 29}, GGate{}}
    case Co.VLeft{x}:
      ch.left(code(x))
    case Co.VRight{x}:
      ch.right(code(x))
    case Co.VAbort{+o, m}:
      ch.abort(o, code(m))

# A value of the run.
type A is Data:
  VlZero{}
  VlPair{+h: H, +a: A, +b: A}
  VlCode{+h: H, +fi: U32, +body: Cd}
  VlGate{}
  VlAborted{}
  VlVar{+h: H, +p: String}
  VlAny{}
  VlSuper{+h: H, +n: Maybe<&2, String>, +a: A, +b: A}

def a.h(v: A) -> H:
  match v:
    case VlZero{}:
      PH{31, 37}
    case VlPair{h, a, b}:
      h
    case VlCode{h, fi, body}:
      h
    case VlGate{}:
      PH{41, 43}
    case VlAborted{}:
      PH{47, 53}
    case VlVar{h, p}:
      h
    case VlAny{}:
      PH{59, 61}
    case VlSuper{h, n, a, b}:
      h

def h.eq(a: H, b: H) -> Bool:
  match a:
    case PH{+x, +y}:
      match b:
        case PH{+u, +v}:
          U32.is_eq(x, u) && U32.is_eq(y, v)

# The same value, by digest.
def same(+a: A, +b: A) -> Bool:
  h.eq(a.h(a), a.h(b))

def pair(+a: A, +b: A) -> A:
  VlPair{mix.h(mix(a.h(a), 67), a.h(b)), a, b}

def n.h(n: Maybe<&2, String>, +h: H) -> H:
  match n:
    case Some{p}:
      hash.str(p, mix(h, 71))
    case None{}:
      mix(h, 73)

def super(+n: Maybe<&2, String>, +a: A, +b: A) -> A:
  VlSuper{mix.h(mix(n.h(n, a.h(a)), 79), a.h(b)), n, a, b}

def var.root() -> A:
  VlVar{PH{83, 89}, ""}

# The branch selectors a gate gives (doLeft, doRight).
def do.left() -> A:
  VlCode{PH{97, 101}, Co.left.gate.ind(), GLeft{GEnv{}}}

def do.right() -> A:
  VlCode{PH{103, 107}, Co.right.gate.ind(), GRight{GEnv{}}}

# What a branch knows of the input (InputPath): positions known to be 0, with
# everything below them, and positions known to be pairs, with everything
# above them, as a tree over the positions.
type K is Data:
  KE{}
  KN{+z: Bool, +p: Bool, +l: K, +r: K}

def zero.known(seen: Bool) -> Maybe<&2, Bool>:
  match seen:
    case True{}:
      Some{True{}}
    case False{}:
      None{}

def k.end(k: K, seen: Bool) -> Maybe<&2, Bool>:
  match k:
    case KE{}:
      zero.known(seen)
    case KN{z, p, l, r}:
      match p:
        case True{}:
          Some{False{}}
        case False{}:
          zero.known(z || seen)

# What the path says of position m, having seen a known 0 above it or not:
# True where m is 0, False where it is a pair (pathDecides).
def k.at(m: String, k: K, +seen: Bool) -> Maybe<&2, Bool>:
  match m:
    case SNil{}:
      k.end(k, seen)
    case SCon{c, rest}:
      match c:
        case Chr{+b}:
          match k:
            case KE{}:
              zero.known(seen)
            case KN{+z, p, l, r}:
              k.at(rest, Bool.pick(K, U32.is_eq(b, 76), l, r), z || seen)

def decides(+k: K, +m: String) -> Maybe<&2, Bool>:
  k.at(m, k, False{})

def decides.n(+k: K, n: Maybe<&2, String>) -> Maybe<&2, Bool>:
  match n:
    case Some{+m}:
      decides(k, m)
    case None{}:
      None{}

def k.mark.leaf(+zero: Bool, k: K) -> K:
  match k:
    case KE{}:
      KN{zero, Bool.not(zero), KE{}, KE{}}
    case KN{z, p, l, r}:
      KN{zero || z, Bool.not(zero) || p, l, r}

def k.join(left: Bool, +zero: Bool, +z: Bool, +p: Bool, +l: K, +r: K, sub: K) -> K:
  match left:
    case True{}:
      KN{z, Bool.not(zero) || p, sub, r}
    case False{}:
      KN{z, Bool.not(zero) || p, l, sub}

# The path with position n known 0 (zero) or a pair, walking down to it. A pair
# marks every position above it too (withLiteral).
def k.with(+zero: Bool, n: String, k: K) -> K:
  match n:
    case SNil{}:
      k.mark.leaf(zero, k)
    case SCon{c, rest}:
      match c:
        case Chr{+b}:
          match k:
            case KE{}:
              k.join(U32.is_eq(b, 76), zero, False{}, False{}, KE{}, KE{}, k.with(zero, rest, KE{}))
            case KN{+z, +p, +l, +r}:
              k.join(U32.is_eq(b, 76), zero, z, p, l, r, k.with(zero, rest, Bool.pick(K, U32.is_eq(b, 76), l, r)))

# withLiteral through a Maybe.
def k.with.n(+zero: Bool, n: Maybe<&2, String>, k: K) -> K:
  match n:
    case Some{+m}:
      k.with(zero, m, k)
    case None{}:
      k

# decendant x d: x is d or below it.
def below(+x: String, +d: String) -> Bool:
  String.starts_with(x, d)

def known.if(yes: Bool, +value: Bool) -> Maybe<&2, Bool>:
  match yes:
    case True{}:
      Some{value}
    case False{}:
      None{}

# What knowing position n to be 0 (zero) or a pair says of position m
# (literalDecides).
def literal.decides(+zero: Bool, +n: String, +m: String) -> Maybe<&2, Bool>:
  match zero:
    case True{}:
      known.if(below(m, n), True{})
    case False{}:
      known.if(below(n, m), False{})

# What the literal decides of v's top superposition, if v has one.
def peel.d(+zero: Bool, +n: String, v: A) -> Maybe<&2, Bool>:
  match v:
    case VlSuper{h, m, l, r}:
      match m:
        case Some{+q}:
          literal.decides(zero, n, q)
        case None{}:
          None{}
    case _:
      None{}

# v with what the literal decides of its top superpositions taken.
def peel(+zero: Bool, +n: String, v: A, d: Maybe<&2, Bool>) -> A:
  match v:
    case VlSuper{h, m, +l, +r}:
      match d:
        case Some{pick}:
          match pick:
            case True{}:
              peel(zero, n, l, peel.d(zero, n, l))
            case False{}:
              peel(zero, n, r, peel.d(zero, n, r))
        case None{}:
          VlSuper{h, m, l, r}
    case other:
      other

def peeled(+zero: Bool, +n: String, +v: A) -> A:
  peel(zero, n, v, peel.d(zero, n, v))

# mergeExact's walk: the choice pushed down past the structure the branches
# share, a superposition left only where they differ in shape. x and y are
# peeled, and eq says they are the same.
def merge.go(+fuel: Nat, +q: String, eq: Bool, +x: A, +y: A) -> A:
  match fuel:
    case 0n:
      x
    case 1n+f:
      match eq:
        case True{}:
          x
        case False{}:
          match x:
            case VlPair{hx, xl, xr}:
              match y:
                case VlPair{hy, yl, yr}:
                  +a = peeled(True{}, q, xl)
                  +c = peeled(False{}, q, yl)
                  +b = peeled(True{}, q, xr)
                  +d = peeled(False{}, q, yr)
                  pair(merge.go(f, q, same(a, c), a, c), merge.go(f, q, same(b, d), b, d))
                case _:
                  super(Some{q}, VlPair{hx, xl, xr}, y)
            case _:
              super(Some{q}, x, y)

def merge.pick(eq: Bool, +a: A, +b: A) -> A:
  match eq:
    case True{}:
      a
    case False{}:
      super(None{}, a, b)

def fuel() -> Nat:
  U32.to_nat(4294967295)

# EitherPF n a b, kept as small as exactness allows (mergeExact). An unknown
# choice is not pushed down, since its two uses would no longer be the same
# choice.
def merge.exact(n: Maybe<&2, String>, +a: A, +b: A) -> A:
  match n:
    case Some{+q}:
      +x = peeled(True{}, q, a)
      +y = peeled(False{}, q, b)
      merge.go(fuel(), q, same(x, y), x, y)
    case None{}:
      merge.pick(same(a, b), a, b)

# The run
# -------

# One run of a check that may fail: what the run knew of the input when the
# check ran, and the check's abort message there, 0 where it passes
# (CheckFire).
type PFire is Data:
  PFire{+path: K, +r: A}

type PRow is Data:
  PRow{+o: L.Origin, +runs: List<&2, PFire>}

# The steps counted, and every run of each check that may fail, latest first.
type PSt is Data:
  PSt{+n: U32, +fires: Map<&2, PRow>}

type PEv is Data:
  PEv{+v: A, +st: PSt}

def tick(st: PSt) -> PSt:
  match st:
    case PSt{+n, fires}:
      PSt{(n + 1 : U32), fires}

def row.add(r: Map<&2, PRow> & PRow, +key: String, +f: PFire) -> Map<&2, PRow>:
  (m, row) = r
  match row:
    case PRow{o, runs}:
      Map.set(&2, PRow, m, key, PRow{o, f <> runs})

def fire.in(+o: L.Origin, +f: PFire, +fires: Map<&2, PRow>) -> Map<&2, PRow>:
  +key = L.origin.key(o)
  row.add(Map.get(PRow, PRow{o, []}, fires, key), key, f)

# What d says of a superposition's or variable's position.
def top.d(+path: K, v: A) -> Maybe<&2, Bool>:
  match v:
    case VlVar{h, +p}:
      decides(path, p)
    case VlSuper{h, n, a, b}:
      decides.n(path, n)
    case _:
      None{}

def not.zero(d: Maybe<&2, Bool>) -> Bool:
  match d:
    case Some{z}:
      Bool.not(z)
    case None{}:
      True{}

# Whether a check's result is something other than 0 on some path consistent
# with the given one, walking its superpositions under what each branch knows
# (mayBeNonZero).
def may.nonzero(m: A, +path: K, d: Maybe<&2, Bool>) -> Bool:
  match m:
    case VlZero{}:
      False{}
    case VlVar{h, p}:
      not.zero(d)
    case VlSuper{h, +n, +l, +r}:
      match d:
        case Some{pick}:
          match pick:
            case True{}:
              may.nonzero(l, path, top.d(path, l))
            case False{}:
              may.nonzero(r, path, top.d(path, r))
        case None{}:
          +pz = k.with.n(True{}, n, path)
          +pn = k.with.n(False{}, n, path)
          may.nonzero(l, pz, top.d(pz, l)) || may.nonzero(r, pn, top.d(pn, r))
    case _:
      True{}

# A run of an abort node: recorded if it may fire with anything but 0, then
# forgotten: every aborted value is the same one, so that runs differing only
# in which check stopped them merge.
def fired.if(yes: Bool, +o: L.Origin, +path: K, +m: A, st: PSt) -> PSt:
  match yes:
    case True{}:
      match st:
        case PSt{+n, +fires}:
          PSt{n, fire.in(o, PFire{path, m}, fires)}
    case False{}:
      st

# The steps the check analysis may take before the compiler gives up and keeps
# every check where it is (checkDecisionBudget).
def budget() -> U32:
  100000000

# What a superposition's two sides do.
type Bk is Data:
  BLeft{+a: A, +b: A}
  BRight{+a: A, +b: A}
  BSet{+a: A, +b: A}
  BGate{+a: A, +b: A}
  BFill{+a: A, +b: A, +e: A}

# What the evaluator takes on. A def may only call itself, so where one run's
# result feeds the next it is handed to itself as a job.
type PJob is Data:
  QEval{+t: Cd, +env: A, +st: PSt}
  QPairA{+b: Cd, +env: A, +r: PEv}
  QPairB{+va: A, +r: PEv}
  QLeftK{+r: PEv}
  QRightK{+r: PEv}
  QSetK{+r: PEv}
  QAbortK{+o: L.Origin, +r: PEv}
  QLeft{+v: A, +st: PSt}
  QRight{+v: A, +st: PSt}
  QSet{+v: A, +st: PSt}
  QGate{+e: A, +st: PSt}
  QDecide{+d: Maybe<&2, Bool>, +n: Maybe<&2, String>, +k: Bk, +st: PSt}
  QMergeA{+n: Maybe<&2, String>, +k: Bk, +r: PEv}
  QMergeB{+n: Maybe<&2, String>, +va: A, +r: PEv}
  QDone{+r: PEv}

# One side of a superposition: its a side where zero, else its b side.
def side(k: Bk, zero: Bool, st: PSt) -> PJob:
  match k:
    case BLeft{a, b}:
      QLeft{Bool.pick(A, zero, a, b), st}
    case BRight{a, b}:
      QRight{Bool.pick(A, zero, a, b), st}
    case BSet{a, b}:
      QSet{Bool.pick(A, zero, a, b), st}
    case BGate{a, b}:
      QGate{Bool.pick(A, zero, a, b), st}
    case BFill{a, b, +e}:
      QSet{pair(Bool.pick(A, zero, a, b), e), st}

def gate.var(d: Maybe<&2, Bool>, +p: String) -> A:
  match d:
    case Some{z}:
      Bool.pick(A, z, do.left(), do.right())
    case None{}:
      super(Some{p}, do.left(), do.right())

# An application's body, unless the budget is spent.
def run.job(over: Bool, +body: Cd, +e: A, +st: PSt) -> PJob:
  match over:
    case True{}:
      QDone{PEv{VlAny{}, st}}
    case False{}:
      QEval{body, e, st}

def st.over(st: PSt) -> Bool:
  match st:
    case PSt{+n, fires}:
      U32.is_ge(n, budget())

# The environment read: data and code are plain movement; anything else counts.
def env.read(+env: A, st: PSt) -> PEv:
  match env:
    case VlZero{}:
      PEv{env, st}
    case VlPair{h, a, b}:
      PEv{env, st}
    case VlCode{h, fi, body}:
      PEv{env, st}
    case VlGate{}:
      PEv{env, st}
    case _:
      PEv{env, tick(st)}

# exactSuperStepM with what it runs under: children first, not under a closure;
# applying a closure runs its body with the environment replaced.
def ev(+fuel: Nat, +path: K, job: PJob) -> PEv:
  match fuel:
    case 0n:
      PEv{VlAny{}, PSt{budget(), Map.new(&2, PRow)}}
    case 1n+f:
      match job:
        case QEval{t, +env, +st}:
          match t:
            case GZero{}:
              PEv{VlZero{}, st}
            case GPair{a, b}:
              ev(f, path, QPairA{b, env, ev(f, path, QEval{a, env, st})})
            case GEnv{}:
              env.read(env, st)
            case GSet{x}:
              ev(f, path, QSetK{ev(f, path, QEval{x, env, st})})
            case GDefer{h, fi, x}:
              PEv{VlCode{h, fi, x}, st}
            case GGate{}:
              PEv{VlGate{}, st}
            case GLeft{x}:
              ev(f, path, QLeftK{ev(f, path, QEval{x, env, st})})
            case GRight{x}:
              ev(f, path, QRightK{ev(f, path, QEval{x, env, st})})
            case GAbort{o, m}:
              ev(f, path, QAbortK{o, ev(f, path, QEval{m, env, st})})
        case QPairA{b, env, r}:
          match r:
            case PEv{va, st}:
              ev(f, path, QPairB{va, ev(f, path, QEval{b, env, st})})
        case QPairB{+va, r}:
          match r:
            case PEv{+vb, st}:
              PEv{pair(va, vb), st}
        case QLeftK{r}:
          match r:
            case PEv{v, st}:
              ev(f, path, QLeft{v, st})
        case QRightK{r}:
          match r:
            case PEv{v, st}:
              ev(f, path, QRight{v, st})
        case QSetK{r}:
          match r:
            case PEv{v, st}:
              ev(f, path, QSet{v, st})
        case QAbortK{+o, r}:
          match r:
            case PEv{+m, st}:
              PEv{VlAborted{}, tick(fired.if(may.nonzero(m, path, top.d(path, m)), o, path, m, st))}
        case QLeft{v, +st}:
          match v:
            case VlZero{}:
              PEv{VlZero{}, st}
            case VlPair{h, a, b}:
              PEv{a, st}
            case VlAborted{}:
              PEv{VlAborted{}, tick(st)}
            case VlVar{+h, +p}:
              PEv{VlVar{mix(h, 76), p ++ "L"}, tick(st)}
            case VlSuper{h, +n, a, b}:
              ev(f, path, QDecide{decides.n(path, n), n, BLeft{a, b}, tick(st)})
            case _:
              PEv{VlAny{}, tick(st)}
        case QRight{v, +st}:
          match v:
            case VlZero{}:
              PEv{VlZero{}, st}
            case VlPair{h, a, b}:
              PEv{b, st}
            case VlAborted{}:
              PEv{VlAborted{}, tick(st)}
            case VlVar{+h, +p}:
              PEv{VlVar{mix(h, 82), p ++ "R"}, tick(st)}
            case VlSuper{h, +n, a, b}:
              ev(f, path, QDecide{decides.n(path, n), n, BRight{a, b}, tick(st)})
            case _:
              PEv{VlAny{}, tick(st)}
        case QSet{v, +st}:
          match v:
            case VlPair{h, c, +e}:
              match c:
                case VlCode{hc, fi, body}:
                  ev(f, path, run.job(st.over(st), body, e, st))
                case VlGate{}:
                  ev(f, path, QGate{e, st})
                case VlAborted{}:
                  PEv{VlAborted{}, tick(st)}
                case VlSuper{hs, +n, a, b}:
                  ev(f, path, QDecide{decides.n(path, n), n, BFill{a, b, e}, tick(st)})
                case _:
                  PEv{VlAny{}, tick(st)}
            case VlAborted{}:
              PEv{VlAborted{}, tick(st)}
            case VlSuper{h, +n, a, b}:
              ev(f, path, QDecide{decides.n(path, n), n, BSet{a, b}, tick(st)})
            case _:
              PEv{VlAny{}, tick(st)}
        case QGate{e, +st}:
          match e:
            case VlZero{}:
              PEv{do.left(), st}
            case VlPair{h, a, b}:
              PEv{do.right(), st}
            case VlAborted{}:
              PEv{VlAborted{}, tick(st)}
            case VlVar{h, +p}:
              PEv{gate.var(decides(path, p), p), tick(st)}
            case VlSuper{h, +n, a, b}:
              ev(f, path, QDecide{decides.n(path, n), n, BGate{a, b}, tick(st)})
            case _:
              PEv{VlAny{}, tick(st)}
        case QDecide{d, +n, +k, st}:
          match d:
            case Some{pick}:
              ev(f, path, side(k, pick, st))
            case None{}:
              ev(f, path, QMergeA{n, k, ev(f, k.with.n(True{}, n, path), side(k, True{}, st))})
        case QMergeA{+n, k, r}:
          match r:
            case PEv{va, st}:
              ev(f, path, QMergeB{n, va, ev(f, k.with.n(False{}, n, path), side(k, False{}, st))})
        case QMergeB{n, +va, r}:
          match r:
            case PEv{+vb, st}:
              PEv{merge.exact(n, va, vb), st}
        case QDone{r}:
          r

# Where a failure matters
# -----------------------

# What a value says, on the paths consistent with a given one, of whether a run
# aborts: on every one of them, on none, or on some, with the first undecided
# superposition in a part that may abort (AbortStatus).
type AS is Data:
  AbSure{}
  AbFree{}
  AbMay{+t: Maybe<&2, String>}

def as.tag(s: AS) -> Maybe<&2, String>:
  match s:
    case AbMay{t}:
      t
    case _:
      None{}

def as.pair(sa: AS, sb: AS) -> AS:
  match sa:
    case AbSure{}:
      AbSure{}
    case AbFree{}:
      sb
    case AbMay{n}:
      match sb:
        case AbSure{}:
          AbSure{}
        case _:
          AbMay{n}

def as.super(n: Maybe<&2, String>, +sa: AS, +sb: AS) -> AS:
  match sa:
    case AbSure{}:
      match sb:
        case AbSure{}:
          AbSure{}
        case _:
          AbMay{Maybe.or(&2, String, n, Maybe.or(&2, String, as.tag(sa), as.tag(sb)))}
    case AbFree{}:
      match sb:
        case AbFree{}:
          AbFree{}
        case _:
          AbMay{Maybe.or(&2, String, n, Maybe.or(&2, String, as.tag(sa), as.tag(sb)))}
    case _:
      AbMay{Maybe.or(&2, String, n, Maybe.or(&2, String, as.tag(sa), as.tag(sb)))}

# One walk of a value for its status. Sound but not complete: a pair aborting
# on every path only because its two sides abort on complementary ones is a May
# (abortStatus).
def abort.status(v: A, +path: K, d: Maybe<&2, Bool>) -> AS:
  match v:
    case VlAborted{}:
      AbSure{}
    case VlPair{h, +a, +b}:
      as.pair(abort.status(a, path, top.d(path, a)), abort.status(b, path, top.d(path, b)))
    case VlSuper{h, +n, +a, +b}:
      match d:
        case Some{pick}:
          match pick:
            case True{}:
              abort.status(a, path, top.d(path, a))
            case False{}:
              abort.status(b, path, top.d(path, b))
        case None{}:
          +pz = k.with.n(True{}, n, path)
          +pn = k.with.n(False{}, n, path)
          as.super(n, abort.status(a, pz, top.d(pz, a)), abort.status(b, pn, top.d(pn, b)))
    case _:
      AbFree{}

# Whether an input position is in the input, not the state: main's input is
# (input, state), so under its left, or the root itself, whether there is any
# (onInput).
def on.input(m: String) -> Bool:
  match m:
    case SNil{}:
      True{}
    case SCon{Chr{+c}, t}:
      U32.is_eq(c, 76)

# The input positions a check's result reads are all on the input, and it reads
# nothing the analysis could not follow (fireReads).
def reads.on.input(r: A) -> Bool:
  match r:
    case VlZero{}:
      True{}
    case VlPair{h, a, b}:
      reads.on.input(a) && reads.on.input(b)
    case VlVar{h, m}:
      on.input(m)
    case VlSuper{h, n, a, b}:
      match n:
        case Some{q}:
          on.input(q) && reads.on.input(a) && reads.on.input(b)
        case None{}:
          False{}
    case _:
      False{}

# Everything the path knows is on the input.
def k.on.input(k: K) -> Bool:
  match k:
    case KE{}:
      True{}
    case KN{z, p, l, r}:
      match r:
        case KE{}:
          True{}
        case _:
          False{}

# The path says the input is a pair somewhere.
def k.has.pair(k: K) -> Bool:
  match k:
    case KE{}:
      False{}
    case KN{z, p, l, r}:
      p

# What one run of a check comes to, as a decision over input positions.
type CT is Data:
  CTPass{}
  CTFail{+msg: A}
  CTUndecided{}
  CTSplit{+n: String, +a: CT, +b: CT}

def ct.eq(a: CT, b: CT) -> Bool:
  match a:
    case CTPass{}:
      match b:
        case CTPass{}:
          True{}
        case _:
          False{}
    case CTFail{+x}:
      match b:
        case CTFail{+y}:
          same(x, y)
        case _:
          False{}
    case CTUndecided{}:
      match b:
        case CTUndecided{}:
          True{}
        case _:
          False{}
    case CTSplit{+n, a1, a2}:
      match b:
        case CTSplit{+m, b1, b2}:
          String.eq(n, m) && ct.eq(a1, b1) && ct.eq(a2, b2)
        case _:
          False{}

def split.if(eq: Bool, +n: String, +a: CT, +b: CT) -> CT:
  match eq:
    case True{}:
      a
    case False{}:
      CTSplit{n, a, b}

# A Split that does not merely repeat one tree.
def split(+n: String, +a: CT, +b: CT) -> CT:
  split.if(ct.eq(a, b), n, a, b)

def undecided.in(t: CT) -> Bool:
  match t:
    case CTUndecided{}:
      True{}
    case CTSplit{n, a, b}:
      undecided.in(a) || undecided.in(b)
    case _:
      False{}

def sure.if(yes: Bool, +msg: A) -> CT:
  match yes:
    case True{}:
      CTFail{msg}
    case False{}:
      CTUndecided{}

# What main's result does where a check fails: the path split on the result's
# own superpositions until it is decided, or the splits run out. Where the run
# surely aborts, the failure is decided before main, unless it can happen on
# the input-less first call or the path has come to depend on the state; where
# it aborts in no case, the failure is never seen.
def demand(+k: Nat, +result: A, +msg: A, +path: K, s: AS) -> CT:
  match k:
    case 0n:
      match s:
        case AbSure{}:
          sure.if(k.on.input(path) && k.has.pair(path), msg)
        case AbFree{}:
          CTPass{}
        case AbMay{t}:
          CTUndecided{}
    case 1n+j:
      match s:
        case AbSure{}:
          sure.if(k.on.input(path) && k.has.pair(path), msg)
        case AbFree{}:
          CTPass{}
        case AbMay{t}:
          match t:
            case Some{+n}:
              +pz = k.with(True{}, n, path)
              +pn = k.with(False{}, n, path)
              split(n, demand(j, result, msg, pz, abort.status(result, pz, top.d(pz, result))),
                       demand(j, result, msg, pn, abort.status(result, pn, top.d(pn, result))))
            case None{}:
              CTUndecided{}

# How many times a path may split on main's result (demandSplits).
def demand.at(+result: A, +msg: A, +path: K) -> CT:
  demand(12n, result, msg, path, abort.status(result, path, top.d(path, result)))

def split.n(n: Maybe<&2, String>, +a: CT, +b: CT) -> CT:
  match n:
    case Some{+q}:
      split(q, a, b)
    case None{}:
      CTUndecided{}

# One run of a check that depends on the input alone, as a decision (runTree):
# its result's own decisions over the input, down to where it fails, and there
# what main's result does.
def fails(r: A, +result: A, +path: K, d: Maybe<&2, Bool>) -> CT:
  match r:
    case VlZero{}:
      CTPass{}
    case VlVar{+h, +v}:
      match d:
        case Some{zero}:
          match zero:
            case True{}:
              CTPass{}
            case False{}:
              demand.at(result, VlVar{h, v}, path)
        case None{}:
          split(v, CTPass{}, demand.at(result, VlVar{h, v}, k.with(False{}, v, path)))
    case VlSuper{h, +n, +a, +b}:
      match d:
        case Some{pick}:
          match pick:
            case True{}:
              fails(a, result, path, top.d(path, a))
            case False{}:
              fails(b, result, path, top.d(path, b))
        case None{}:
          +pz = k.with.n(True{}, n, path)
          +pn = k.with.n(False{}, n, path)
          split.n(n, fails(a, result, pz, top.d(pz, a)), fails(b, result, pn, top.d(pn, b)))
    case +other:
      demand.at(result, other, path)

# Where a check that may fail goes (CheckVerdict): how it is decided before
# main, each run with the path that reached it, and whether main must still
# make it.
type PRun is Data:
  PRun{+path: K, +tree: CT}

type CV is Data:
  CV{+runs: List<&2, PRun>, +kept: Bool}

def all.input(fs: List<&2, PFire>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      match x:
        case PFire{path, r}:
          k.on.input(path) && reads.on.input(r) && all.input(rest)

def runs.of(fs: List<&2, PFire>, +result: A) -> List<&2, PRun>:
  match fs:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case PFire{+path, +r}:
          PRun{path, fails(r, result, path, top.d(path, r))} <> runs.of(rest, result)

def any.undecided(rs: List<&2, PRun>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      match x:
        case PRun{path, t}:
          undecided.in(t) || any.undecided(rest)

def cv.of(und: Bool, +rs: List<&2, PRun>) -> CV:
  match und:
    case True{}:
      CV{[], True{}}
    case False{}:
      CV{rs, False{}}

def cv.if(ok: Bool, fs: List<&2, PFire>, +result: A) -> CV:
  match ok:
    case True{}:
      +rs = runs.of(fs, result)
      cv.of(any.undecided(rs), rs)
    case False{}:
      CV{[], True{}}

# A check whose every run depends on the input alone is decided run by run; it
# stays in main if any part of any run is undecided, and then entirely. Any
# other check stays in main (checkVerdicts).
def verdict(fs: List<&2, PFire>, +result: A) -> CV:
  +forward = List.reverse(&2, PFire, fs)
  cv.if(all.input(forward), forward, result)

type VRow is Data:
  VRow{+o: L.Origin, +cv: CV}

def verdicts(rows: List<&2, PRow>, +result: A) -> List<&2, VRow>:
  match rows:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case PRow{o, fs}:
          VRow{o, verdict(fs, result)} <> verdicts(rest, result)

def vrow.le(a: VRow, b: VRow) -> Bool:
  match a:
    case VRow{oa, ca}:
      match b:
        case VRow{ob, cb}:
          L.origin.le(oa, ob)

# The input prologue
# ------------------

# The strict if on code (GateSwitchEE).
def gate.sw(l: Co.V, r: Co.V, s: Co.V) -> Co.V:
  Co.VSetEnv{Co.VPair{Co.VSetEnv{Co.VPair{Co.VGate{}, s}}, Co.VPair{l, r}}}

def path.step(m: String, +x: Co.V) -> Co.V:
  match m:
    case SNil{}:
      x
    case SCon{Chr{+c}, t}:
      path.step(t, Bool.pick(Co.V, U32.is_eq(c, 76), Co.VLeft{x}, Co.VRight{x}))

# An input position as code whose environment is (input, _) (inputPath).
def input.path(m: String) -> Co.V:
  path.step(m, Co.VLeft{Co.VEnv{}})

def result.code(r: A) -> Co.V:
  match r:
    case VlPair{h, a, b}:
      Co.VPair{result.code(a), result.code(b)}
    case VlVar{h, m}:
      input.path(m)
    case VlSuper{h, n, a, b}:
      match n:
        case Some{q}:
          gate.sw(result.code(a), result.code(b), input.path(q))
        case None{}:
          Co.VZero{}
    case _:
      Co.VZero{}

def tree.code(+o: L.Origin, t: CT) -> Co.V:
  match t:
    case CTFail{msg}:
      Co.VAbort{o, result.code(msg)}
    case CTSplit{n, a, b}:
      gate.sw(tree.code(o, a), tree.code(o, b), input.path(n))
    case _:
      Co.VZero{}

# The shallowest of the positions known 0, ahead of acc.
def k.zeros(k: K, +at: String, acc: List<&2, String>) -> List<&2, String>:
  match k:
    case KE{}:
      acc
    case KN{z, p, l, r}:
      match z:
        case True{}:
          at <> acc
        case False{}:
          k.zeros(l, at ++ "L", k.zeros(r, at ++ "R", acc))

def k.p(k: K) -> Bool:
  match k:
    case KE{}:
      False{}
    case KN{z, p, l, r}:
      p

def at.if(yes: Bool, +at: String, acc: List<&2, String>) -> List<&2, String>:
  match yes:
    case True{}:
      at <> acc
    case False{}:
      acc

# The deepest of the positions known to be pairs, ahead of acc.
def k.pairs(k: K, +at: String, acc: List<&2, String>) -> List<&2, String>:
  match k:
    case KE{}:
      acc
    case KN{z, p, +l, +r}:
      match p:
        case True{}:
          k.pairs(l, at ++ "L", k.pairs(r, at ++ "R", at.if(Bool.not(k.p(l) || k.p(r)), at, acc)))
        case False{}:
          acc

# Numeric order: shorter first, then 'L' before 'R'.
def pos.ord(+a: String, +b: String) -> Bool:
  +la = String.length(a)
  +lb = String.length(b)
  Nat.is_lt(la, lb) || (Nat.is_eq(la, lb) && String.is_le(a, b))

def pos.le(a: String, b: String) -> Bool:
  pos.ord(a, b)

def on.zeros(xs: List<&2, String>, c: Co.V) -> Co.V:
  match xs:
    case Nil{}:
      c
    case Con{n, rest}:
      gate.sw(on.zeros(rest, c), Co.VZero{}, input.path(n))

def on.pairs(xs: List<&2, String>, c: Co.V) -> Co.V:
  match xs:
    case Nil{}:
      c
    case Con{n, rest}:
      gate.sw(Co.VZero{}, on.pairs(rest, c), input.path(n))

# A run's tree under gates testing the path that reached it. Of what the path
# knows, only the deepest of its pairs and the shallowest of its zeros are
# tested, since the rest follows.
def on.path(+path: K, code: Co.V) -> Co.V:
  on.zeros(List.sort(~String, ~pos.le, k.zeros(path, "", [])),
    on.pairs(List.sort(~String, ~pos.le, k.pairs(path, "", [])), code))

def tree.is.pass(t: CT) -> Bool:
  match t:
    case CTPass{}:
      True{}
    case _:
      False{}

def run.code.if(pass: Bool, +o: L.Origin, +path: K, +t: CT, rest: List<&2, Co.V>) -> List<&2, Co.V>:
  match pass:
    case True{}:
      rest
    case False{}:
      on.path(path, tree.code(o, t)) <> rest

def run.codes(rs: List<&2, PRun>, +o: L.Origin, rest: List<&2, Co.V>) -> List<&2, Co.V>:
  match rs:
    case Nil{}:
      rest
    case Con{x, more}:
      match x:
        case PRun{+path, +t}:
          run.code.if(tree.is.pass(t), o, path, t, run.codes(more, o, rest))

def row.codes(rows: List<&2, VRow>) -> List<&2, Co.V>:
  match rows:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case VRow{+o, cv}:
          match cv:
            case CV{rs, kept}:
              run.codes(rs, o, row.codes(rest))

def chain(vs: List<&2, Co.V>) -> Co.V:
  match vs:
    case Nil{}:
      Co.VZero{}
    case Con{v, rest}:
      gate.sw(chain(rest), Co.VZero{}, v)

# main's input prologue: a function run on main's input before main, giving 0
# when every hoisted check passes and, when one does not, the abort of the
# first in the order they were written; none when no check is hoisted
# (inputPrologue). The first call of main, made before there is any input, runs
# without it.
def prologue.of(vs: List<&2, Co.V>) -> Maybe<&2, Co.V>:
  match vs:
    case Nil{}:
      None{}
    case Con{v, rest}:
      Some{Co.VPair{Co.VDefer{Co.prologue.ind(), chain(v <> rest)}, Co.VZero{}}}

# The plan
# --------

# What the check analysis decided (checkPlan). keep: the checks main still
# makes, by origin key, or None when analyzing them was over budget and every
# check stays. hoisted: those the prologue makes.
type Plan is Data:
  Plan{+keep: Maybe<&2, Set()>, +hoisted: Set(), +prologue: Maybe<&2, Co.V>}

def plan.none() -> Plan:
  Plan{None{}, Set.new(), None{}}

def kept.add(rows: List<&2, VRow>, acc: Set()) -> Set():
  match rows:
    case Nil{}:
      acc
    case Con{x, rest}:
      match x:
        case VRow{o, cv}:
          match cv:
            case CV{rs, kept}:
              match kept:
                case True{}:
                  kept.add(rest, Set.add(acc, L.origin.key(o)))
                case False{}:
                  kept.add(rest, acc)

def any.tree(rs: List<&2, PRun>) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      match x:
        case PRun{path, t}:
          Bool.not(tree.is.pass(t)) || any.tree(rest)

def key.if(yes: Bool, +o: L.Origin, acc: Set()) -> Set():
  match yes:
    case True{}:
      Set.add(acc, L.origin.key(o))
    case False{}:
      acc

def hoisted.add(rows: List<&2, VRow>, acc: Set()) -> Set():
  match rows:
    case Nil{}:
      acc
    case Con{x, rest}:
      match x:
        case VRow{+o, cv}:
          match cv:
            case CV{rs, kept}:
              hoisted.add(rest, key.if(any.tree(rs), o, acc))

def plan.rows(+rows: List<&2, VRow>) -> Plan:
  Plan{Some{kept.add(rows, Set.new())}, hoisted.add(rows, Set.new()), prologue.of(row.codes(rows))}

def plan.over(over: Bool, fires: Map<&2, PRow>, +result: A) -> Plan:
  match over:
    case True{}:
      plan.none()
    case False{}:
      plan.rows(List.sort(~VRow, ~vrow.le, verdicts(Map.values(&2, PRow, fires), result)))

def plan.result(r: PEv) -> Plan:
  match r:
    case PEv{+v, st}:
      match st:
        case PSt{+n, fires}:
          plan.over(U32.is_ge(n, budget()), fires, v)

def code.of(c: PCH) -> Cd:
  match c:
    case PCH{h, x}:
      x

def twiddle.of(c: Cd) -> A:
  match c:
    case GDefer{hd, fi, x}:
      VlCode{hd, fi, x}
    case _:
      VlAny{}

def twiddle() -> A:
  twiddle.of(code.of(code(Co.twiddle())))

# The second application of appB: main run on its input.
def applied(r: PEv) -> PEv:
  match r:
    case PEv{v, st}:
      ev(fuel(), KE{}, QSet{v, st})

# main applied to the symbolic input, main's closure evaluated first.
def run.main(r: PEv) -> PEv:
  match r:
    case PEv{v, st}:
      applied(ev(fuel(), KE{}, QSet{pair(twiddle(), pair(var.root(), v)), tick(st)}))

# Where a sized main's refinement checks go.
def plan(prog: Co.V) -> Plan:
  plan.result(run.main(ev(fuel(), KE{}, QEval{code.of(code(prog)), VlZero{}, PSt{0, Map.new(&2, PRow)}})))

# Whether main still makes a check from this origin.
def kept(k: Maybe<&2, Set()>, +o: L.Origin) -> Bool:
  match k:
    case None{}:
      True{}
    case Some{s}:
      Pair.snd(Set(), Bool, Set.has(s, L.origin.key(o)))

def erase.of(m: Maybe<&2, L.Origin>, +keep: Maybe<&2, Set()>) -> Bool:
  match m:
    case Some{+o}:
      Bool.not(kept(keep, o))
    case None{}:
      False{}

def erase.pick(yes: Bool, +c: Co.V, +whole: Co.V) -> Co.V:
  match yes:
    case True{}:
      c
    case False{}:
      Co.VSetEnv{whole}

def erase.set(+keep: Maybe<&2, Set()>, x: Co.V) -> Co.V:
  match x:
    case Co.VPair{a, b}:
      match a:
        case Co.VDefer{+fi, +body}:
          match b:
            case Co.VPair{+tc, +c}:
              erase.pick(U32.is_eq(fi, Co.refinement.tc()) && erase.of(Co.check.origin(body), keep), c, Co.VPair{Co.VDefer{fi, body}, Co.VPair{tc, c}})
            case other:
              Co.VSetEnv{Co.VPair{Co.VDefer{fi, body}, other}}
        case other:
          Co.VSetEnv{Co.VPair{other, b}}
    case other:
      Co.VSetEnv{other}

# Every check main no longer makes becomes the value it guards (eraseChecks).
def erase(+keep: Maybe<&2, Set()>, v: Co.V) -> Co.V:
  match v:
    case Co.VPair{a, b}:
      Co.VPair{erase(keep, a), erase(keep, b)}
    case Co.VSetEnv{x}:
      erase.set(keep, erase(keep, x))
    case Co.VDefer{fi, x}:
      Co.VDefer{fi, erase(keep, x)}
    case Co.VLeft{x}:
      Co.VLeft{erase(keep, x)}
    case Co.VRight{x}:
      Co.VRight{erase(keep, x)}
    case Co.VAbort{o, m}:
      Co.VAbort{o, erase(keep, m)}
    case other:
      other

# main as the plan leaves it.
def erased(p: Plan, +v: Co.V) -> Co.V:
  match p:
    case Plan{keep, h, g}:
      match keep:
        case None{}:
          v
        case Some{+s}:
          erase(Some{s}, v)

# For bend/dev/plantime.bend: the steps the run took, and the runs of checks it
# recorded.
def run.counts(rows: List<&2, PRow>) -> Nat:
  match rows:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case PRow{o, runs}:
          (List.length(&2, PFire, runs) + run.counts(rest) : Nat)

def stats.of(r: PEv) -> String:
  match r:
    case PEv{v, st}:
      match st:
        case PSt{+n, +fires}:
          "steps " ++ U32.show(n) ++ ", checks " ++ Nat.show(Map.size(&2, PRow, fires)) ++ ", runs " ++ Nat.show(run.counts(Map.values(&2, PRow, fires)))

def stats(prog: Co.V) -> String:
  stats.of(run.main(ev(fuel(), KE{}, QEval{code.of(code(prog)), VlZero{}, PSt{0, Map.new(&2, PRow)}})))
