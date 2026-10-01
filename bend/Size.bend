import Base
import ./Expr.bend as E
import ./Core.bend as Co
import ./Term.bend as T
import ./Loc.bend as L

# Sizing (haskell-final's Telomare.Size, Size.IR and the sizing half of
# Telomare.Machine). One abstract run of main over a symbolic input finds
# how deep each recursion can go:
#
# 1. The input limits: main run with every recursion left opaque, each
#    refinement check evaluated over the symbolic input to learn which
#    input positions must be 0 (zeroes) and which must be pairs.
# 2. The main run: input positions stand for unknown data; a gate on one
#    explores both branches as a superposition (EitherPF); each recursion
#    unrolls one step at a time, recording the depth where its test says
#    stop (SizeStageF). A test that depends on input nothing bounds, or a
#    recursion past the budget, fails sizing.
# 3. Each recursion site becomes a chain of that many steps
#    (sizedRecursionChain), over the program as written.
#
# The evaluator is Haskell's transformNoDeferM over its step chain: children
# first (not under a Defer), then the step on the node; applying a closure
# evaluates its body with Env replaced by the argument. The three runs are
# one machine with a mode.

# Which run: the main sizing run, the input limits pass, or a refinement
# check inside it.

type Mode is Data:
  MSize{}
  MLimits{}
  MCheck{}

type Cfg is Data:
  Cfg{+mode: Mode, +zeros: Set(), +max: U32}

# A result: the value, the counts found (SizedRecursion), and the input
# restrictions found (zeroes, pairs).
type R is Data:
  R{+v: E.X, +s: List<&2, E.TS>, +z: Set(), +p: Set()}

type Job is Data:
  JEval{+t: E.X, +env: E.X}
  JStep{+t: E.X}

# Where a gate's outcome can go: left, right, or an outcome already
# aborted (GateResult).
type GR is Data:
  GR{+l: Bool, +r: Bool, +o: Maybe<&2, E.X>}

# What a check needs of the input for its answer to come out as expected
# (expected: Just False = 0, Just True = a pair).
type IRX is Data:
  IRX{+z: Set(), +p: Set(), +v: E.X}

# Why sizing failed. Leftover is sizing's own bug: the program it would
# hand the runtime still holds a form only sizing uses.
type SizeFail is Data:
  Unsizable{+tok: U32}
  Overfueled{+tok: U32}
  Crash{+msg: String}
  Leftover{+form: String}

# The sized program, as the runnable core, and the counts that sized it.
type Sized is Data:
  Sized{+counts: List<&2, E.TS>, +expr: Co.V}

type InSt is Data:
  InSt{+split: Bool, +p: String}

def has(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

def union(a: Set(), b: Set()) -> Set():
  Map.union(&2, Unit, a, b)

# Counts
# ------

def ts.tok(t: E.TS) -> U32:
  match t:
    case E.TS{tok, n}:
      tok

def ts.put(c: Cmp, +t: E.TS, y: E.TS, rest: List<&2, E.TS>, later: List<&2, E.TS>) -> List<&2, E.TS>:
  match c:
    case LT{}:
      t <> y <> rest
    case EQ{}:
      match t:
        case E.TS{tok, a}:
          match y:
            case E.TS{tok2, b}:
              E.TS{tok, U32.max(a, b)} <> rest
    case GT{}:
      y <> later

# A count into ascending counts, keeping the larger at the same token.
def ts.insert(ys: List<&2, E.TS>, +t: E.TS) -> List<&2, E.TS>:
  match ys:
    case Nil{}:
      [t]
    case Con{+y, +rest}:
      ts.put(U32.cmp(ts.tok(t), ts.tok(y)), t, y, rest, ts.insert(rest, t))

# The union of two count lists, maximum at each token (SizedRecursion's
# semigroup).
def ts.merge(xs: List<&2, E.TS>, ys: List<&2, E.TS>) -> List<&2, E.TS>:
  match xs:
    case Nil{}:
      ys
    case Con{x, rest}:
      ts.merge(rest, ts.insert(ys, x))

def ret(v: E.X) -> R:
  R{v, [], Set.new(), Set.new()}

def r.v(r: R) -> E.X:
  match r:
    case R{v, s, z, p}:
      v

# r's findings added to q's result.
def plus(r: R, q: R) -> R:
  match r:
    case R{v1, s1, z1, p1}:
      match q:
        case R{v2, s2, z2, p2}:
          R{v2, ts.merge(s1, s2), union(z1, z2), union(p1, p2)}

def with.value(r: R, +v: E.X) -> R:
  match r:
    case R{v1, s, z, p}:
      R{v, s, z, p}

def pair.of(ra: R, rb: R) -> R:
  match ra:
    case R{va, sa, za, pa}:
      match rb:
        case R{vb, sb, zb, pb}:
          R{E.XPair{va, vb}, ts.merge(sa, sb), union(za, zb), union(pa, pb)}

def staged(sr: List<&2, E.TS>, r: R) -> R:
  match r:
    case R{v, s, z, p}:
      R{v, ts.merge(sr, s), z, p}

def bad(msg: String) -> R:
  ret(E.XError{msg})

# Input positions
# ---------------

# decendant x d: x is d or below it.
def below(+x: String, +d: String) -> Bool:
  String.starts_with(x, d)

def any.below(zs: List<&2, String>, +p: String) -> Bool:
  match zs:
    case Nil{}:
      False{}
    case Con{z, rest}:
      below(z, p) || any.below(rest, p)

# No zero bounds what lies at or below p (isUnbounded).
def unbounded(+zeros: Set(), +p: String) -> Bool:
  Bool.not(any.below(Set.to_list(zeros), p))

def res.pick(zero: Bool, +p: String) -> E.X:
  match zero:
    case True{}:
      E.XZero{}
    case False{}:
      E.XVar{p}

# A position, or 0 where the input is known to be 0.
def res(+zeros: Set(), +p: String) -> E.X:
  res.pick(has(zeros, p), p)

# Steps that need no further evaluation
# -------------------------------------

def cfg.res(cfg: Cfg, +p: String) -> E.X:
  match cfg:
    case Cfg{mode, zeros, max}:
      res(zeros, p)

def cfg.zeros(cfg: Cfg) -> Set():
  match cfg:
    case Cfg{mode, zeros, max}:
      zeros

def cfg.max(cfg: Cfg) -> U32:
  match cfg:
    case Cfg{mode, zeros, max}:
      max

def cfg.check(cfg: Cfg) -> Cfg:
  match cfg:
    case Cfg{mode, zeros, max}:
      Cfg{MCheck{}, Set.new(), max}

def data.eq(a: E.X, b: E.X) -> Bool:
  match a:
    case E.XZero{}:
      match b:
        case E.XZero{}:
          True{}
        case _:
          False{}
    case E.XPair{a1, a2}:
      match b:
        case E.XPair{b1, b2}:
          data.eq(a1, b1) && data.eq(a2, b2)
        case _:
          False{}
    case _:
      False{}

# The same outcome at the top (ShallowEq1): a superposition of two equal
# outcomes is just the outcome.
def shallow.eq(a: E.X, b: E.X) -> Bool:
  match a:
    case E.XZero{}:
      match b:
        case E.XZero{}:
          True{}
        case _:
          False{}
    case E.XDefer{fa, x}:
      match b:
        case E.XDefer{fb, y}:
          U32.is_eq(fa, fb)
        case _:
          False{}
    case E.XAborted{ma}:
      match b:
        case E.XAborted{mb}:
          data.eq(ma, mb)
        case _:
          False{}
    case E.XAbort{}:
      match b:
        case E.XAbort{}:
          True{}
        case _:
          False{}
    case _:
      False{}

def merge.pick(same: Bool, n: Maybe<&2, String>, a: E.X, b: E.X) -> E.X:
  match same:
    case True{}:
      a
    case False{}:
      E.XEither{n, a, b}

# mergeShallow
def merge.shallow(n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  merge.pick(shallow.eq(a, b), n, a, b)

def merge2(n: Maybe<&2, String>, ra: R, rb: R) -> R:
  match ra:
    case R{va, sa, za, pa}:
      match rb:
        case R{vb, sb, zb, pb}:
          R{merge.shallow(n, va, vb), ts.merge(sa, sb), union(za, zb), union(pa, pb)}

def is.gate.selector(x: E.X) -> Bool:
  match x:
    case E.XDefer{+fi, b}:
      U32.is_eq(fi, Co.left.gate.ind()) || U32.is_eq(fi, Co.right.gate.ind())
    case _:
      False{}

def gr.outcome(n: Maybe<&2, String>, oa: Maybe<&2, E.X>, ob: Maybe<&2, E.X>) -> Maybe<&2, E.X>:
  match oa:
    case Some{a}:
      match ob:
        case Some{b}:
          Some{E.XEither{n, a, b}}
        case None{}:
          Some{a}
    case None{}:
      ob

def gr.combine(n: Maybe<&2, String>, ga: GR, gb: GR) -> GR:
  match ga:
    case GR{la, ra, oa}:
      match gb:
        case GR{lb, rb, ob}:
          GR{la || lb, ra || rb, gr.outcome(n, oa, ob)}

def gate.result(v: E.X) -> GR:
  match v:
    case E.XZero{}:
      GR{True{}, False{}, None{}}
    case E.XPair{a, b}:
      GR{False{}, True{}, None{}}
    case E.XAborted{m}:
      GR{False{}, False{}, Some{E.XAborted{m}}}
    case E.XVar{p}:
      GR{True{}, True{}, None{}}
    case E.XEither{+n, a, b}:
      gr.combine(n, gate.result(a), gate.result(b))
    case _:
      GR{False{}, False{}, Some{E.XError{"sizeTermM unhandled gate input"}}}

def fold.branch(n: Maybe<&2, String>, l: Bool, r: Bool) -> Maybe<&2, E.X>:
  match l r:
    case True{} True{}:
      Some{E.XEither{n, E.do.left(), E.do.right()}}
    case True{} False{}:
      Some{E.do.left()}
    case False{} True{}:
      Some{E.do.right()}
    case False{} False{}:
      None{}

def fold.pick(o: Maybe<&2, E.X>, bp: Maybe<&2, E.X>) -> E.X:
  match o:
    case Some{x}:
      match bp:
        case Some{y}:
          E.XEither{None{}, x, y}
        case None{}:
          x
    case None{}:
      match bp:
        case Some{y}:
          y
        case None{}:
          E.XError{"foldGateResult: no results"}

# foldGateResult
def fold.gate(n: Maybe<&2, String>, g: GR) -> E.X:
  match g:
    case GR{l, r, o}:
      fold.pick(o, fold.branch(n, l, r))

def filter.right(yes: Bool, q: String, a: E.X, b: E.X) -> E.X:
  match yes:
    case True{}:
      b
    case False{}:
      E.XEither{Some{q}, a, b}

def filter.at(nt: Maybe<&2, String>, left: Bool, +n: String, +a: E.X, +b: E.X) -> E.X:
  match nt:
    case Some{+q}:
      match left:
        case True{}:
          merge.pick(Bool.not(below(q, n)), Some{q}, a, b)
        case False{}:
          filter.right(below(n, q), q, a, b)
    case None{}:
      E.XEither{None{}, a, b}

# Keep one side of the superpositions a choice at n decides (filterLeft,
# filterRight). The left side goes where the superposition's position is at
# or below n, the right side where n is at or below it, as Haskell has it.
# Code under a Defer holds no superposition, so it is left alone.
def filter(+fuel: Nat, +n: String, +left: Bool, e: E.X) -> E.X:
  match fuel:
    case 0n:
      e
    case 1n+f:
      match e:
        case E.XEither{nt, a, b}:
          filter.at(nt, left, n, filter(f, n, left, a), filter(f, n, left, b))
        case E.XPair{a, b}:
          E.XPair{filter(f, n, left, a), filter(f, n, left, b)}
        case other:
          other

def fuel() -> Nat:
  U32.to_nat(4294967295)

def filter.side(n: Maybe<&2, String>, sel: Bool, +left: Bool, e: E.X) -> E.X:
  match n:
    case None{}:
      e
    case Some{+q}:
      match sel:
        case True{}:
          e
        case False{}:
          filter(fuel(), q, left, e)

def is.unsizeable(x: E.X) -> Bool:
  match x:
    case E.XAborted{E.XPair{E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}, t}}:
      True{}
    case _:
      False{}

def test.pick(n: Maybe<&2, String>, a: Bool, b: Bool, +na: E.X, +nb: E.X) -> E.X:
  match a b:
    case True{} _:
      na
    case False{} True{}:
      nb
    case False{} False{}:
      E.XEither{n, na, nb}

def test.var(ub: Bool, +zeros: Set(), +tok: U32, +p: String) -> E.X:
  match ub:
    case True{}:
      E.XAborted{E.abort.unsizeable(tok)}
    case False{}:
      res(zeros, p)

def test.of(n: Maybe<&2, String>, +na: E.X, +nb: E.X) -> E.X:
  test.pick(n, is.unsizeable(na), is.unsizeable(nb), na, nb)

# A recursion's test value (unsizedTestIndexed, unsizedTestSuper): an input
# position nothing bounds cannot be sized; a known 0 stops it.
def unsized.test(+zeros: Set(), +tok: U32, v: E.X) -> E.X:
  match v:
    case E.XVar{+p}:
      test.var(unbounded(zeros, p), zeros, tok, p)
    case E.XEither{n, a, b}:
      test.of(n, unsized.test(zeros, tok, a), unsized.test(zeros, tok, b))
    case other:
      other

# A recursion placeholder meets its {t, r, b}: the first unrolling, its test
# marked (unsizedStepM''' on UnsizedStubF).
def stub.expand(+tok: U32, v: E.X) -> E.X:
  match v:
    case E.XPair{E.XPair{E.XPair{E.XDefer{sid, tf}, e}, rest}, x}:
      E.XPair{E.XDefer{Co.step.rfa(), E.step.body(tok, 1)},
              E.XPair{E.XPair{E.XDefer{sid, E.XTest{tok, tf}}, e}, rest}}
    case _:
      E.XError{"unsizedStepM''' unexpected oracle operand"}

def step.next(+tok: U32, +n: U32, v: E.X) -> E.X:
  match v:
    case E.XPair{x, trb}:
      E.XPair{E.XDefer{Co.step.rfa(), E.step.body(tok, (n + 1 : U32))}, trb}
    case _:
      E.XError{"unsizedStepM''' unexpected step operand"}

def step.over(over: Bool, +tok: U32, +n: U32, v: E.X) -> E.X:
  match over:
    case True{}:
      E.XAborted{E.abort.recursion(tok)}
    case False{}:
      step.next(tok, n, v)

# The next unrolling, unless past the budget.
def step.expand(+max: U32, +tok: U32, +n: U32, v: E.X) -> E.X:
  step.over(U32.is_gt(n, max), tok, n, v)

# Data only, anything else 0 (abortStep's truncF).
def trunc(e: E.X) -> E.X:
  match e:
    case E.XZero{}:
      E.XZero{}
    case E.XPair{a, b}:
      E.XPair{trunc(a), trunc(b)}
    case _:
      E.XZero{}

def mode.of(cfg: Cfg) -> Mode:
  match cfg:
    case Cfg{mode, zeros, max}:
      mode

# A gate on an input position: both branches while sizing; nothing to learn
# while finding limits; deferred behind a barrier inside a check.
def gate.var(m: Mode, +p: String) -> E.X:
  match m:
    case MSize{}:
      E.XEither{Some{p}, E.do.left(), E.do.right()}
    case MLimits{}:
      E.XAny{}
    case MCheck{}:
      E.XBarrier{E.fill(E.XGate{}, E.XVar{p})}

def gate.any(m: Mode) -> E.X:
  match m:
    case MCheck{}:
      E.XError{"unexpected gate on an unsized value in a check"}
    case _:
      E.XAny{}

def gate.on(+cfg: Cfg, e: E.X) -> E.X:
  match e:
    case E.XZero{}:
      E.do.left()
    case E.XPair{a, b}:
      E.do.right()
    case E.XAborted{m}:
      E.XAborted{m}
    case E.XAny{}:
      gate.any(mode.of(cfg))
    case E.XVar{p}:
      gate.var(mode.of(cfg), p)
    case E.XEither{+n, a, b}:
      fold.gate(n, gate.result(E.XEither{n, a, b}))
    case E.XBarrier{s}:
      E.XBarrier{E.fill(E.XGate{}, s)}
    case _:
      E.XError{"sizeTermM unhandled gate"}

def abort.var(m: Mode) -> E.X:
  match m:
    case MSize{}:
      E.XAborted{E.abort.any()}
    case _:
      E.XError{"unexpected abort on input in a check"}

def abort.on(+cfg: Cfg, e: E.X) -> E.X:
  match e:
    case E.XAborted{m}:
      E.XAborted{m}
    case E.XZero{}:
      E.XDefer{Co.abort.ind(), E.XEnv{}}
    case E.XPair{a, b}:
      E.XAborted{trunc(E.XPair{a, b})}
    case E.XVar{p}:
      abort.var(mode.of(cfg))
    case E.XBarrier{x}:
      E.XBarrier{E.fill(E.XAbort{}, x)}
    case _:
      E.XError{"sizeTermM unhandled abort"}

def any.on(m: Mode) -> E.X:
  match m:
    case MCheck{}:
      E.XError{"unexpected unsized value applied in a check"}
    case _:
      E.XAny{}

# Refinement checks while finding limits
# --------------------------------------

# The check's answer with its barriers removed (stripBarrier).
def strip(x: E.X) -> E.X:
  match x:
    case E.XBarrier{inner}:
      strip(inner)
    case E.XPair{a, b}:
      E.XPair{strip(a), strip(b)}
    case E.XSetEnv{a}:
      E.XSetEnv{strip(a)}
    case E.XLeft{a}:
      E.XLeft{strip(a)}
    case E.XRight{a}:
      E.XRight{strip(a)}
    case E.XLefts{n, a}:
      E.XLefts{n, strip(a)}
    case E.XRights{n, a}:
      E.XRights{n, strip(a)}
    case E.XEither{n, a, b}:
      E.XEither{n, strip(a), strip(b)}
    case E.XAborted{m}:
      E.XAborted{strip(m)}
    case other:
      other

def irx.v(r: IRX) -> E.X:
  match r:
    case IRX{z, p, v}:
      v

def irx.expect(nl: Maybe<&2, IRX>, nr: Maybe<&2, IRX>) -> Maybe<&2, Bool>:
  match nl:
    case Some{a}:
      match nr:
        case Some{b}:
          None{}
        case None{}:
          Some{False{}}
    case None{}:
      match nr:
        case Some{b}:
          Some{True{}}
        case None{}:
          None{}

def irx.add(a: IRX, b: IRX) -> IRX:
  match a:
    case IRX{za, pa, va}:
      match b:
        case IRX{zb, pb, vb}:
          IRX{union(za, zb), union(pa, pb), va}

def irx.combine(nl: Maybe<&2, IRX>, nr: Maybe<&2, IRX>, es: Maybe<&2, IRX>) -> Maybe<&2, IRX>:
  match nl:
    case Some{a}:
      match nr:
        case Some{b}:
          match es:
            case Some{s}:
              Some{irx.add(irx.add(a, b), s)}
            case None{}:
              None{}
        case None{}:
          match es:
            case Some{s}:
              Some{irx.add(a, s)}
            case None{}:
              None{}
    case None{}:
      match nr:
        case Some{b}:
          match es:
            case Some{s}:
              Some{irx.add(b, s)}
            case None{}:
              None{}
        case None{}:
          None{}

def irx.zero(expected: Maybe<&2, Bool>) -> Maybe<&2, IRX>:
  match expected:
    case Some{True{}}:
      None{}
    case _:
      Some{IRX{Set.new(), Set.new(), E.XZero{}}}

def irx.pair(expected: Maybe<&2, Bool>) -> Maybe<&2, IRX>:
  match expected:
    case Some{False{}}:
      None{}
    case _:
      Some{IRX{Set.new(), Set.new(), E.XPair{E.XZero{}, E.XZero{}}}}

def irx.var(expected: Maybe<&2, Bool>, +p: String) -> Maybe<&2, IRX>:
  match expected:
    case Some{False{}}:
      Some{IRX{Set.add(Set.new(), p), Set.new(), E.XZero{}}}
    case Some{True{}}:
      Some{IRX{Set.new(), Set.add(Set.new(), p), E.XPair{E.XZero{}, E.XZero{}}}}
    case None{}:
      Some{IRX{Set.new(), Set.new(), E.XZero{}}}

# extractInputRestrictions' walk.
def extract(+fuel: Nat, x: E.X, +expected: Maybe<&2, Bool>) -> Maybe<&2, IRX>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match x:
        case E.XZero{}:
          irx.zero(expected)
        case E.XPair{a, b}:
          irx.pair(expected)
        case E.XVar{p}:
          irx.var(expected, p)
        case E.XSetEnv{E.XPair{E.XAbort{}, i}}:
          extract(f, i, Some{False{}})
        case E.XSetEnv{E.XPair{E.XSetEnv{E.XPair{E.XGate{}, s}}, E.XPair{l, r}}}:
          +nl = extract(f, l, expected)
          +nr = extract(f, r, expected)
          irx.combine(nl, nr, extract(f, s, irx.expect(nl, nr)))
        case _:
          None{}

def irx.result(m: Maybe<&2, IRX>, +c: E.X) -> R:
  match m:
    case Some{r}:
      match r:
        case IRX{z, p, v}:
          R{c, [], z, p}
    case None{}:
      ret(c)

# The check applied to its value, over the symbolic input (performTC).
def perform.tc(tc: E.X, c: E.X) -> E.X:
  E.fill(E.XAbort{}, E.app(tc, c))

# The evaluator
# -------------

def eval(+fuel: Nat, +cfg: Cfg, job: Job) -> R:
  match fuel:
    case 0n:
      bad("evaluation too deep")
    case 1n+f:
      match job:
        case JEval{t, +env}:
          match t:
            case E.XDefer{fi, x}:
              ret(E.XDefer{fi, x})
            case E.XEnv{}:
              ret(env)
            case E.XVar{p}:
              ret(cfg.res(cfg, p))
            case E.XPair{a, b}:
              pair.of(eval(f, cfg, JEval{a, env}), eval(f, cfg, JEval{b, env}))
            case E.XSetEnv{x}:
              +rx = eval(f, cfg, JEval{x, env})
              plus(rx, eval(f, cfg, JStep{E.XSetEnv{r.v(rx)}}))
            case E.XLeft{x}:
              +rx = eval(f, cfg, JEval{x, env})
              plus(rx, eval(f, cfg, JStep{E.XLeft{r.v(rx)}}))
            case E.XRight{x}:
              +rx = eval(f, cfg, JEval{x, env})
              plus(rx, eval(f, cfg, JStep{E.XRight{r.v(rx)}}))
            case E.XTest{tok, x}:
              +rx = eval(f, cfg, JEval{x, env})
              plus(rx, eval(f, cfg, JStep{E.XTest{tok, r.v(rx)}}))
            case E.XStub{tok, x}:
              +rx = eval(f, cfg, JEval{x, env})
              plus(rx, eval(f, cfg, JStep{E.XStub{tok, r.v(rx)}}))
            case E.XStep{tok, n, x}:
              +rx = eval(f, cfg, JEval{x, env})
              plus(rx, eval(f, cfg, JStep{E.XStep{tok, n, r.v(rx)}}))
            case E.XStage{sr, x}:
              staged(sr, eval(f, cfg, JEval{x, env}))
            case E.XCheck{tc, c}:
              +rtc = eval(f, cfg, JEval{tc, env})
              +rc = eval(f, cfg, JEval{c, env})
              plus(rtc, plus(rc, irx.result(
                extract(fuel(), strip(r.v(eval(f, cfg.check(cfg), JEval{perform.tc(r.v(rtc), r.v(rc)), E.XZero{}}))), None{}),
                r.v(rc))))
            case E.XEither{n, a, b}:
              merge2(n, eval(f, cfg, JEval{a, env}), eval(f, cfg, JEval{b, env}))
            case E.XBarrier{x}:
              +rx = eval(f, cfg, JEval{x, env})
              with.value(rx, E.XBarrier{r.v(rx)})
            case E.XLefts{n, x}:
              +rx = eval(f, cfg, JEval{x, env})
              with.value(rx, E.XLefts{n, r.v(rx)})
            case E.XRights{n, x}:
              +rx = eval(f, cfg, JEval{x, env})
              with.value(rx, E.XRights{n, r.v(rx)})
            case other:
              ret(other)
        case JStep{t}:
          match t:
            case E.XSetEnv{v}:
              match v:
                case E.XPair{c, +e}:
                  match c:
                    case E.XDefer{fi, d}:
                      eval(f, cfg, JEval{d, e})
                    case E.XGate{}:
                      ret(gate.on(cfg, e))
                    case E.XAborted{m}:
                      ret(E.XAborted{m})
                    case E.XAbort{}:
                      match e:
                        case E.XEither{n, a, b}:
                          merge2(n, eval(f, cfg, JStep{E.fill(E.XAbort{}, a)}),
                                    eval(f, cfg, JStep{E.fill(E.XAbort{}, b)}))
                        case other:
                          ret(abort.on(cfg, other))
                    case E.XAny{}:
                      ret(any.on(mode.of(cfg)))
                    case E.XEither{+n, +sca, +scb}:
                      merge2(n, eval(f, cfg, JStep{E.fill(sca, filter.side(n, is.gate.selector(sca), True{}, e))}),
                                eval(f, cfg, JStep{E.fill(scb, filter.side(n, is.gate.selector(scb), False{}, e))}))
                    case E.XBarrier{c2}:
                      ret(E.XBarrier{E.fill(c2, e)})
                    case _:
                      bad("sizeTermM unhandled application")
                case E.XAborted{m}:
                  ret(E.XAborted{m})
                case E.XAny{}:
                  ret(any.on(mode.of(cfg)))
                case E.XEither{n, a, b}:
                  merge2(n, eval(f, cfg, JStep{E.XSetEnv{a}}), eval(f, cfg, JStep{E.XSetEnv{b}}))
                case E.XBarrier{x}:
                  ret(E.XBarrier{E.XSetEnv{x}})
                case _:
                  bad("sizeTermM unhandled SetEnv")
            case E.XLeft{v}:
              match v:
                case E.XZero{}:
                  ret(E.XZero{})
                case E.XPair{a, b}:
                  ret(a)
                case E.XAborted{m}:
                  ret(E.XAborted{m})
                case E.XVar{p}:
                  ret(cfg.res(cfg, p ++ "L"))
                case E.XAny{}:
                  ret(E.XAny{})
                case E.XEither{n, a, b}:
                  merge2(n, eval(f, cfg, JStep{E.XLeft{a}}), eval(f, cfg, JStep{E.XLeft{b}}))
                case E.XBarrier{E.XLefts{k, x}}:
                  ret(E.XBarrier{E.XLefts{(k + 1 : U32), x}})
                case E.XBarrier{x}:
                  ret(E.XBarrier{E.XLefts{1, x}})
                case _:
                  bad("sizeTermM unhandled Left")
            case E.XRight{v}:
              match v:
                case E.XZero{}:
                  ret(E.XZero{})
                case E.XPair{a, b}:
                  ret(b)
                case E.XAborted{m}:
                  ret(E.XAborted{m})
                case E.XVar{p}:
                  ret(cfg.res(cfg, p ++ "R"))
                case E.XAny{}:
                  ret(E.XAny{})
                case E.XEither{n, a, b}:
                  merge2(n, eval(f, cfg, JStep{E.XRight{a}}), eval(f, cfg, JStep{E.XRight{b}}))
                case E.XBarrier{E.XRights{k, x}}:
                  ret(E.XBarrier{E.XRights{(k + 1 : U32), x}})
                case E.XBarrier{x}:
                  ret(E.XBarrier{E.XRights{1, x}})
                case _:
                  bad("sizeTermM unhandled Right")
            case E.XTest{tok, v}:
              ret(unsized.test(cfg.zeros(cfg), tok, v))
            case E.XStub{tok, v}:
              ret(stub.expand(tok, v))
            case E.XStep{tok, n, v}:
              ret(step.expand(cfg.max(cfg), tok, n, v))
            case other:
              ret(other)

# The runs
# --------

# For the limits pass a recursion is opaque (convertIS).
def convert.is(x: E.X) -> E.X:
  match x:
    case E.XStub{tok, y}:
      E.XAny{}
    case E.XTest{tok, y}:
      convert.is(y)
    case E.XPair{a, b}:
      E.XPair{convert.is(a), convert.is(b)}
    case E.XSetEnv{a}:
      E.XSetEnv{convert.is(a)}
    case E.XDefer{fi, a}:
      E.XDefer{fi, convert.is(a)}
    case E.XLeft{a}:
      E.XLeft{convert.is(a)}
    case E.XRight{a}:
      E.XRight{convert.is(a)}
    case E.XCheck{a, b}:
      E.XCheck{convert.is(a), convert.is(b)}
    case other:
      other

# Without the cap, an environment outside every closure reads as 0
# (convertNakedEnvs).
def naked.envs(x: E.X) -> E.X:
  match x:
    case E.XEnv{}:
      E.XZero{}
    case E.XPair{a, b}:
      E.XPair{naked.envs(a), naked.envs(b)}
    case E.XSetEnv{a}:
      E.XSetEnv{naked.envs(a)}
    case E.XLeft{a}:
      E.XLeft{naked.envs(a)}
    case E.XRight{a}:
      E.XRight{naked.envs(a)}
    case E.XStub{tok, a}:
      E.XStub{tok, naked.envs(a)}
    case E.XCheck{a, b}:
      E.XCheck{naked.envs(a), naked.envs(b)}
    case other:
      other

def in.st(+pairs: List<&2, String>, +p: String) -> InSt:
  InSt{any.below(pairs, p), p}

# The symbolic input: pairs as deep as the checks say it is paired, input
# positions below (initialInput).
def initial.input(+fuel: Nat, +pairs: List<&2, String>, st: InSt) -> E.X:
  match fuel:
    case 0n:
      match st:
        case InSt{split, p}:
          E.XVar{p}
    case 1n+f:
      match st:
        case InSt{split, +p}:
          match split:
            case True{}:
              E.XPair{initial.input(f, pairs, in.st(pairs, p ++ "L")), initial.input(f, pairs, in.st(pairs, p ++ "R"))}
            case False{}:
              E.XVar{p}

def fail.tok(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{k}:
      k
    case None{}:
      0

def fail.of.abort(m: E.X) -> Maybe<&2, SizeFail>:
  match m:
    case E.XPair{E.XZero{}, t}:
      Some{Overfueled{fail.tok(E.to.int(t))}}
    case E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}:
      Some{Crash{"sizeTermM AbortAny hit"}}
    case E.XPair{E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}, t}:
      Some{Unsizable{fail.tok(E.to.int(t))}}
    case _:
      None{}

def fail.pick(x: SizeFail, y: SizeFail) -> SizeFail:
  match x:
    case Crash{m}:
      Crash{m}
    case Leftover{f}:
      Leftover{f}
    case Unsizable{t}:
      match y:
        case Crash{m}:
          Crash{m}
        case _:
          Unsizable{t}
    case Overfueled{t}:
      match y:
        case Overfueled{u}:
          Overfueled{t}
        case other:
          other

# SizedResult's semigroup: an unbounded input outweighs an exhausted budget.
def fail.or(a: Maybe<&2, SizeFail>, b: Maybe<&2, SizeFail>) -> Maybe<&2, SizeFail>:
  match a:
    case None{}:
      b
    case Some{x}:
      match b:
        case None{}:
          Some{x}
        case Some{y}:
          Some{fail.pick(x, y)}

# The first failure left in the run's result (foldAborted). Code under a
# Defer holds none.
def fold.aborted(v: E.X) -> Maybe<&2, SizeFail>:
  match v:
    case E.XAborted{m}:
      fail.of.abort(m)
    case E.XError{msg}:
      Some{Crash{msg}}
    case E.XPair{a, b}:
      fail.or(fold.aborted(a), fold.aborted(b))
    case E.XEither{n, a, b}:
      fail.or(fold.aborted(a), fold.aborted(b))
    case _:
      None{}

def count.pick(yes: Bool, n: U32, later: U32) -> U32:
  match yes:
    case True{}:
      n
    case False{}:
      later

def count.of(counts: List<&2, E.TS>, +tok: U32) -> U32:
  match counts:
    case Nil{}:
      1
    case Con{c, rest}:
      match c:
        case E.TS{t, n}:
          count.pick(U32.is_eq(t, tok), (n + 1 : U32), count.of(rest, tok))

# Each recursion site becomes a chain of its count plus one steps
# (setSizes); one never reached gets one.
def set.sizes(+counts: List<&2, E.TS>, x: E.X) -> E.X:
  match x:
    case E.XStub{+tok, y}:
      E.sized.chain(tok, count.of(counts, tok))
    case E.XPair{a, b}:
      E.XPair{set.sizes(counts, a), set.sizes(counts, b)}
    case E.XSetEnv{a}:
      E.XSetEnv{set.sizes(counts, a)}
    case E.XDefer{fi, a}:
      E.XDefer{fi, set.sizes(counts, a)}
    case E.XLeft{a}:
      E.XLeft{set.sizes(counts, a)}
    case E.XRight{a}:
      E.XRight{set.sizes(counts, a)}
    case other:
      other

# main, from main applied to its input.
def uncap(x: E.X) -> E.X:
  match x:
    case E.XSetEnv{E.XSetEnv{E.XPair{tw, E.XPair{i, c}}}}:
      c
    case other:
      other

def r.s(r: R) -> List<&2, E.TS>:
  match r:
    case R{v, s, z, p}:
      s

def r.z(r: R) -> Set():
  match r:
    case R{v, s, z, p}:
      z

def r.p(r: R) -> Set():
  match r:
    case R{v, s, z, p}:
      p

# The sized program handed on as the runnable core (H1: the runtime cannot
# be given a sizing form).
def cored(+counts: List<&2, E.TS>, r: Result<&2, &2, String, Co.V>) -> Result<&2, &2, SizeFail, Sized>:
  match r:
    case Done{v}:
      Done{Sized{counts, v}}
    case Fail{form}:
      Fail{Leftover{form}}

def tidy(m: Maybe<&2, SizeFail>, +run: R, +cm: E.X, cap: Bool) -> Result<&2, &2, SizeFail, Sized>:
  match m:
    case Some{fail}:
      Fail{fail}
    case None{}:
      match cap:
        case True{}:
          cored(r.s(run), E.core(uncap(set.sizes(r.s(run), cm))))
        case False{}:
          cored(r.s(run), E.core(set.sizes(r.s(run), cm)))

def main.run.from(+max: U32, +cm: E.X, zeros: Set(), mx: E.X, +cap: Bool) -> Result<&2, &2, SizeFail, Sized>:
  +run = eval(fuel(), Cfg{MSize{}, zeros, max}, JEval{E.remove.checks(mx), E.XZero{}})
  tidy(fold.aborted(r.v(run)), run, cm, cap)

def main.run(+max: U32, +cm: E.X, +lim: R, +x: E.X, +cap: Bool) -> Result<&2, &2, SizeFail, Sized>:
  match cap:
    case True{}:
      main.run.from(max, cm, r.z(lim), E.app(x, initial.input(fuel(), Set.to_list(r.p(lim)), in.st(Set.to_list(r.p(lim)), ""))), cap)
    case False{}:
      main.run.from(max, cm, r.z(lim), naked.envs(x), cap)

def capped(+x: E.X, cap: Bool) -> E.X:
  match cap:
    case True{}:
      E.app(x, E.XVar{""})
    case False{}:
      x

# sizeTermM: size every recursion in x, cap it (apply it to the symbolic
# input) as main is, and give the sized program, at a budget of max
# unrollings per site.
def size(+max: U32, +cap: Bool, +x: E.X) -> Result<&2, &2, SizeFail, Sized>:
  +cm = capped(x, cap)
  main.run(max, E.remove.checks(cm),
           eval(fuel(), Cfg{MLimits{}, Set.new(), max}, JEval{convert.is(cm), E.XZero{}}),
           x, cap)

# Failures, as the command reports them
# -------------------------------------

def site.loc.if(yes: Bool, l: L.Loc) -> Maybe<&2, L.Loc>:
  match yes:
    case True{}:
      Some{l}
    case False{}:
      None{}

def site.loc(t: T.C, +tok: U32) -> Maybe<&2, L.Loc>:
  match t:
    case T.CUnsized{loc, t2}:
      site.loc.if(U32.is_eq(t2, tok), loc)
    case T.CPair{a, x, y}:
      Maybe.or(&2, L.Loc, site.loc(x, tok), site.loc(y, tok))
    case T.CSetEnv{a, x}:
      site.loc(x, tok)
    case T.CDefer{a, fi, x}:
      site.loc(x, tok)
    case T.CLeft{a, x}:
      site.loc(x, tok)
    case T.CRight{a, x}:
      site.loc(x, tok)
    case T.CCheck{a, c, x, y}:
      Maybe.or(&2, L.Loc, site.loc(x, tok), site.loc(y, tok))
    case _:
      None{}

def site.name(+tok: U32, place: Maybe<&2, String>) -> String:
  match place:
    case Some{p}:
      "recursion #" ++ U32.show(tok) ++ " at " ++ p
    case None{}:
      "recursion #" ++ U32.show(tok)

def site.render(+tok: U32, loc: Maybe<&2, L.Loc>) -> String:
  match loc:
    case Some{l}:
      site.name(tok, L.render_compact(l))
    case None{}:
      site.name(tok, None{})

# renderSizingFailure, the site located in the Term3 (locateSizingFailure).
def render(f: SizeFail, t: T.C, +max: U32) -> String:
  match f:
    case Overfueled{+tok}:
      "could not size " ++ site.render(tok, site.loc(t, tok)) ++ ":\n"
        ++ "  its test had still not stopped after " ++ U32.show((max + 1 : U32)) ++ " unrollings.\n"
        ++ "  Either it needs a deeper recursion than the sizing budget allows, or\n"
        ++ "  its test never stops."
    case Unsizable{+tok}:
      "could not size " ++ site.render(tok, site.loc(t, tok)) ++ ":\n"
        ++ "  its test depends on input that nothing bounds, so no finite iteration\n"
        ++ "  count can be proven for it. Constrain that input with a refinement\n"
        ++ "  (`x : someValidator`) or an `assert` before recursing on it."
    case Crash{msg}:
      msg
    case Leftover{form}:
      "sizing left " ++ form ++ " in the compiled program (a bug in sizing)"
