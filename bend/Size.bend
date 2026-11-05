import Base
import ./Expr.bend as E
import ./Core.bend as Co
import ./Term.bend as T
import ./Loc.bend as L
import ./Sem.bend as Sm
import ./Check.bend as Ck
import ./Plan.bend as Pl

# Sizing (master's Telomare.Size, Size.IR and the sizing half of
# Telomare.Machine). One abstract run of main over a symbolic input finds
# how deep each recursion can go:
#
# 1. The input limits: main run with every recursion left opaque, each
#    refinement check evaluated over the symbolic input to learn which
#    input positions must be 0 (zeroes) and which must be pairs.
# 2. The main run: input positions stand for unknown data; a gate on one
#    explores both branches as a superposition (EitherPF); each recursion
#    unrolls one step at a time, recording every depth whose test it reaches
#    (SizeStageF). A test that depends on input nothing bounds, or a
#    recursion past the budget, fails sizing.
# 3. Each recursion site becomes a chain of that many steps
#    (sizedRecursionChain), over the program as written.
# 4. Where the checks go (Plan.bend): those that can never fail are erased,
#    and those decided by main's input alone move into its input prologue.
#
# The evaluator is Haskell's transformNoDeferM over its step chain: children
# first (not under a Defer), then the step on the node; applying a closure
# evaluates its body with Env replaced by the argument. The runs of 1 and 2
# are one machine with a mode.

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

# Why sizing failed (SizingFailure). A program can fail in exactly two
# ways, which need different advice (DESIGN.md §4): a recursion's test
# reads input nothing bounds, so no budget helps (UnboundedInput); or the
# test has not stopped within the budget (FuelExhausted). The rest are
# sizing's own failures, each named: an abort on any input (sizeTermM's
# AbortAny), a case haskell-final's sizing threw on (Internal, its message),
# and a sizing form left in the program handed to the runtime (Leftover).
type SizeFail is Data:
  UnboundedInput{+tok: U32}
  FuelExhausted{+tok: U32}
  AbortAny{}
  Internal{+msg: String}
  Leftover{+form: String}

# Whether the erasures past the check analysis's are sound (SIZING-PROOF.md
# §4): Unproven, when the checker did not run; Checked, its verdict on main's
# witness, and the runs it had left. Only a Proven verdict erases: the theorem
# in PROOF.bend covers exactly that.
type Erasure is Data:
  Unproven{}
  Checked{+seen: Ck.Seen}

# What became of the refinement checks. keep: those main still makes, by origin
# key, or None when analyzing them was over budget and all stay; hoisted: those
# its input prologue makes; erasure: what the erasure checker made of the rest.
type Checks is Data:
  Checks{+keep: Maybe<&2, Set()>, +hoisted: Set(), +erasure: Erasure}

# The sized program, as the runnable core: the counts that sized it; expr, what
# the net runs (plain with every chain's bottom erased, where the erasure
# checker proves that); what became of its checks; plain, master's program; and
# master's input prologue, which runs before main on every line.
type Sized is Data:
  Sized{+counts: List<&2, E.TS>, +expr: Co.V, +checks: Checks, +plain: Co.V, +prologue: Maybe<&2, Co.V>}

def checks.keep(c: Checks) -> Maybe<&2, Set()>:
  match c:
    case Checks{keep, h, e}:
      keep

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

def is.sizing(at: E.Site) -> Bool:
  match at:
    case E.AtRecursion{t}:
      True{}
    case _:
      False{}

def aborted.pick(a: Bool, +sb: E.Site, ma: E.X, mb: E.X) -> Bool:
  match a:
    case True{}:
      is.sizing(sb) && data.eq(ma, mb)
    case False{}:
      Bool.not(is.sizing(sb))

def aborted.eq(+sa: E.Site, +sb: E.Site, ma: E.X, mb: E.X) -> Bool:
  aborted.pick(is.sizing(sa), sb, ma, mb)

# The same outcome at the top (ShallowEq1): a superposition of two equal
# outcomes is just the outcome. The program's own aborts are all alike to
# sizing, which only cares that a path aborts; the sizing analysis's aborts
# carry its verdict in their messages, so two of them are the same only when
# the messages are.
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
    case E.XAborted{+sa, ma}:
      match b:
        case E.XAborted{+sb, mb}:
          aborted.eq(sa, sb, ma, mb)
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

# A sizing run's AbortStuck.
def is.stuck(x: E.X) -> Bool:
  match x:
    case E.XAborted{E.AtRecursion{t}, E.XPair{E.XPair{E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}, E.XZero{}}, E.XZero{}}}:
      True{}
    case _:
      False{}

def merge.bs(stuck: Bool, n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  match stuck:
    case True{}:
      a
    case False{}:
      merge.pick(shallow.eq(a, b), n, a, b)

def merge.as(stuck: Bool, n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  match stuck:
    case True{}:
      b
    case False{}:
      merge.bs(is.stuck(b), n, a, b)

# mergeShallow. A stuck path has no value to contribute: it does not exist, or
# the run stops there.
def merge.shallow(n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  merge.as(is.stuck(a), n, a, b)

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

# A gate's result once gates distribute over superpositions: a branch selector,
# or a superposition of them (an aborted gate stays aborted). Choosing a branch
# with one runs no code, so it needs no environment restricted to the inputs
# that make each choice (isSelectorTree).
def is.selector.tree(x: E.X) -> Bool:
  match x:
    case E.XEither{n, a, b}:
      is.selector.tree(a) && is.selector.tree(b)
    case E.XAborted{at, m}:
      True{}
    case other:
      is.gate.selector(other)

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
    case E.XAborted{at, m}:
      GR{False{}, False{}, Some{E.XAborted{at, m}}}
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

def filter.left(yes: Bool, q: String, a: E.X, b: E.X) -> E.X:
  match yes:
    case True{}:
      a
    case False{}:
      E.XEither{Some{q}, a, b}

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
          filter.left(below(q, n), q, a, b)
        case False{}:
          filter.right(below(n, q), q, a, b)
    case None{}:
      E.XEither{None{}, a, b}

def fuel() -> Nat:
  U32.to_nat(4294967295)

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
    case E.XAborted{at, E.XPair{E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}, t}}:
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
      E.XAborted{E.AtRecursion{tok}, E.abort.unsizeable(tok)}
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
      E.XAborted{E.AtRecursion{tok}, E.abort.recursion(tok)}
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
      E.XBarrier{E.fill(E.XGate{}, E.XAny{})}
    case _:
      E.XAny{}

# A step the real evaluator is stuck on (stuckSizingStepM): the sizing analysis's
# AbortStuck, which needs no recursion counted after it. The other runs never
# meet one (master throws).
def stuck.or(m: Mode, +msg: String) -> E.X:
  match m:
    case MSize{}:
      E.XAborted{E.AtRecursion{0}, E.abort.stuck()}
    case _:
      E.XError{msg}

# Structural equality, code by its function index.
def x.eq(a: E.X, b: E.X) -> Bool:
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
          x.eq(a1, b1) && x.eq(a2, b2)
        case _:
          False{}
    case E.XEnv{}:
      match b:
        case E.XEnv{}:
          True{}
        case _:
          False{}
    case E.XSetEnv{x}:
      match b:
        case E.XSetEnv{y}:
          x.eq(x, y)
        case _:
          False{}
    case E.XDefer{fa, x}:
      match b:
        case E.XDefer{fb, y}:
          U32.is_eq(fa, fb)
        case _:
          False{}
    case E.XGate{}:
      match b:
        case E.XGate{}:
          True{}
        case _:
          False{}
    case E.XLeft{x}:
      match b:
        case E.XLeft{y}:
          x.eq(x, y)
        case _:
          False{}
    case E.XRight{x}:
      match b:
        case E.XRight{y}:
          x.eq(x, y)
        case _:
          False{}
    case E.XAborted{sa, ma}:
      match b:
        case E.XAborted{sb, mb}:
          E.site.eq(sa, sb) && x.eq(ma, mb)
        case _:
          False{}
    case E.XVar{p}:
      match b:
        case E.XVar{q}:
          String.eq(p, q)
        case _:
          False{}
    case E.XAny{}:
      match b:
        case E.XAny{}:
          True{}
        case _:
          False{}
    case E.XBarrier{x}:
      match b:
        case E.XBarrier{y}:
          x.eq(x, y)
        case _:
          False{}
    case E.XLefts{n, x}:
      match b:
        case E.XLefts{m, y}:
          U32.is_eq(n, m) && x.eq(x, y)
        case _:
          False{}
    case E.XRights{n, x}:
      match b:
        case E.XRights{m, y}:
          U32.is_eq(n, m) && x.eq(x, y)
        case _:
          False{}
    case _:
      False{}

def abort.free(x: E.X) -> Bool:
  match x:
    case E.XAbort{at}:
      False{}
    case E.XAborted{at, m}:
      False{}
    case E.XPair{a, b}:
      abort.free(a) && abort.free(b)
    case E.XSetEnv{a}:
      abort.free(a)
    case E.XDefer{fi, a}:
      abort.free(a)
    case E.XLeft{a}:
      abort.free(a)
    case E.XRight{a}:
      abort.free(a)
    case E.XEither{n, a, b}:
      abort.free(a) && abort.free(b)
    case E.XBarrier{a}:
      abort.free(a)
    case E.XLefts{n, a}:
      abort.free(a)
    case E.XRights{n, a}:
      abort.free(a)
    case _:
      True{}

def switch.pick(same: Bool, +l: E.X, +r: E.X, +s: E.X) -> E.X:
  match same:
    case True{}:
      l
    case False{}:
      E.XBarrier{E.gate.switch(l, r, s)}

# An undecided gate over its evaluated branches. A gate whose branches are the
# same is that branch, unless its scrutinee can abort: a nested check that
# passes whichever way an input bit goes then reduces to 0 rather than staying a
# residual.
def switch(+l: E.X, +r: E.X, +s: E.X) -> E.X:
  switch.pick(x.eq(l, r) && abort.free(s), l, r, s)

# A gate's own result, flattened (gateSuper): the gate on a where position n is
# 0, and on b where it is a pair, each side flattened to the choices it can make
# under an unknown tag. Flattening the whole superposition under n, as this once
# did, says the left branch is taken where n is 0, which is wrong when a goes
# right or both ways.
def gate.side(+x: E.X) -> E.X:
  fold.gate(None{}, gate.result(x))

def gate.on(+cfg: Cfg, e: E.X) -> E.X:
  match e:
    case E.XZero{}:
      E.do.left()
    case E.XPair{a, b}:
      E.do.right()
    case E.XAborted{at, m}:
      E.XAborted{at, m}
    case E.XAny{}:
      gate.any(mode.of(cfg))
    case E.XVar{p}:
      gate.var(mode.of(cfg), p)
    case E.XEither{+n, +a, +b}:
      merge.shallow(n, gate.side(a), gate.side(b))
    case E.XBarrier{s}:
      match s:
        case E.XSetEnv{E.XPair{E.XSetEnv{E.XPair{E.XGate{}, +s2}}, E.XPair{l, r}}}:
          switch(gate.on(cfg, l), gate.on(cfg, r), s2)
        case other:
          E.XBarrier{E.fill(E.XGate{}, other)}
    case E.XDefer{fi, x}:
      stuck.or(mode.of(cfg), "sizeTermM unhandled gate")
    case _:
      E.XError{"sizeTermM unhandled gate"}

# An abort node, its message evaluated (abortStep): an abort in the message is
# the one that counts, and an aborted value keeps only its message's data.
def abort.on(+at: E.Site, e: E.X) -> E.X:
  match e:
    case E.XAborted{at2, m}:
      E.XAborted{at2, m}
    case other:
      E.XAborted{at, trunc(other)}

def any.on(m: Mode) -> E.X:
  match m:
    case MCheck{}:
      E.XError{"unexpected unsized value applied in a check"}
    case _:
      E.XAny{}

# A barrier applied to e (sameBranchStep, deferredEvalStep): a gate whose
# branches are the same is that branch.
def bar.pick(same: Bool, +l: E.X, +c: E.X, +e: E.X) -> E.X:
  match same:
    case True{}:
      l
    case False{}:
      E.XBarrier{E.fill(c, e)}

def bar.fill(+e: E.X, +c: E.X) -> E.X:
  match e:
    case E.XPair{+l, +r}:
      match c:
        case E.XSetEnv{E.XPair{E.XGate{}, +s}}:
          bar.pick(x.eq(l, r) && abort.free(s), l, c, e)
        case _:
          E.XBarrier{E.fill(c, e)}
    case _:
      E.XBarrier{E.fill(c, e)}

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
    case E.XAborted{at, m}:
      E.XAborted{at, strip(m)}
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

# A function value is neither impossible nor restricting.
def irx.defer(expected: Maybe<&2, Bool>) -> Maybe<&2, IRX>:
  match expected:
    case None{}:
      Some{IRX{Set.new(), Set.new(), E.XZero{}}}
    case _:
      None{}

# extractInputRestrictions' walk. An abort never yields a value, so a gate path
# ending in one is ruled out: a check `if r then c else abort (1, c)` restricts
# r to a pair.
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
        case E.XDefer{fi, b}:
          irx.defer(expected)
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

# `if r then c else abort (1, c)` over an evaluated check result r and value c:
# what a check reduces to once its predicate has run (refinementGate). An
# undecided r leaves a barrier-wrapped gate switch with r itself as the
# scrutinee.
def refinement.gate(+site: U32, r: E.X, +c: E.X) -> E.X:
  match r:
    case E.XZero{}:
      E.XAborted{E.AtCheck{site}, E.XPair{E.XPair{E.XZero{}, E.XZero{}}, trunc(c)}}
    case E.XAborted{at, m}:
      E.XAborted{at, m}
    case E.XPair{a, b}:
      c
    case other:
      E.XBarrier{E.gate.switch(E.XAborted{E.AtCheck{site}, E.XPair{E.XPair{E.XZero{}, E.XZero{}}, trunc(c)}}, c, other)}

# A check met while finding limits reports the zeros and pairs it needs in order
# to pass, and its value goes on unchanged (checkResultStepM); one nested inside
# a check reduces in place, so its restrictions apply only on the gate paths
# where it runs.
def check.result(m: Mode, +site: U32, +r: E.X, +c: E.X) -> R:
  match m:
    case MCheck{}:
      ret(refinement.gate(site, r, c))
    case _:
      irx.result(extract(fuel(), strip(refinement.gate(site, r, E.XZero{})), None{}), c)

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
            case E.XCheck{+site, tc, c}:
              +rtc = eval(f, cfg, JEval{tc, env})
              +rc = eval(f, cfg, JEval{c, env})
              +tw = eval(f, cfg.check(cfg), JStep{E.fill(E.twiddle(), E.XPair{r.v(rc), r.v(rtc)})})
              +ans = eval(f, cfg.check(cfg), JStep{E.XSetEnv{r.v(tw)}})
              plus(rtc, plus(rc, check.result(mode.of(cfg), site, r.v(ans), r.v(rc))))
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
                    case E.XAborted{at, m}:
                      ret(E.XAborted{at, m})
                    case E.XAbort{+at}:
                      ret(abort.on(at, e))
                    case E.XAny{}:
                      ret(any.on(mode.of(cfg)))
                    case E.XEither{+n, +sca, +scb}:
                      merge2(n, eval(f, cfg, JStep{E.fill(sca, filter.side(n, is.selector.tree(sca), True{}, e))}),
                                eval(f, cfg, JStep{E.fill(scb, filter.side(n, is.selector.tree(scb), False{}, e))}))
                    case E.XBarrier{c2}:
                      match c2:
                        case E.XSetEnv{E.XPair{E.XSetEnv{E.XPair{E.XGate{}, +s}}, E.XPair{l, r}}}:
                          ret(switch(r.v(eval(f, cfg, JStep{E.fill(l, e)})), r.v(eval(f, cfg, JStep{E.fill(r, e)})), s))
                        case other:
                          ret(bar.fill(e, other))
                    case E.XZero{}:
                      ret(stuck.or(mode.of(cfg), "sizeTermM unhandled application"))
                    case E.XPair{a, b}:
                      ret(stuck.or(mode.of(cfg), "sizeTermM unhandled application"))
                    case E.XVar{p}:
                      ret(stuck.or(mode.of(cfg), "sizeTermM unhandled application"))
                    case _:
                      bad("sizeTermM unhandled application")
                case E.XAborted{at, m}:
                  ret(E.XAborted{at, m})
                case E.XAny{}:
                  ret(any.on(mode.of(cfg)))
                case E.XEither{n, a, b}:
                  merge2(n, eval(f, cfg, JStep{E.XSetEnv{a}}), eval(f, cfg, JStep{E.XSetEnv{b}}))
                case E.XBarrier{x}:
                  match x:
                    case E.XSetEnv{E.XPair{E.XSetEnv{E.XPair{E.XGate{}, +s}}, E.XPair{l, r}}}:
                      ret(switch(r.v(eval(f, cfg, JStep{E.XSetEnv{l}})), r.v(eval(f, cfg, JStep{E.XSetEnv{r}})), s))
                    case other:
                      ret(E.XBarrier{E.XSetEnv{other}})
                case E.XZero{}:
                  ret(stuck.or(mode.of(cfg), "sizeTermM unhandled SetEnv"))
                case E.XDefer{fi, d}:
                  ret(stuck.or(mode.of(cfg), "sizeTermM unhandled SetEnv"))
                case _:
                  bad("sizeTermM unhandled SetEnv")
            case E.XLeft{v}:
              match v:
                case E.XZero{}:
                  ret(E.XZero{})
                case E.XPair{a, b}:
                  ret(a)
                case E.XAborted{at, m}:
                  ret(E.XAborted{at, m})
                case E.XVar{p}:
                  ret(cfg.res(cfg, p ++ "L"))
                case E.XAny{}:
                  ret(E.XAny{})
                case E.XEither{n, a, b}:
                  merge2(n, eval(f, cfg, JStep{E.XLeft{a}}), eval(f, cfg, JStep{E.XLeft{b}}))
                case E.XBarrier{x}:
                  match x:
                    case E.XSetEnv{E.XPair{E.XSetEnv{E.XPair{E.XGate{}, +s}}, E.XPair{l, r}}}:
                      ret(switch(r.v(eval(f, cfg, JStep{E.XLeft{l}})), r.v(eval(f, cfg, JStep{E.XLeft{r}})), s))
                    case E.XLefts{k, y}:
                      ret(E.XBarrier{E.XLefts{(k + 1 : U32), y}})
                    case other:
                      ret(E.XBarrier{E.XLefts{1, other}})
                case E.XDefer{fi, d}:
                  ret(stuck.or(mode.of(cfg), "sizeTermM unhandled Left"))
                case _:
                  bad("sizeTermM unhandled Left")
            case E.XRight{v}:
              match v:
                case E.XZero{}:
                  ret(E.XZero{})
                case E.XPair{a, b}:
                  ret(b)
                case E.XAborted{at, m}:
                  ret(E.XAborted{at, m})
                case E.XVar{p}:
                  ret(cfg.res(cfg, p ++ "R"))
                case E.XAny{}:
                  ret(E.XAny{})
                case E.XEither{n, a, b}:
                  merge2(n, eval(f, cfg, JStep{E.XRight{a}}), eval(f, cfg, JStep{E.XRight{b}}))
                case E.XBarrier{x}:
                  match x:
                    case E.XSetEnv{E.XPair{E.XSetEnv{E.XPair{E.XGate{}, +s}}, E.XPair{l, r}}}:
                      ret(switch(r.v(eval(f, cfg, JStep{E.XRight{l}})), r.v(eval(f, cfg, JStep{E.XRight{r}})), s))
                    case E.XRights{k, y}:
                      ret(E.XBarrier{E.XRights{(k + 1 : U32), y}})
                    case other:
                      ret(E.XBarrier{E.XRights{1, other}})
                case E.XDefer{fi, d}:
                  ret(stuck.or(mode.of(cfg), "sizeTermM unhandled Right"))
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
    case E.XCheck{s, a, b}:
      E.XCheck{s, convert.is(a), convert.is(b)}
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
    case E.XCheck{s, a, b}:
      E.XCheck{s, naked.envs(a), naked.envs(b)}
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
      Some{FuelExhausted{fail.tok(E.to.int(t))}}
    case E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}:
      Some{AbortAny{}}
    case E.XPair{E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}, t}:
      Some{UnboundedInput{fail.tok(E.to.int(t))}}
    case _:
      None{}

# Sizing's own failures outweigh the program's; of the program's, an
# unbounded input outweighs an exhausted budget.
def fail.pick(x: SizeFail, y: SizeFail) -> SizeFail:
  match x:
    case UnboundedInput{t}:
      match y:
        case UnboundedInput{u}:
          UnboundedInput{t}
        case FuelExhausted{u}:
          UnboundedInput{t}
        case other:
          other
    case FuelExhausted{t}:
      match y:
        case FuelExhausted{u}:
          FuelExhausted{t}
        case other:
          other
    case own:
      own

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

# Only the sizing analysis's own aborts say anything about sizing; the program's
# are just one of the outcomes some inputs have.
def fail.at(at: E.Site, m: E.X) -> Maybe<&2, SizeFail>:
  match at:
    case E.AtRecursion{t}:
      fail.of.abort(m)
    case _:
      None{}

# The first failure left in the run's result (foldAborted). Code under a
# Defer holds none.
def fold.aborted(v: E.X) -> Maybe<&2, SizeFail>:
  match v:
    case E.XAborted{at, m}:
      fail.at(at, m)
    case E.XError{msg}:
      Some{Internal{msg}}
    case E.XPair{a, b}:
      fail.or(fold.aborted(a), fold.aborted(b))
    case E.XEither{n, a, b}:
      fail.or(fold.aborted(a), fold.aborted(b))
    case _:
      None{}

# The erasure checker's budget: the evaluation steps its runs may take in
# all (Check.bend), and how deep its input tree may grow.
def check.work() -> Nat:
  U32.to_nat(268435456)

def check.depth() -> Nat:
  U32.to_nat(100000)

# The erasure checker on main's witness, watching the sites the net's program
# erases (every check main no longer makes, and every chain's bottom), on the
# inputs the prologue passes.
def erasure.run(check: Bool, +left: Set(), +counts: List<&2, E.TS>, +x: E.X, g: Maybe<&2, E.X>) -> Erasure:
  match check:
    case True{}:
      Checked{Ck.check(check.depth(), Sm.fuel(), Sm.Pol{Sm.Watch{}, Ck.erasable(x, left)}, Ck.witness(counts, x), g, check.work())}
    case False{}:
      Unproven{}

# Whether the checker proved the erasures: then, and only then, they are made.
def erased(e: Erasure) -> Bool:
  match e:
    case Checked{s}:
      match s:
        case Ck.Seen{v, left}:
          match v:
            case Ck.Proven{}:
              True{}
            case _:
              False{}
    case Unproven{}:
      False{}

# Each recursion site becomes a chain of its count of steps (setSizes); one
# never reached gets one. inert: the chains' bottoms are proven dead.
def set.sizes(+counts: List<&2, E.TS>, +inert: Bool, x: E.X) -> E.X:
  match x:
    case E.XStub{+tok, y}:
      E.sized.chain(E.count.of(counts, tok), inert)
    case E.XPair{a, b}:
      E.XPair{set.sizes(counts, inert, a), set.sizes(counts, inert, b)}
    case E.XSetEnv{a}:
      E.XSetEnv{set.sizes(counts, inert, a)}
    case E.XDefer{fi, a}:
      E.XDefer{fi, set.sizes(counts, inert, a)}
    case E.XLeft{a}:
      E.XLeft{set.sizes(counts, inert, a)}
    case E.XRight{a}:
      E.XRight{set.sizes(counts, inert, a)}
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

# The sized program, from cm (main applied to the input): each recursion
# its chain, and the checks left to run time (left; None for every check)
# resolved.
def program(+counts: List<&2, E.TS>, +left: Maybe<&2, Set()>, +inert: Bool, +cm: E.X, cap: Bool) -> E.X:
  match cap:
    case True{}:
      uncap(set.sizes(counts, inert, E.resolve.checks(left, cm)))
    case False{}:
      set.sizes(counts, inert, E.resolve.checks(left, cm))

# The sites of the checks main still makes.
def left.of(kvs: List<&2, Sigma<&2, &2, String, _ => L.Origin>>, +keep: Maybe<&2, Set()>, +acc: Set()) -> Set():
  match kvs:
    case Nil{}:
      acc
    case Con{kv, rest}:
      match kv:
        case (+site, +o):
          left.of(rest, keep, Bool.pick(Set(), Pl.kept(keep, o), Set.add(acc, site), acc))

def plan.keep(p: Pl.Plan) -> Maybe<&2, Set()>:
  match p:
    case Pl.Plan{keep, h, g}:
      keep

def plan.hoisted(p: Pl.Plan) -> Set():
  match p:
    case Pl.Plan{keep, h, g}:
      h

def plan.prologue(p: Pl.Plan) -> Maybe<&2, Co.V>:
  match p:
    case Pl.Plan{keep, h, g}:
      g

# The prologue as the erasure checker runs it.
def guard.sem(g: Maybe<&2, Co.V>) -> Maybe<&2, E.X>:
  match g:
    case None{}:
      None{}
    case Some{v}:
      Some{Sm.of.core(v)}

# Where the erasure checker proves the net's program, its core; else master's.
def net.expr(proven: Bool, +os: Map<&2, L.Origin>, +counts: List<&2, E.TS>, +left: Set(), +cm: E.X, +cap: Bool, +plain: Co.V) -> Result<&2, &2, String, Co.V>:
  match proven:
    case True{}:
      E.core(os, program(counts, Some{left}, True{}, cm, cap))
    case False{}:
      Done{plain}

def cored(+counts: List<&2, E.TS>, cs: Checks, r: Result<&2, &2, String, Co.V>, +plain: Co.V, +g: Maybe<&2, Co.V>) -> Result<&2, &2, SizeFail, Sized>:
  match r:
    case Done{v}:
      Done{Sized{counts, v, cs, plain, g}}
    case Fail{form}:
      Fail{Leftover{form}}

def with.erasure(+e: Erasure, +p: Pl.Plan, +plain: Co.V, +os: Map<&2, L.Origin>, +counts: List<&2, E.TS>, +left: Set(), +cm: E.X, +cap: Bool) -> Result<&2, &2, SizeFail, Sized>:
  cored(counts, Checks{plan.keep(p), plan.hoisted(p), e}, net.expr(erased(e), os, counts, left, cm, cap, plain), plain, plan.prologue(p))

def with.left(+left: Set(), +p: Pl.Plan, +plain: Co.V, +os: Map<&2, L.Origin>, +counts: List<&2, E.TS>, +cm: E.X, +x: E.X, +cap: Bool, +check: Bool) -> Result<&2, &2, SizeFail, Sized>:
  with.erasure(erasure.run(cap && check, left, counts, x, guard.sem(plan.prologue(p))), p, plain, os, counts, left, cm, cap)

def with.plan(+p: Pl.Plan, +v0: Co.V, +os: Map<&2, L.Origin>, +counts: List<&2, E.TS>, +cm: E.X, +x: E.X, +cap: Bool, +check: Bool) -> Result<&2, &2, SizeFail, Sized>:
  with.left(left.of(Map.to_list(&2, L.Origin, os), plan.keep(p), Set.new()), p, Pl.erased(p, v0), os, counts, cm, x, cap, check)

# The analysis is of a main, so of a capped term, and only when something reads
# its answer: `--certificate` needs the counts alone (master's laziness).
def plan.if(cap: Bool, +v: Co.V) -> Pl.Plan:
  match cap:
    case True{}:
      Pl.plan(v)
    case False{}:
      Pl.plan.none()

# What a compile will read: the counts alone (`--certificate`); master's program
# too (a plain run); or the net's as well, which is what the erasure checker is
# for.
type Want is Data:
  WantCounts{}
  WantPlain{}
  WantNet{}

def wants.plan(w: Want) -> Bool:
  match w:
    case WantCounts{}:
      False{}
    case _:
      True{}

def wants.check(w: Want) -> Bool:
  match w:
    case WantNet{}:
      True{}
    case _:
      False{}

# Master's program, every check in it, then where the checks go, and what the
# net runs.
def planned(r: Result<&2, &2, String, Co.V>, +os: Map<&2, L.Origin>, +counts: List<&2, E.TS>, +cm: E.X, +x: E.X, +cap: Bool, +check: Bool) -> Result<&2, &2, SizeFail, Sized>:
  match r:
    case Fail{form}:
      Fail{Leftover{form}}
    case Done{+v}:
      with.plan(plan.if(cap, v), v, os, counts, cm, x, cap, check)

def tidy(+os: Map<&2, L.Origin>, m: Maybe<&2, SizeFail>, +run: R, +cm: E.X, +x: E.X, +cap: Bool, +want: Want) -> Result<&2, &2, SizeFail, Sized>:
  match m:
    case Some{fail}:
      Fail{fail}
    case None{}:
      planned(E.core(os, program(r.s(run), None{}, False{}, cm, cap)), os, r.s(run), cm, x, cap && wants.plan(want), wants.check(want))

def main.run.from(+os: Map<&2, L.Origin>, +max: U32, +cm: E.X, +lim: R, +mx: E.X, +x: E.X, +cap: Bool, +want: Want) -> Result<&2, &2, SizeFail, Sized>:
  +run = eval(fuel(), {Cfg{MSize{}, r.z(lim), max} : Cfg}, JEval{E.remove.checks(mx), E.XZero{}})
  tidy(os, fold.aborted(r.v(run)), run, cm, x, cap, want)

def main.run(+os: Map<&2, L.Origin>, +max: U32, +cm: E.X, +lim: R, +x: E.X, +cap: Bool, +want: Want) -> Result<&2, &2, SizeFail, Sized>:
  match cap:
    case True{}:
      main.run.from(os, max, cm, lim, E.app(x, initial.input(fuel(), Set.to_list(r.p(lim)), in.st(Set.to_list(r.p(lim)), ""))), x, cap, want)
    case False{}:
      main.run.from(os, max, cm, lim, naked.envs(x), x, cap, want)

def capped(+x: E.X, cap: Bool) -> E.X:
  match cap:
    case True{}:
      E.app(x, E.XVar{""})
    case False{}:
      x

# sizeTermM and checkPlan: size every recursion in t, cap it (apply it to the
# symbolic input) as main is, and give the sized program, at a budget of max
# unrollings per site, as far as want says.
def size.checked(+max: U32, +cap: Bool, +t: T.C, +want: Want) -> Result<&2, &2, SizeFail, Sized>:
  +x = E.of.term3(t)
  +cm = capped(x, cap)
  main.run(E.origins(t), max, cm, eval(fuel(), Cfg{MLimits{}, Set.new(), max}, JEval{convert.is(cm), E.XZero{}}), x, cap, want)

def size(+max: U32, +cap: Bool, +t: T.C) -> Result<&2, &2, SizeFail, Sized>:
  size.checked(max, cap, t, WantNet{})

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
    case T.CCheck{a, c, s, x, y}:
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
    case FuelExhausted{+tok}:
      "could not size " ++ site.render(tok, site.loc(t, tok)) ++ ":\n"
        ++ "  its test had still not stopped after " ++ U32.show((max + 1 : U32)) ++ " unrollings.\n"
        ++ "  Either it needs a deeper recursion than the sizing budget allows, or\n"
        ++ "  its test never stops."
    case UnboundedInput{+tok}:
      "could not size " ++ site.render(tok, site.loc(t, tok)) ++ ":\n"
        ++ "  its test depends on input that nothing bounds, so no finite iteration\n"
        ++ "  count can be proven for it. Constrain that input with a refinement\n"
        ++ "  (`x : somePredicate`) before recursing on it."
    case AbortAny{}:
      "sizeTermM AbortAny hit"
    case Internal{msg}:
      msg
    case Leftover{form}:
      "sizing left " ++ form ++ " in the compiled program (a bug in sizing)"
