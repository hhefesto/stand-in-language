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
# 1. The run: input positions stand for unknown data, unbounded; a gate on
#    one explores both branches as a superposition (EitherPF); each
#    recursion unrolls one step at a time, recording every depth whose test
#    it reaches (SizeStageF). A test that depends on input nothing bounds,
#    or a recursion past the budget, fails sizing.
# 2. A refinement check met on the way is sized as compiled, over the value
#    that reaches it, and the run goes on with that value narrowed to what
#    passing the check requires (narrowChecked): its check function runs
#    over the value symbolically, to learn which input positions must be 0
#    and which pairs, and the positions the value holds are bounded so
#    (BoundedF). A check bounds exactly the computation its value flows
#    into: only the inputs that pass it reach there.
# 3. Each recursion site becomes a chain of that many steps
#    (sizedRecursionChain), over the program as written.
# 4. Where the checks go (Plan.bend): those that can never fail are erased,
#    and those decided by main's input alone move into its input prologue.
#
# The evaluator is Haskell's transformNoDeferM over its step chain: children
# first (not under a Defer), then the step on the node; applying a closure
# evaluates its body with Env replaced by the argument. The run and a check's
# function (refinementCheckStep) are one machine with a mode.

# Which run: the sizing run, or a refinement check's function inside it.
type Mode is Data:
  MSize{}
  MCheck{}

# max: the budget of unrollings per site, which a check's function also
# unfolds by.
type Cfg is Data:
  Cfg{+mode: Mode, +max: U32}

# A result: the value, and the counts found (SizedRecursion).
type R is Data:
  R{+v: E.X, +s: List<&2, E.TS>}

# A check met: run (JCheck, m the run's mode), then, while sizing, what its
# sized run gave (JChecked: checked, the first failure in it, and whether
# the checked value reads the input).
type Job is Data:
  JEval{+t: E.X, +env: E.X}
  JStep{+t: E.X}
  JCheck{+m: Mode, +site: U32, +tc: E.X, +c: E.X}
  JChecked{+site: U32, +tc: E.X, +c: E.X, +checked: E.X, +fail: Maybe<&2, SizeFail>, +reads: Bool}

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
# witness, and the runs it had left; first: None when that verdict is on every
# check main makes, the ones left to run time too, else that run's verdict, and
# seen is the run on the sites the net's program erases anyway. Only a Proven verdict erases: the
# theorem in PROOF.bend covers exactly that.
type Erasure is Data:
  Unproven{}
  Checked{+seen: Ck.Seen, +first: Maybe<&2, Ck.Verdict>}

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
  R{v, []}

def r.v(r: R) -> E.X:
  match r:
    case R{v, s}:
      v

# r's findings added to q's result.
def plus(r: R, q: R) -> R:
  match r:
    case R{v1, s1}:
      match q:
        case R{v2, s2}:
          R{v2, ts.merge(s1, s2)}

def with.value(r: R, +v: E.X) -> R:
  match r:
    case R{v1, s}:
      R{v, s}

def pair.of(ra: R, rb: R) -> R:
  match ra:
    case R{va, sa}:
      match rb:
        case R{vb, sb}:
          R{E.XPair{va, vb}, ts.merge(sa, sb)}

def staged(sr: List<&2, E.TS>, r: R) -> R:
  match r:
    case R{v, s}:
      R{v, ts.merge(sr, s)}

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

def bounded.pick(zero: Bool, free: Bool, +zeros: Set(), +p: String) -> E.X:
  match zero:
    case True{}:
      E.XZero{}
    case False{}:
      match free:
        case True{}:
          E.XVar{p}
        case False{}:
          E.XBounded{zeros, p}

# An input position under the zeros a refinement check requires
# (boundedInput): 0 where one is required, unbounded where none is required
# at or below it, and bounded otherwise.
def bounded.input(+zeros: Set(), +p: String) -> E.X:
  bounded.pick(has(zeros, p), unbounded(zeros, p), zeros, p)

# Steps that need no further evaluation
# -------------------------------------

def cfg.max(cfg: Cfg) -> U32:
  match cfg:
    case Cfg{mode, max}:
      max

def cfg.check(cfg: Cfg) -> Cfg:
  match cfg:
    case Cfg{mode, max}:
      Cfg{MCheck{}, max}

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

# A value the program aborts on, not the sizing analysis.
def is.program.abort(x: E.X) -> Bool:
  match x:
    case E.XAborted{at, m}:
      Bool.not(is.sizing(at))
    case _:
      False{}

def merge.pb(abort: Bool, n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  match abort:
    case True{}:
      a
    case False{}:
      merge.pick(shallow.eq(a, b), n, a, b)

def merge.pa(abort: Bool, n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  match abort:
    case True{}:
      b
    case False{}:
      merge.pb(is.program.abort(b), n, a, b)

def merge.bs(stuck: Bool, n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  match stuck:
    case True{}:
      a
    case False{}:
      merge.pa(is.program.abort(a), n, a, b)

def merge.as(stuck: Bool, n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  match stuck:
    case True{}:
      b
    case False{}:
      merge.bs(is.stuck(b), n, a, b)

# mergeShallow. A stuck path has no value to contribute: it does not exist, or
# the run stops there. Nor has a path the program aborts on: what follows an
# aborted value only passes it on, so it needs no count, and kept as an
# alternative the abort multiplies through all that follows (a case with no
# default yields it beside every value it matches).
def merge.shallow(n: Maybe<&2, String>, +a: E.X, +b: E.X) -> E.X:
  merge.as(is.stuck(a), n, a, b)

def merge2(n: Maybe<&2, String>, ra: R, rb: R) -> R:
  match ra:
    case R{va, sa}:
      match rb:
        case R{vb, sb}:
          R{merge.shallow(n, va, vb), ts.merge(sa, sb)}

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
    case E.XBounded{zs, p}:
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

# A gate on a value the program aborts on selects nothing worth sizing
# (mergeShallow).
def fold.both(abort: Bool, +x: E.X, +y: E.X) -> E.X:
  match abort:
    case True{}:
      y
    case False{}:
      E.XEither{None{}, x, y}

def fold.pick(o: Maybe<&2, E.X>, bp: Maybe<&2, E.X>) -> E.X:
  match o:
    case Some{+x}:
      match bp:
        case Some{y}:
          fold.both(is.program.abort(x), x, y)
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

def test.bounded(ub: Bool, +zeros: Set(), +tok: U32, +p: String) -> E.X:
  match ub:
    case True{}:
      E.XAborted{E.AtRecursion{tok}, E.abort.unsizeable(tok)}
    case False{}:
      E.XBounded{zeros, p}

def test.of(n: Maybe<&2, String>, +na: E.X, +nb: E.X) -> E.X:
  test.pick(n, is.unsizeable(na), is.unsizeable(nb), na, nb)

# A recursion's test value while sizing (unsizedTestIndexed,
# unsizedTestSuper): an input position nothing bounds cannot be sized.
def size.test(+tok: U32, v: E.X) -> E.X:
  match v:
    case E.XVar{+p}:
      E.XAborted{E.AtRecursion{tok}, E.abort.unsizeable(tok)}
    case E.XBounded{+zs, +p}:
      test.bounded(unbounded(zs, p), zs, tok, p)
    case E.XEither{n, a, b}:
      test.of(n, size.test(tok, a), size.test(tok, b))
    case other:
      other

# A recursion's test value inside a check's function (unfoldRecursion): a
# decided one goes on; one that reads the input is unknown.
def check.test(v: E.X) -> E.X:
  match v:
    case E.XZero{}:
      E.XZero{}
    case E.XPair{a, b}:
      E.XPair{a, b}
    case _:
      E.XAny{}

def unsized.test(m: Mode, +tok: U32, v: E.X) -> E.X:
  match m:
    case MSize{}:
      size.test(tok, v)
    case MCheck{}:
      check.test(v)

# What a check's function makes of a form sizing would fail on: an unknown.
def unexpected(m: Mode, +msg: String) -> E.X:
  match m:
    case MSize{}:
      E.XError{msg}
    case MCheck{}:
      E.XAny{}

# A recursion placeholder meets its {t, r, b}: the first unrolling, its test
# marked (unsizedStepM''' on UnsizedStubF). Inside a check's function a
# recursion unfolds as it does while sizing, so a check counting a constant
# (Num 2, Vector 9, d2c 57 left x) restricts the input it reads
# (unfoldRecursion).
def stub.expand(m: Mode, +tok: U32, v: E.X) -> E.X:
  match v:
    case E.XPair{E.XPair{E.XPair{E.XDefer{sid, tf}, e}, rest}, x}:
      E.XPair{E.XDefer{Co.step.rfa(), E.step.body(tok, 1)},
              E.XPair{E.XPair{E.XDefer{sid, E.XTest{tok, tf}}, e}, rest}}
    case _:
      unexpected(m, "unsizedStepM''' unexpected oracle operand")

def step.next(m: Mode, +tok: U32, +n: U32, v: E.X) -> E.X:
  match v:
    case E.XPair{x, trb}:
      E.XPair{E.XDefer{Co.step.rfa(), E.step.body(tok, (n + 1 : U32))}, trb}
    case _:
      unexpected(m, "unsizedStepM''' unexpected step operand")

# Past the budget: sizing fails; inside a check's function, the result is
# unknown.
def step.over(over: Bool, m: Mode, +tok: U32, +n: U32, v: E.X) -> E.X:
  match over:
    case True{}:
      match m:
        case MSize{}:
          E.XAborted{E.AtRecursion{tok}, E.abort.recursion(tok)}
        case MCheck{}:
          E.XAny{}
    case False{}:
      step.next(m, tok, n, v)

# The next unrolling, unless past the budget.
def step.expand(m: Mode, +max: U32, +tok: U32, +n: U32, v: E.X) -> E.X:
  step.over(U32.is_gt(n, max), m, tok, n, v)

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
    case Cfg{mode, max}:
      mode

# A gate on an input position: both branches while sizing; deferred behind
# a barrier inside a check. A gate on an unknown is an unknown, rather than a
# residual whose branches both run: an undecided recursion test must stop
# unfolding.
def gate.var(m: Mode, +p: String) -> E.X:
  match m:
    case MSize{}:
      E.XEither{Some{p}, E.do.left(), E.do.right()}
    case MCheck{}:
      E.XBarrier{E.fill(E.XGate{}, E.XVar{p})}

# A step the real evaluator is stuck on (stuckSizingStepM): the sizing analysis's
# AbortStuck, which needs no recursion counted after it. A check's function
# never meets one (master throws).
def stuck.or(m: Mode, +msg: String) -> E.X:
  match m:
    case MSize{}:
      E.XAborted{E.AtRecursion{0}, E.abort.stuck()}
    case _:
      E.XError{msg}

def all.in(xs: List<&2, String>, +s: Set()) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      has(s, x) && all.in(rest, s)

def set.eq(+a: Set(), +b: Set()) -> Bool:
  U32.is_eq(U32.from_nat(Map.size(&2, Unit, a)), U32.from_nat(Map.size(&2, Unit, b))) && all.in(Set.to_list(a), b)

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
    case E.XBounded{za, p}:
      match b:
        case E.XBounded{zb, q}:
          String.eq(p, q) && set.eq(za, zb)
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
      E.XAny{}
    case E.XVar{p}:
      gate.var(mode.of(cfg), p)
    case E.XBounded{zs, p}:
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

# Refinement checks: what passing one requires
# --------------------------------------------

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

def inter.go(xs: List<&2, String>, +b: Set(), +acc: Set()) -> Set():
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      inter.go(rest, b, Bool.pick(Set(), has(b, x), Set.add(acc, x), acc))

def inter(+a: Set(), +b: Set()) -> Set():
  inter.go(Set.to_list(a), b, Set.new())

# An input taking either branch is restricted only by what both require.
def irx.both(a: IRX, b: IRX) -> IRX:
  match a:
    case IRX{za, pa, va}:
      match b:
        case IRX{zb, pb, vb}:
          IRX{inter(za, zb), inter(pa, pb), va}

def irx.combine(nl: Maybe<&2, IRX>, nr: Maybe<&2, IRX>, es: Maybe<&2, IRX>) -> Maybe<&2, IRX>:
  match nl:
    case Some{a}:
      match nr:
        case Some{b}:
          match es:
            case Some{s}:
              Some{irx.add(irx.both(a, b), s)}
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
# r to a pair. An unknown value (what the analysis could not follow, such as a
# recursion whose test reads the input) may be either, so a path through it is
# possible and says nothing about the input.
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
        case E.XAny{}:
          Some{IRX{Set.new(), Set.new(), E.XAny{}}}
        case E.XSetEnv{E.XPair{E.XSetEnv{E.XPair{E.XGate{}, s}}, E.XPair{l, r}}}:
          +nl = extract(f, l, expected)
          +nr = extract(f, r, expected)
          irx.combine(nl, nr, extract(f, s, irx.expect(nl, nr)))
        case _:
          None{}

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

# What passing a check requires of the input, from its answer r: the zeros
# and pairs (checkRestrictions; only whether the check passes matters, not
# the value it guards).
def check.restrictions(+site: U32, r: E.X) -> Maybe<&2, IRX>:
  extract(fuel(), strip(refinement.gate(site, r, E.XZero{})), None{})

# Whether a value of the run holds an input position.
def reads.input(x: E.X) -> Bool:
  match x:
    case E.XVar{p}:
      True{}
    case E.XBounded{zs, p}:
      True{}
    case E.XPair{a, b}:
      reads.input(a) || reads.input(b)
    case E.XSetEnv{a}:
      reads.input(a)
    case E.XDefer{fi, a}:
      reads.input(a)
    case E.XLeft{a}:
      reads.input(a)
    case E.XRight{a}:
      reads.input(a)
    case E.XAborted{at, m}:
      reads.input(m)
    case E.XEither{n, a, b}:
      reads.input(a) || reads.input(b)
    case E.XTest{tok, a}:
      reads.input(a)
    case E.XStub{tok, a}:
      reads.input(a)
    case E.XStage{sr, a}:
      reads.input(a)
    case E.XCheck{site, a, b}:
      reads.input(a) || reads.input(b)
    case E.XStep{tok, n, a}:
      reads.input(a)
    case _:
      False{}

# A value of the run as a check's function reads it (toCheckValue): it has no
# superpositions, one being an unknown there, and a bounded input position
# reads as the position, which only loses what bounds it.
def to.check(x: E.X) -> E.X:
  match x:
    case E.XBounded{zs, p}:
      E.XVar{p}
    case E.XEither{n, a, b}:
      E.XAny{}
    case E.XPair{a, b}:
      E.XPair{to.check(a), to.check(b)}
    case E.XSetEnv{a}:
      E.XSetEnv{to.check(a)}
    case E.XDefer{fi, a}:
      E.XDefer{fi, to.check(a)}
    case E.XLeft{a}:
      E.XLeft{to.check(a)}
    case E.XRight{a}:
      E.XRight{to.check(a)}
    case E.XAborted{at, m}:
      E.XAborted{at, to.check(m)}
    case E.XTest{tok, a}:
      E.XTest{tok, to.check(a)}
    case E.XStub{tok, a}:
      E.XStub{tok, to.check(a)}
    case E.XStage{sr, a}:
      E.XStage{sr, to.check(a)}
    case E.XCheck{site, a, b}:
      E.XCheck{site, to.check(a), to.check(b)}
    case E.XStep{tok, n, a}:
      E.XStep{tok, n, to.check(a)}
    case other:
      other

# An input position narrowed to what the restrictions allow it: a pair where a
# pair is required at or below it (split), and otherwise the position under
# the zeros required of it (boundedInput).
def shape(+fuel: Nat, zero: Bool, split: Bool, +zeros: Set(), +pairs: List<&2, String>, +p: String) -> E.X:
  match fuel:
    case 0n:
      bounded.input(zeros, p)
    case 1n+f:
      match zero:
        case True{}:
          bounded.input(zeros, p)
        case False{}:
          match split:
            case True{}:
              E.XPair{shape(f, has(zeros, p ++ "L"), any.below(pairs, p ++ "L"), zeros, pairs, p ++ "L"),
                      shape(f, has(zeros, p ++ "R"), any.below(pairs, p ++ "R"), zeros, pairs, p ++ "R")}
            case False{}:
              bounded.input(zeros, p)

def shape.at(+zeros: Set(), +pairs: List<&2, String>, +p: String) -> E.X:
  shape(fuel(), has(zeros, p), any.below(pairs, p), zeros, pairs, p)

# Each input position in a value, narrowed (narrowTo); a bounded position adds
# its own zeros to the restrictions'.
def narrow.to(+zeros: Set(), +pairs: List<&2, String>, x: E.X) -> E.X:
  match x:
    case E.XVar{+p}:
      shape.at(zeros, pairs, p)
    case E.XBounded{zs, +p}:
      shape.at(union(zeros, zs), pairs, p)
    case E.XPair{a, b}:
      E.XPair{narrow.to(zeros, pairs, a), narrow.to(zeros, pairs, b)}
    case E.XSetEnv{a}:
      E.XSetEnv{narrow.to(zeros, pairs, a)}
    case E.XDefer{fi, a}:
      E.XDefer{fi, narrow.to(zeros, pairs, a)}
    case E.XLeft{a}:
      E.XLeft{narrow.to(zeros, pairs, a)}
    case E.XRight{a}:
      E.XRight{narrow.to(zeros, pairs, a)}
    case E.XAborted{at, m}:
      E.XAborted{at, narrow.to(zeros, pairs, m)}
    case E.XEither{n, a, b}:
      E.XEither{n, narrow.to(zeros, pairs, a), narrow.to(zeros, pairs, b)}
    case E.XTest{tok, a}:
      E.XTest{tok, narrow.to(zeros, pairs, a)}
    case E.XStub{tok, a}:
      E.XStub{tok, narrow.to(zeros, pairs, a)}
    case E.XStage{sr, a}:
      E.XStage{sr, narrow.to(zeros, pairs, a)}
    case E.XCheck{site, a, b}:
      E.XCheck{site, narrow.to(zeros, pairs, a), narrow.to(zeros, pairs, b)}
    case E.XStep{tok, n, a}:
      E.XStep{tok, n, narrow.to(zeros, pairs, a)}
    case other:
      other

def narrow.nonempty(nothing: Bool, +z: Set(), +p: Set(), +c: E.X) -> E.X:
  match nothing:
    case True{}:
      c
    case False{}:
      narrow.to(z, Set.to_list(p), c)

# The checked value narrowed to what passing the check requires, or as it is
# when the check requires nothing (narrowChecked).
def narrowed(m: Maybe<&2, IRX>, +c: E.X) -> E.X:
  match m:
    case None{}:
      c
    case Some{r}:
      match r:
        case IRX{+z, +p, v}:
          narrow.nonempty(U32.is_eq(U32.from_nat(Map.size(&2, Unit, z)), 0) && U32.is_eq(U32.from_nat(Map.size(&2, Unit, p)), 0), z, p, c)

# Sizing failures
# ----------------

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
              plus(rtc, plus(rc, eval(f, cfg, JCheck{mode.of(cfg), site, r.v(rtc), r.v(rc)})))
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
        # A check inside a check's function reduces in place
        # (refinementGate), so its restrictions apply only on the gate paths
        # where it runs. One met while sizing is sized as compiled, over every
        # value that reaches it (checkStep).
        case JCheck{m, +site, +tc, +c}:
          match m:
            case MCheck{}:
              +tw = eval(f, cfg, JStep{E.fill(E.twiddle(), E.XPair{c, tc})})
              +ans = eval(f, cfg, JStep{E.XSetEnv{r.v(tw)}})
              ret(refinement.gate(site, r.v(ans), c))
            case MSize{}:
              +chk = eval(f, cfg, JStep{E.check.of(True{}, site, tc, c)})
              with.value(chk, r.v(eval(f, cfg, JChecked{site, tc, c, r.v(chk), fold.aborted(r.v(chk)), reads.input(c)})))
        # A check that fails wherever it runs is its abort, and one that cannot
        # be sized its verdict. Otherwise what follows it runs on the value
        # narrowed to what passing it requires (narrowChecked): the inputs it
        # fails on abort there, needing no count after it, so its aborts are
        # left behind; carried on, they would multiply through everything after
        # the check. The check's function runs over the value symbolically.
        case JChecked{+site, +tc, +c, checked, fail, reads}:
          match checked:
            case E.XAborted{at, msg}:
              ret(E.XAborted{at, msg})
            case other:
              match fail:
                case Some{x}:
                  ret(other)
                case None{}:
                  match reads:
                    case False{}:
                      ret(c)
                    case True{}:
                      +tw = eval(f, cfg.check(cfg), JStep{E.fill(E.twiddle(), E.XPair{to.check(c), to.check(tc)})})
                      +ans = eval(f, cfg.check(cfg), JStep{E.XSetEnv{r.v(tw)}})
                      ret(narrowed(check.restrictions(site, r.v(ans)), c))
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
                      ret(E.XAny{})
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
                    case E.XBounded{zs, p}:
                      ret(stuck.or(mode.of(cfg), "sizeTermM unhandled application"))
                    case _:
                      bad("sizeTermM unhandled application")
                case E.XAborted{at, m}:
                  ret(E.XAborted{at, m})
                case E.XAny{}:
                  ret(E.XAny{})
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
                  ret(E.XVar{p ++ "L"})
                case E.XBounded{+zs, p}:
                  ret(bounded.input(zs, p ++ "L"))
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
                  ret(E.XVar{p ++ "R"})
                case E.XBounded{+zs, p}:
                  ret(bounded.input(zs, p ++ "R"))
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
              ret(unsized.test(mode.of(cfg), tok, v))
            case E.XStub{tok, v}:
              ret(stub.expand(mode.of(cfg), tok, v))
            case E.XStep{tok, n, v}:
              ret(step.expand(mode.of(cfg), cfg.max(cfg), tok, n, v))
            case other:
              ret(other)

# The runs
# --------

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

# The erasure checker's budget: the evaluation steps its runs may take in
# all (Check.bend), and how deep its input tree may grow. 2^30: simpleplus
# needs 481,067,842 steps to prove every check main makes on the session's
# inputs (2026-11-18; 2^28 before, which ran out on it).
def check.work() -> Nat:
  U32.to_nat(1073741824)

def check.depth() -> Nat:
  U32.to_nat(100000)

def erasure.watching(+left: Set(), +counts: List<&2, E.TS>, +x: E.X, +g: Maybe<&2, E.X>) -> Ck.Seen:
  Ck.check.session(check.depth(), Sm.fuel(), Sm.Pol{Sm.Watch{}, Ck.erasable(x, left)}, Ck.witness(counts, x), g, check.work())

def erasure.all(s: Ck.Seen, +left: Set(), +counts: List<&2, E.TS>, +x: E.X, +g: Maybe<&2, E.X>) -> Erasure:
  match s:
    case Ck.Seen{v, l}:
      match v:
        case Ck.Proven{}:
          Checked{Ck.Seen{Ck.Proven{}, l}, None{}}
        case other:
          Checked{erasure.watching(left, counts, x, g), Some{other}}

# The erasure checker on main's witness, on the inputs a session gives main
# that the prologue passes (Ck.check.session: the user's decision of
# 2026-11-17, that a line is a list of code points). It watches every check
# main makes, the ones left to run time too, and every chain's bottom; where
# that is not proven, only the sites the net's program erases anyway (every
# check main no longer makes, and every chain's bottom).
def erasure.run(check: Bool, +left: Set(), +counts: List<&2, E.TS>, +x: E.X, +g: Maybe<&2, E.X>) -> Erasure:
  match check:
    case True{}:
      erasure.all(erasure.watching(Set.new(), counts, x, g), left, counts, x, g)
    case False{}:
      Unproven{}

# left, unless the checker proved every check (first is None).
def left.unless(first: Maybe<&2, Ck.Verdict>, +left: Set()) -> Set():
  match first:
    case None{}:
      Set.new()
    case Some{v}:
      left

# The checks main still makes on the net: none, where the checker proved every
# check unreachable; else those left to run time.
def erasure.left(e: Erasure, +left: Set()) -> Set():
  match e:
    case Checked{s, first}:
      left.unless(first, left)
    case Unproven{}:
      left

# Whether the checker proved the erasures: then, and only then, they are made.
def erased(e: Erasure) -> Bool:
  match e:
    case Checked{s, first}:
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
    case R{v, s}:
      s

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
  cored(counts, Checks{plan.keep(p), plan.hoisted(p), e}, net.expr(erased(e), os, counts, erasure.left(e, left), cm, cap, plain), plain, plan.prologue(p))

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

# The run keeps the refinement checks: each is sized where it is met. No input
# is bounded but by the checks its values pass.
def main.run.from(+os: Map<&2, L.Origin>, +max: U32, +cm: E.X, +mx: E.X, +x: E.X, +cap: Bool, +want: Want) -> Result<&2, &2, SizeFail, Sized>:
  +run = eval(fuel(), {Cfg{MSize{}, max} : Cfg}, JEval{mx, E.XZero{}})
  tidy(os, fold.aborted(r.v(run)), run, cm, x, cap, want)

def main.run(+os: Map<&2, L.Origin>, +max: U32, +cm: E.X, +x: E.X, +cap: Bool, +want: Want) -> Result<&2, &2, SizeFail, Sized>:
  match cap:
    case True{}:
      main.run.from(os, max, cm, E.app(x, E.XVar{""}), x, cap, want)
    case False{}:
      main.run.from(os, max, cm, naked.envs(x), x, cap, want)

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
  main.run(E.origins(t), max, cm, x, cap, want)

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
