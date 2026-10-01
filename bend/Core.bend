import Base

# The runnable core (haskell-final's IR.Core CompiledExpr and IR.Base
# BasicExpr): what sizing hands the runtime, and what the runtime hands
# back. Its type is the last stage of DESIGN.md §3: sizing's holes, stubs
# and abstract values cannot be written in it, so the runtime and the
# session cannot be handed one (H1).
#
# Data is Zero and Pair alone: a program's input, its state, an abort's
# message.
type D is Data:
  DZero{}
  DPair{+a: D, +b: D}

# The eight machine forms, Abort, and an aborted value (a result only).
type V is Data:
  VZero{}
  VPair{+a: V, +b: V}
  VEnv{}
  VSetEnv{+x: V}
  VDefer{+fi: U32, +x: V}
  VGate{}
  VLeft{+x: V}
  VRight{+x: V}
  VAbort{}
  VAborted{+m: D}

def of.data(d: D) -> V:
  match d:
    case DZero{}:
      VZero{}
    case DPair{a, b}:
      VPair{of.data(a), of.data(b)}

def data.pair(a: Maybe<&2, D>, b: Maybe<&2, D>) -> Maybe<&2, D>:
  match a:
    case Some{x}:
      match b:
        case Some{y}:
          Some{DPair{x, y}}
        case None{}:
          None{}
    case None{}:
      None{}

# A value that is data through and through, as data.
def data(v: V) -> Maybe<&2, D>:
  match v:
    case VZero{}:
      Some{DZero{}}
    case VPair{a, b}:
      data.pair(data(a), data(b))
    case _:
      None{}

# Numbers and strings (intB, b2i, s2b, b2s)
# -----------------------------------------

# n as nested pairs.
def int(n: Nat) -> D:
  match n:
    case 0n:
      DZero{}
    case 1n+k:
      DPair{int(k), DZero{}}

def int.u32(n: U32) -> D:
  int(U32.to_nat(n))

def to.int.succ(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case Some{k}:
      Some{(k + 1 : U32)}
    case None{}:
      None{}

# A unary number, if it is one.
def to.int(d: D) -> Maybe<&2, U32>:
  match d:
    case DZero{}:
      Some{0}
    case DPair{n, DZero{}}:
      to.int.succ(to.int(n))
    case _:
      None{}

def to.string.cons(c: Maybe<&2, U32>, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match c:
    case Some{k}:
      match rest:
        case Some{s}:
          Some{SCon{Chr{k}, s}}
        case None{}:
          None{}
    case None{}:
      None{}

def to.string.d(d: D) -> Maybe<&2, String>:
  match d:
    case DZero{}:
      Some{SNil{}}
    case DPair{c, rest}:
      to.string.cons(to.int(c), to.string.d(rest))

def to.string.of(m: Maybe<&2, D>) -> Maybe<&2, String>:
  match m:
    case Some{d}:
      to.string.d(d)
    case None{}:
      None{}

# A list of unary code points, if the value is one.
def to.string(v: V) -> Maybe<&2, String>:
  to.string.of(data(v))

def of.string(s: String) -> D:
  match s:
    case SNil{}:
      DZero{}
    case SCon{Chr{c}, rest}:
      DPair{int.u32(c), of.string(rest)}

# Reserved function indices
# -------------------------
#
# Negative function indices name the compiler's own closures (DESIGN.md §2);
# as a U32 they wrap (-1 is 4294967295).

def neg(k: U32) -> U32:
  (0 - k : U32)

def twiddle.ind() -> U32:
  neg(1)

def left.gate.ind() -> U32:
  neg(2)

def right.gate.ind() -> U32:
  neg(3)

def step.e.ind() -> U32:
  neg(4)

def step.t.ind() -> U32:
  neg(5)

def step.rfa() -> U32:
  neg(7)

def step.rfb() -> U32:
  neg(8)

def step.w() -> U32:
  neg(9)

def refinement.tc() -> U32:
  neg(10)

def abort.ind() -> U32:
  neg(11)

# Builders (IR.Builder)
# ---------------------

def rights(n: Nat, x: V) -> V:
  match n:
    case 0n:
      x
    case 1n+k:
      VRight{rights(k, x)}

# varB
def var(n: Nat) -> V:
  VLeft{rights(n, VEnv{})}

def twiddle() -> V:
  VDefer{twiddle.ind(), VPair{VLeft{VRight{VEnv{}}}, VPair{VLeft{VEnv{}}, VRight{VRight{VEnv{}}}}}}

# appB: c applied to i.
def app(c: V, i: V) -> V:
  VSetEnv{VSetEnv{VPair{twiddle(), VPair{i, c}}}}

def fill(c: V, e: V) -> V:
  VSetEnv{VPair{c, e}}

# The strict if: both branches evaluated, then chosen (GateSwitchEE).
def gate.switch(l: V, r: V, s: V) -> V:
  fill(fill(VGate{}, s), VPair{l, r})

# The lazy if (iteB): the branches stay deferred until chosen.
def ite(i: V, t: V, e: V) -> V:
  fill(fill(fill(VGate{}, i), VPair{VDefer{step.e.ind(), e}, VDefer{step.t.ind(), t}}), VEnv{})

# Showing
# -------

def fi.signed(neg: Bool, +n: U32) -> String:
  match neg:
    case True{}:
      "-" ++ U32.show((0 - n : U32))
    case False{}:
      U32.show(n)

def fi.show(+fi: U32) -> String:
  "FunctionIndex {unFunctionIndex = " ++ fi.signed(U32.is_ge(fi, 2147483648), fi) ++ "}"

# How Haskell shows a CompiledExpr (data-fix's Show over the Show1
# instances, which quote their constructor text): Pair 0 0 is
# Fix "PairSF ("Fix "ZeroSF"", "Fix "ZeroSF"")". Data shows the same.
def show.data(d: D) -> String:
  match d:
    case DZero{}:
      "Fix \"ZeroSF\""
    case DPair{a, b}:
      "Fix \"PairSF (\"" ++ show.data(a) ++ "\", \"" ++ show.data(b) ++ "\")\""

def show(v: V) -> String:
  match v:
    case VZero{}:
      "Fix \"ZeroSF\""
    case VPair{a, b}:
      "Fix \"PairSF (\"" ++ show(a) ++ "\", \"" ++ show(b) ++ "\")\""
    case VEnv{}:
      "Fix \"EnvSF\""
    case VSetEnv{a}:
      "Fix \"SetEnvSF (\"" ++ show(a) ++ "\")\""
    case VDefer{fi, a}:
      "Fix \"DeferSF \"" ++ fi.show(fi) ++ "\" (\"" ++ show(a) ++ "\")\""
    case VGate{}:
      "Fix \"GateSF\""
    case VLeft{a}:
      "Fix \"LeftSF (\"" ++ show(a) ++ "\")\""
    case VRight{a}:
      "Fix \"RightSF (\"" ++ show(a) ++ "\")\""
    case VAbort{}:
      "Fix \"AbortF\""
    case VAborted{m}:
      "Fix \"(AbortedF \"" ++ show.data(m) ++ "\")\""

# Haskell's prettyPrint of a StuckExpr: one child continues the line, a
# pair's second child goes on the next line under the first. Abort shows
# as "!"; an aborted value is no StuckExpr, and shows as "?".
def pretty.at(v: V, +col: Nat) -> String:
  match v:
    case VZero{}:
      "Z"
    case VPair{a, b}:
      "P " ++ pretty.at(a, (col + 2n : Nat)) ++ "\n" ++ String.repeat(" ", (col + 2n : Nat)) ++ pretty.at(b, (col + 2n : Nat))
    case VEnv{}:
      "E"
    case VSetEnv{a}:
      "S " ++ pretty.at(a, (col + 2n : Nat))
    case VDefer{fi, a}:
      "F" ++ fi.signed(U32.is_ge(fi, 2147483648), fi) ++ " "
        ++ pretty.at(a, (col + 2n + String.length(fi.signed(U32.is_ge(fi, 2147483648), fi)) : Nat))
    case VGate{}:
      "G"
    case VLeft{a}:
      "L " ++ pretty.at(a, (col + 2n : Nat))
    case VRight{a}:
      "R " ++ pretty.at(a, (col + 2n : Nat))
    case VAbort{}:
      "!"
    case VAborted{m}:
      "?"

def pretty(v: V) -> String:
  pretty.at(v, 0n)
