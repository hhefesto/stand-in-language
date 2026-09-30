import Base
import ./Term.bend as T

# The core expression (haskell-final's IR.Base and Size.IR): Term3 without
# its locations, plus the abstract values sizing works with. The sized,
# compiled program (CompiledExpr) uses only the first ten constructors.
# XError is where Haskell's sizing would have thrown: it travels with the
# value, and is reported only if it reaches the result.
#
# An input position (IVarF) is its path from the root, 'L' and 'R' for
# left and right, where Haskell numbers positions 2n+1 and 2n+2: a
# position descends from another when its path extends the other's.

# Sizing's per-token iteration counts (SizedRecursion), ascending by token.

type TS is Data:
  TS{+tok: U32, +n: U32}

type X is Data:
  XZero{}
  XPair{+a: X, +b: X}
  XEnv{}
  XSetEnv{+x: X}
  XDefer{+fi: U32, +x: X}
  XGate{}
  XLeft{+x: X}
  XRight{+x: X}
  XAbort{}
  XAborted{+m: X}
  XEither{+n: Maybe<&2, String>, +a: X, +b: X}
  XTest{+tok: U32, +x: X}
  XStub{+tok: U32, +x: X}
  XStage{+sr: List<&2, TS>, +x: X}
  XCheck{+tc: X, +c: X}
  XStep{+tok: U32, +n: U32, +x: X}
  XVar{+p: String}
  XAny{}
  XBarrier{+x: X}
  XLefts{+n: U32, +x: X}
  XRights{+n: U32, +x: X}
  XError{+msg: String}

# Negative function indices name the machinery's own closures; as a U32
# they wrap (-1 is 4294967295).
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

# Term3 without locations (term3ToUnsizedExpr): a recursion placeholder
# becomes its stub over the environment.
def of.term3(t: T.C) -> X:
  match t:
    case T.CZero{loc}:
      XZero{}
    case T.CPair{loc, a, b}:
      XPair{of.term3(a), of.term3(b)}
    case T.CEnv{loc}:
      XEnv{}
    case T.CSetEnv{loc, x}:
      XSetEnv{of.term3(x)}
    case T.CDefer{loc, fi, x}:
      XDefer{fi, of.term3(x)}
    case T.CGate{loc}:
      XGate{}
    case T.CLeft{loc, x}:
      XLeft{of.term3(x)}
    case T.CRight{loc, x}:
      XRight{of.term3(x)}
    case T.CAbort{loc}:
      XAbort{}
    case T.CUnsized{loc, tok}:
      XStub{tok, XEnv{}}
    case T.CCheck{loc, cloc, tc, c}:
      XCheck{of.term3(tc), of.term3(c)}

# Builders (Machine.hs)
# ---------------------

def rights(n: Nat, x: X) -> X:
  match n:
    case 0n:
      x
    case 1n+k:
      XRight{rights(k, x)}

# varB
def var(n: Nat) -> X:
  XLeft{rights(n, XEnv{})}

def twiddle() -> X:
  XDefer{twiddle.ind(), XPair{XLeft{XRight{XEnv{}}}, XPair{XLeft{XEnv{}}, XRight{XRight{XEnv{}}}}}}

# appB: c applied to i.
def app(c: X, i: X) -> X:
  XSetEnv{XSetEnv{XPair{twiddle(), XPair{i, c}}}}

def fill(c: X, e: X) -> X:
  XSetEnv{XPair{c, e}}

# The strict if: both branches evaluated, then chosen (GateSwitchEE).
def gate.switch(l: X, r: X, s: X) -> X:
  fill(fill(XGate{}, s), XPair{l, r})

# The lazy if (iteB): the branches stay deferred until chosen.
def ite(i: X, t: X, e: X) -> X:
  fill(fill(fill(XGate{}, i), XPair{XDefer{step.e.ind(), e}, XDefer{step.t.ind(), t}}), XEnv{})

def do.left() -> X:
  XDefer{left.gate.ind(), XLeft{XEnv{}}}

def do.right() -> X:
  XDefer{right.gate.ind(), XRight{XEnv{}}}

# intB / i2B: n as nested pairs.
def int(n: Nat) -> X:
  match n:
    case 0n:
      XZero{}
    case 1n+k:
      XPair{int(k), XZero{}}

def int.u32(n: U32) -> X:
  int(U32.to_nat(n))

# The abort reasons (IR.Base).
def abort.recursion(tok: U32) -> X:
  XPair{XZero{}, int.u32(tok)}

def abort.any() -> X:
  XPair{XPair{XPair{XZero{}, XZero{}}, XZero{}}, XZero{}}

def abort.unsizeable(tok: U32) -> X:
  XPair{XPair{XPair{XPair{XZero{}, XZero{}}, XZero{}}, XZero{}}, int.u32(tok)}

# One unrolling of a recursion while sizing: if the test holds, apply the
# recursive step to the next unrolling (a stub, expanded when reached),
# else stop here, recording depth n (unsizedStepBody). Its environment is
# (input, (test, (recursive, (base, 0)))).
def step.body(+tok: U32, +n: U32) -> X:
  ite(app(var(1n), var(0n)),
      app(app(var(2n), XStep{tok, n, XEnv{}}), var(0n)),
      XStage{[TS{tok, n}], app(var(3n), var(0n))})

# One step of a sized recursion: if test input then recursive recur input
# else base input, both branches built (approximantStep with GateSwitchEE).
def approx.body() -> X:
  gate.switch(app(var(4n), var(0n)), app(app(var(3n), var(1n)), var(0n)), app(var(2n), var(0n)))

def chain(n: Nat, +tok: U32) -> X:
  match n:
    case 0n:
      XPair{XDefer{step.w(), fill(fill(XAbort{}, XRight{XEnv{}}), XLeft{XEnv{}})},
            XPair{XZero{}, int.u32(tok)}}
    case 1n+k:
      XPair{XDefer{step.rfb(), approx.body()}, XPair{chain(k, tok), XLeft{XEnv{}}}}

# A recursion sized to n iterations: n links over a base that aborts with
# (0, token) (sizedRecursionChain).
def sized.chain(+tok: U32, n: U32) -> X:
  chain(U32.to_nat(n), tok)

# A refinement check becomes: apply the check, abort with its answer if
# that is not 0, else the value (removeRefinementWrappers).
def remove.checks(t: X) -> X:
  match t:
    case XCheck{tc, c}:
      fill(XDefer{refinement.tc(), fill(fill(XAbort{}, app(XLeft{XEnv{}}, XRight{XEnv{}})), XRight{XEnv{}})},
           XPair{remove.checks(tc), remove.checks(c)})
    case XPair{a, b}:
      XPair{remove.checks(a), remove.checks(b)}
    case XSetEnv{x}:
      XSetEnv{remove.checks(x)}
    case XDefer{fi, x}:
      XDefer{fi, remove.checks(x)}
    case XLeft{x}:
      XLeft{remove.checks(x)}
    case XRight{x}:
      XRight{remove.checks(x)}
    case XStub{tok, x}:
      XStub{tok, remove.checks(x)}
    case other:
      other

def to.int.succ(m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match m:
    case Some{k}:
      Some{(k + 1 : U32)}
    case None{}:
      None{}

# b2i: a unary number, if it is one.
def to.int(x: X) -> Maybe<&2, U32>:
  match x:
    case XZero{}:
      Some{0}
    case XPair{n, XZero{}}:
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

# b2s: a list of unary code points, if it is one.
def to.string(x: X) -> Maybe<&2, String>:
  match x:
    case XZero{}:
      Some{SNil{}}
    case XPair{c, rest}:
      to.string.cons(to.int(c), to.string(rest))
    case _:
      None{}

# s2b
def of.string(s: String) -> X:
  match s:
    case SNil{}:
      XZero{}
    case SCon{Chr{c}, rest}:
      XPair{int.u32(c), of.string(rest)}
