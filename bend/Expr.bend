import Base
import ./Term.bend as T
import ./Core.bend as Co

# Sizing's expression (haskell-final's IR.Base and Size.IR): Term3 without
# its locations, plus the abstract values sizing works with. Sizing ends by
# handing the runtime the runnable core (Core.bend), in which none of these
# values can be written (`core`). XError is where Haskell's sizing would
# have thrown: it travels with the value, and is reported only if it
# reaches the result.
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
  XDefer{Co.twiddle.ind(), XPair{XLeft{XRight{XEnv{}}}, XPair{XLeft{XEnv{}}, XRight{XRight{XEnv{}}}}}}

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
  fill(fill(fill(XGate{}, i), XPair{XDefer{Co.step.e.ind(), e}, XDefer{Co.step.t.ind(), t}}), XEnv{})

def do.left() -> X:
  XDefer{Co.left.gate.ind(), XLeft{XEnv{}}}

def do.right() -> X:
  XDefer{Co.right.gate.ind(), XRight{XEnv{}}}

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
      XPair{XDefer{Co.step.w(), fill(fill(XAbort{}, XRight{XEnv{}}), XLeft{XEnv{}})},
            XPair{XZero{}, int.u32(tok)}}
    case 1n+k:
      XPair{XDefer{Co.step.rfb(), approx.body()}, XPair{chain(k, tok), XLeft{XEnv{}}}}

# A recursion sized to n iterations: n links over a base that aborts with
# (0, token) (sizedRecursionChain).
def sized.chain(+tok: U32, n: U32) -> X:
  chain(U32.to_nat(n), tok)

# A refinement check becomes: apply the check, abort with its answer if
# that is not 0, else the value (removeRefinementWrappers).
def remove.checks(t: X) -> X:
  match t:
    case XCheck{tc, c}:
      fill(XDefer{Co.refinement.tc(), fill(fill(XAbort{}, app(XLeft{XEnv{}}, XRight{XEnv{}})), XRight{XEnv{}})},
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

# The runnable core
# -----------------

def core.pair(a: Result<&2, &2, String, Co.V>, b: Result<&2, &2, String, Co.V>) -> Result<&2, &2, String, Co.V>:
  match a:
    case Done{x}:
      match b:
        case Done{y}:
          Done{Co.VPair{x, y}}
        case Fail{e}:
          Fail{e}
    case Fail{e}:
      Fail{e}

def core.defer(+fi: U32, a: Result<&2, &2, String, Co.V>) -> Result<&2, &2, String, Co.V>:
  match a:
    case Done{x}:
      Done{Co.VDefer{fi, x}}
    case Fail{e}:
      Fail{e}

def core.setenv(a: Result<&2, &2, String, Co.V>) -> Result<&2, &2, String, Co.V>:
  match a:
    case Done{x}:
      Done{Co.VSetEnv{x}}
    case Fail{e}:
      Fail{e}

def core.left(a: Result<&2, &2, String, Co.V>) -> Result<&2, &2, String, Co.V>:
  match a:
    case Done{x}:
      Done{Co.VLeft{x}}
    case Fail{e}:
      Fail{e}

def core.right(a: Result<&2, &2, String, Co.V>) -> Result<&2, &2, String, Co.V>:
  match a:
    case Done{x}:
      Done{Co.VRight{x}}
    case Fail{e}:
      Fail{e}

def core.data.pair(a: Result<&2, &2, String, Co.D>, b: Result<&2, &2, String, Co.D>) -> Result<&2, &2, String, Co.D>:
  match a:
    case Done{x}:
      match b:
        case Done{y}:
          Done{Co.DPair{x, y}}
        case Fail{e}:
          Fail{e}
    case Fail{e}:
      Fail{e}

def core.data(x: X) -> Result<&2, &2, String, Co.D>:
  match x:
    case XZero{}:
      Done{Co.DZero{}}
    case XPair{a, b}:
      core.data.pair(core.data(a), core.data(b))
    case _:
      Fail{"a non-data abort message"}

def core.aborted(m: Result<&2, &2, String, Co.D>) -> Result<&2, &2, String, Co.V>:
  match m:
    case Done{d}:
      Done{Co.VAborted{d}}
    case Fail{e}:
      Fail{e}

# The sized program as the runnable core, or the first form sizing should
# have removed from it (a sizing bug).
def core(x: X) -> Result<&2, &2, String, Co.V>:
  match x:
    case XZero{}:
      Done{Co.VZero{}}
    case XPair{a, b}:
      core.pair(core(a), core(b))
    case XEnv{}:
      Done{Co.VEnv{}}
    case XSetEnv{a}:
      core.setenv(core(a))
    case XDefer{+fi, a}:
      core.defer(fi, core(a))
    case XGate{}:
      Done{Co.VGate{}}
    case XLeft{a}:
      core.left(core(a))
    case XRight{a}:
      core.right(core(a))
    case XAbort{}:
      Done{Co.VAbort{}}
    case XAborted{m}:
      core.aborted(core.data(m))
    case XEither{n, a, b}:
      Fail{"a superposition"}
    case XTest{tok, a}:
      Fail{"a recursion test"}
    case XStub{tok, a}:
      Fail{"an unsized recursion"}
    case XStage{sr, a}:
      Fail{"a sizing stage"}
    case XCheck{tc, c}:
      Fail{"a refinement check"}
    case XStep{tok, n, a}:
      Fail{"an unrolling step"}
    case XVar{v}:
      Fail{"an input variable"}
    case XAny{}:
      Fail{"an unknown value"}
    case XBarrier{a}:
      Fail{"a barrier"}
    case XLefts{n, a}:
      Fail{"a left projection chain"}
    case XRights{n, a}:
      Fail{"a right projection chain"}
    case XError{msg}:
      Fail{"a sizing error (" ++ msg ++ ")"}
