import Base
import ./Core.bend as Co
import ./Reference.bend as Rf

# Partial evaluation (master's Telomare.Eval.Reference evalPartial, with
# Telomare.Machine's steps), for the REPL's `:p`: a compiled term reduced
# bottom-up as far as it goes without an input. A function's body is
# reduced too, its argument unknown: its Env, and whatever needs it, sits
# behind a barrier, which comes off at the end. An application of a known
# function reduces its body with Env replaced by the argument (and leaves
# the functions inside unreduced, as master's stuckStep does).

# The term with barriers (PartialExpr's DeferredF BarrierF).
type PV is Data:
  PZero{}
  PPair{+a: PV, +b: PV}
  PEnv{}
  PSetEnv{+x: PV}
  PDefer{+fi: U32, +x: PV}
  PGate{}
  PLeft{+x: PV}
  PRight{+x: PV}
  PBar{+x: PV}

# Aborts were made inert before (compileUnitTestNoAbort): none is left.
def of.v(v: Co.V) -> PV:
  match v:
    case Co.VZero{}:
      PZero{}
    case Co.VPair{a, b}:
      PPair{of.v(a), of.v(b)}
    case Co.VEnv{}:
      PEnv{}
    case Co.VSetEnv{x}:
      PSetEnv{of.v(x)}
    case Co.VDefer{fi, x}:
      PDefer{fi, of.v(x)}
    case Co.VGate{}:
      PGate{}
    case Co.VLeft{x}:
      PLeft{of.v(x)}
    case Co.VRight{x}:
      PRight{of.v(x)}
    case Co.VAbort{o, m}:
      of.v(m)

# removeBarriers, everywhere.
def to.v(p: PV) -> Co.V:
  match p:
    case PZero{}:
      Co.VZero{}
    case PPair{a, b}:
      Co.VPair{to.v(a), to.v(b)}
    case PEnv{}:
      Co.VEnv{}
    case PSetEnv{x}:
      Co.VSetEnv{to.v(x)}
    case PDefer{fi, x}:
      Co.VDefer{fi, to.v(x)}
    case PGate{}:
      Co.VGate{}
    case PLeft{x}:
      Co.VLeft{to.v(x)}
    case PRight{x}:
      Co.VRight{to.v(x)}
    case PBar{x}:
      to.v(x)

def unbar(p: PV) -> PV:
  match p:
    case PPair{a, b}:
      PPair{unbar(a), unbar(b)}
    case PSetEnv{x}:
      PSetEnv{unbar(x)}
    case PDefer{fi, x}:
      PDefer{fi, unbar(x)}
    case PLeft{x}:
      PLeft{unbar(x)}
    case PRight{x}:
      PRight{unbar(x)}
    case PBar{x}:
      unbar(x)
    case other:
      other

# Which step a node gets: evalPartial's (deferStep first), the same inside
# a function's body (its Env behind a barrier first: addBarrier), or an
# applied function body's (Env is the argument: replaceEnv; no deferStep).
type Md is Data:
  MOut{}
  MBar{}
  MFill{+e: PV}

# What is left to do: transform a term (its parts, then itself); step a
# node whose parts are done; reduce a function's body (deferStep); or
# nothing, the value in hand.
type Job is Data:
  JTr{+m: Md, +t: PV}
  JStep{+m: Md, +n: PV}
  JDefer{+fi: U32, +x: PV}
  JDone{+v: PV}

# stuckStep's projections, then deferredEvalStep's barrier, then
# wrapUnknownStep's.
def left.of(x: PV) -> PV:
  match x:
    case PZero{}:
      PZero{}
    case PPair{l, r}:
      l
    case PBar{y}:
      PBar{PLeft{y}}
    case other:
      PBar{PLeft{other}}

def right.of(x: PV) -> PV:
  match x:
    case PZero{}:
      PZero{}
    case PPair{l, r}:
      r
    case PBar{y}:
      PBar{PRight{y}}
    case other:
      PBar{PRight{other}}

# A gate given its argument: doLeft for 0, doRight for a pair.
def gate.of(e: PV) -> PV:
  match e:
    case PZero{}:
      of.v(Rf.do.left())
    case PPair{a, b}:
      of.v(Rf.do.right())
    case PBar{s}:
      PBar{PSetEnv{PPair{PGate{}, s}}}
    case other:
      PBar{PSetEnv{PPair{PGate{}, other}}}

# FillFunction c e: a known function's body under its argument.
def fill(c: PV, +e: PV) -> Job:
  match c:
    case PDefer{fi, d}:
      JTr{MFill{e}, d}
    case PGate{}:
      JDone{gate.of(e)}
    case PBar{c2}:
      JDone{PBar{PSetEnv{PPair{c2, e}}}}
    case other:
      JDone{PBar{PSetEnv{PPair{other, e}}}}

def setenv.of(x: PV) -> Job:
  match x:
    case PPair{c, e}:
      fill(c, e)
    case PBar{y}:
      JDone{PBar{PSetEnv{y}}}
    case other:
      JDone{PBar{PSetEnv{other}}}

# basicStep, then stuckStep, then deferredEvalStep', then wrapUnknownStep.
def core(n: PV) -> Job:
  match n:
    case PSetEnv{x}:
      setenv.of(x)
    case PLeft{x}:
      JDone{left.of(x)}
    case PRight{x}:
      JDone{right.of(x)}
    case PEnv{}:
      JDone{PBar{PEnv{}}}
    case other:
      JDone{other}

def pre.out(n: PV) -> Job:
  match n:
    case PDefer{fi, x}:
      JDefer{fi, x}
    case other:
      core(other)

def pre.bar(n: PV) -> Job:
  match n:
    case PEnv{}:
      JDone{PBar{PEnv{}}}
    case PDefer{fi, x}:
      JDefer{fi, x}
    case other:
      core(other)

def pre.fill(+e: PV, n: PV) -> Job:
  match n:
    case PEnv{}:
      core(e)
    case other:
      core(other)

def pre(m: Md, n: PV) -> Job:
  match m:
    case MOut{}:
      pre.out(n)
    case MBar{}:
      pre.bar(n)
    case MFill{e}:
      pre.fill(e, n)

# transformNoDefer and the steps, as one machine: a function's body is
# not entered but by deferStep or an application.
def go(fuel: Nat, job: Job) -> PV:
  match fuel:
    case 0n:
      PZero{}
    case 1n++k:
      match job:
        case JDone{v}:
          v
        case JDefer{fi, x}:
          PDefer{fi, unbar(go(k, JTr{MBar{}, x}))}
        case JStep{m, n}:
          go(k, pre(m, n))
        case JTr{+m, t}:
          match t:
            case PPair{a, b}:
              go(k, JStep{m, PPair{go(k, JTr{m, a}), go(k, JTr{m, b})}})
            case PSetEnv{x}:
              go(k, JStep{m, PSetEnv{go(k, JTr{m, x})}})
            case PLeft{x}:
              go(k, JStep{m, PLeft{go(k, JTr{m, x})}})
            case PRight{x}:
              go(k, JStep{m, PRight{go(k, JTr{m, x})}})
            case PBar{x}:
              go(k, JStep{m, PBar{go(k, JTr{m, x})}})
            case other:
              go(k, JStep{m, other})

# evalPartial': the term partially evaluated, its barriers removed.
def partial(v: Co.V) -> Co.V:
  to.v(go(U32.to_nat(4294967295), JTr{MOut{}, of.v(v)}))
