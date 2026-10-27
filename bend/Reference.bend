import Base
import ./Core.bend as Co
import ./Loc.bend as L

# The reference evaluator (master's Telomare.Eval.Reference, as
# Telomare.Eval.Meter mirrors it): what a plain run and its `--meter` use,
# where `--ic` runs the interaction net. It evaluates the runnable core
# with an environment, binding a function body's Env to the argument as
# evaluation reaches it, and counts what master's meter counts: its
# evaluation steps, and the term nodes it builds (pairs and aborted
# values). A gate switch evaluates its scrutinee, then only the branch it
# chooses, in the current environment: master's evaluator gets that from
# Haskell's laziness, the meter (and this machine) from the shape.
#
# The machine keeps its continuation as a list, so evaluation never nests
# deeper than one frame of Bend's stack, however deep the program's
# recursion goes.

# What is left to do once a value is in hand.
type K is Data:
  KPairA{+b: Co.V, +env: Maybe<&2, Co.V>}
  KPairB{+a: Co.V}
  KAbort{+o: L.Origin}
  KGate{+l: Co.V, +r: Co.V, +env: Maybe<&2, Co.V>}
  KLeft{}
  KRight{}
  KSetEnv{}

# What a run cost (Meter): evaluation steps, and term nodes built.
type Cost is Data:
  Cost{+steps: U32, +built: U32}

# The machine: a term to evaluate in an environment, or a value to hand to
# the continuation; the run's value; or why it broke (master's `error`).
type St is Data:
  SEval{+x: Co.V, +env: Maybe<&2, Co.V>, +ks: List<&2, K>, +c: Cost}
  SRet{+v: Co.V, +ks: List<&2, K>, +c: Cost}
  SDone{+v: Co.V, +c: Cost}
  SErr{+msg: String, +c: Cost}

def step(c: Cost) -> Cost:
  match c:
    case Cost{+s, +b}:
      Cost{(s + 1 : U32), b}

def built(c: Cost) -> Cost:
  match c:
    case Cost{+s, +b}:
      Cost{s, (b + 1 : U32)}

def cost.plus(a: Cost, b: Cost) -> Cost:
  match a:
    case Cost{+s, +n}:
      match b:
        case Cost{+t, +m}:
          Cost{(s + t : U32), (n + m : U32)}

# The branch-selector functions a gate applied to 0 or a pair gives
# (doLeft, doRight).
def do.left() -> Co.V:
  Co.VDefer{Co.left.gate.ind(), Co.VLeft{Co.VEnv{}}}

def do.right() -> Co.V:
  Co.VDefer{Co.right.gate.ind(), Co.VRight{Co.VEnv{}}}

def is.abort(v: Co.V) -> Bool:
  match v:
    case Co.VAbort{o, m}:
      True{}
    case _:
      False{}

# A term, in env.
def eval(x: Co.V, +env: Maybe<&2, Co.V>, ks: List<&2, K>, c: Cost) -> St:
  match x:
    case Co.VZero{}:
      SRet{Co.VZero{}, ks, step(c)}
    case Co.VDefer{fi, b}:
      SRet{Co.VDefer{fi, b}, ks, step(c)}
    case Co.VGate{}:
      SRet{Co.VGate{}, ks, step(c)}
    case Co.VAbort{+o, m}:
      SEval{m, env, KAbort{o} <> ks, c}
    case Co.VSetEnv{Co.VPair{Co.VSetEnv{Co.VPair{Co.VGate{}, s}}, Co.VPair{l, r}}}:
      SEval{s, env, KGate{l, r, env} <> ks, c}
    case Co.VPair{a, b}:
      SEval{a, env, KPairA{b, env} <> ks, c}
    case Co.VLeft{y}:
      SEval{y, env, KLeft{} <> ks, c}
    case Co.VRight{y}:
      SEval{y, env, KRight{} <> ks, c}
    case Co.VSetEnv{y}:
      SEval{y, env, KSetEnv{} <> ks, c}
    case Co.VEnv{}:
      match env:
        case Some{v}:
          SRet{v, ks, step(c)}
        case None{}:
          SErr{"unapplied environment reference", c}

# A projection of v: what is left if it is an abort, the pair's half, 0 of
# 0.
def project(v: Co.V, left: Bool, ks: List<&2, K>, c: Cost) -> St:
  match v:
    case Co.VAbort{o, m}:
      SRet{Co.VAbort{o, m}, ks, step(c)}
    case Co.VPair{a, b}:
      SRet{Bool.pick(Co.V, left, a, b), ks, step(c)}
    case Co.VZero{}:
      SRet{Co.VZero{}, ks, step(c)}
    case _:
      SErr{"projection of something that is not a pair", step(c)}

def apply.gate(e: Co.V, ks: List<&2, K>, c: Cost) -> St:
  match e:
    case Co.VZero{}:
      SRet{do.left(), ks, step(c)}
    case Co.VPair{a, b}:
      SRet{do.right(), ks, step(c)}
    case _:
      SErr{"application of something that is not a function", c}

# f applied to e: an abort on either side is what is left; a gate gives
# the branch selector; a function runs its body with e as its Env.
def apply(f: Co.V, +e: Co.V, ks: List<&2, K>, c: Cost) -> St:
  match f:
    case Co.VAbort{o, m}:
      SRet{Co.VAbort{o, m}, ks, step(c)}
    case Co.VGate{}:
      match e:
        case Co.VAbort{o, m}:
          SRet{Co.VAbort{o, m}, ks, step(c)}
        case other:
          apply.gate(other, ks, c)
    case Co.VDefer{fi, body}:
      match e:
        case Co.VAbort{o, m}:
          SRet{Co.VAbort{o, m}, ks, step(c)}
        case other:
          SEval{body, Some{other}, ks, step(c)}
    case _:
      match e:
        case Co.VAbort{o, m}:
          SRet{Co.VAbort{o, m}, ks, step(c)}
        case other:
          SErr{"application of something that is not a function", c}

def setenv(v: Co.V, ks: List<&2, K>, c: Cost) -> St:
  match v:
    case Co.VAbort{o, m}:
      SRet{Co.VAbort{o, m}, ks, step(c)}
    case Co.VPair{f, e}:
      apply(f, e, ks, c)
    case _:
      SErr{"SetEnv of something that is not a pair", c}

# An abort's message evaluated: an abort in it is the one that counts;
# otherwise the abort is an aborted value, built.
def aborted(+o: L.Origin, m: Co.V, ks: List<&2, K>, c: Cost) -> St:
  match m:
    case Co.VAbort{p, n}:
      SRet{Co.VAbort{p, n}, ks, step(c)}
    case other:
      SRet{Co.VAbort{o, other}, ks, built(step(c))}

def chose(s: Co.V, l: Co.V, r: Co.V, +env: Maybe<&2, Co.V>, ks: List<&2, K>, c: Cost) -> St:
  match s:
    case Co.VAbort{o, m}:
      SRet{Co.VAbort{o, m}, ks, step(c)}
    case Co.VZero{}:
      SEval{l, env, ks, step(step(c))}
    case Co.VPair{a, b}:
      SEval{r, env, ks, step(step(c))}
    case _:
      SErr{"gate on a non-data scrutinee", step(c)}

# A value v for the continuation.
def ret(+v: Co.V, ks: List<&2, K>, c: Cost) -> St:
  match ks:
    case Nil{}:
      SDone{v, c}
    case Con{k, rest}:
      match k:
        case KPairA{b, env}:
          SEval{b, env, KPairB{v} <> rest, c}
        case KPairB{a}:
          SRet{Co.VPair{a, v}, rest, built(step(c))}
        case KAbort{o}:
          aborted(o, v, rest, c)
        case KGate{l, r, env}:
          chose(v, l, r, env, rest, c)
        case KLeft{}:
          project(v, True{}, rest, c)
        case KRight{}:
          project(v, False{}, rest, c)
        case KSetEnv{}:
          setenv(v, rest, c)

def run.go(fuel: Nat, st: St) -> St:
  match fuel:
    case 0n:
      match st:
        case SDone{v, c}:
          SDone{v, c}
        case SErr{m, c}:
          SErr{m, c}
        case SEval{x, env, ks, c}:
          SErr{"evaluation did not finish", c}
        case SRet{v, ks, c}:
          SErr{"evaluation did not finish", c}
    case 1n+f:
      match st:
        case SEval{x, +env, ks, c}:
          run.go(f, eval(x, env, ks, c))
        case SRet{+v, ks, c}:
          run.go(f, ret(v, ks, c))
        case SDone{v, c}:
          SDone{v, c}
        case SErr{m, c}:
          SErr{m, c}

# The value of a closed term, or why evaluation broke, and what it cost.
def run(x: Co.V) -> St:
  run.go(U32.to_nat(4294967295), SEval{x, None{}, [], Cost{0, 0}})

# One iteration: main applied to its input (funWrap's `app fun input`).
def iteration(+main: Co.V, input: Co.D) -> St:
  run(Co.app(main, Co.of.data(input)))

# What master's `--meter` prints for a run that cost c (renderMeter).
def render(c: Cost) -> String:
  match c:
    case Cost{s, b}:
      "steps (measured): " ++ U32.show(s) ++ "\nnodes built (measured): " ++ U32.show(b)
