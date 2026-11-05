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
  KChecked{+o: L.Origin, +entry: U32, +outer: U32}

# What one refinement check (one origin) cost over a run (CheckCost): how many
# times it ran, and the steps spent running it, less those of the checks nested
# in it, so the costs of all checks add up to their share of the steps.
type CheckCost is Data:
  CheckCost{+o: L.Origin, +runs: U32, +steps: U32}

# What a run cost (Meter): evaluation steps, term nodes built, what the checks
# cost, and the steps of the checks finished inside the check now running.
type Cost is Data:
  Cost{+steps: U32, +built: U32, +checks: List<&2, CheckCost>, +nested: U32}

def cost.none() -> Cost:
  Cost{0, 0, [], 0}

def cc.keep(same: Bool, +o: L.Origin, +r: U32, +s: U32, +xr: U32, +xs: U32, rest: List<&2, CheckCost>, later: List<&2, CheckCost>) -> List<&2, CheckCost>:
  match same:
    case True{}:
      CheckCost{o, (xr + r : U32), (xs + s : U32)} <> rest
    case False{}:
      CheckCost{o, xr, xs} <> later

# What r more runs and s more steps of origin o come to.
def cc.add(xs: List<&2, CheckCost>, +key: String, +o: L.Origin, +r: U32, +s: U32) -> List<&2, CheckCost>:
  match xs:
    case Nil{}:
      [CheckCost{o, r, s}]
    case Con{x, +rest}:
      match x:
        case CheckCost{+oo, +xr, +xs2}:
          cc.keep(String.eq(L.origin.key(oo), key), oo, r, s, xr, xs2, rest, cc.add(rest, key, o, r, s))

# The machine: a term to evaluate in an environment, or a value to hand to
# the continuation; the run's value; or why it broke (master's `error`).
type St is Data:
  SEval{+x: Co.V, +env: Maybe<&2, Co.V>, +ks: List<&2, K>, +c: Cost}
  SRet{+v: Co.V, +ks: List<&2, K>, +c: Cost}
  SDone{+v: Co.V, +c: Cost}
  SErr{+msg: String, +c: Cost}

def step(c: Cost) -> Cost:
  match c:
    case Cost{+s, b, k, n}:
      Cost{(s + 1 : U32), b, k, n}

def built(c: Cost) -> Cost:
  match c:
    case Cost{s, +b, k, n}:
      Cost{s, (b + 1 : U32), k, n}

def cost.steps(c: Cost) -> U32:
  match c:
    case Cost{s, b, k, n}:
      s

def cc.merge(xs: List<&2, CheckCost>, ys: List<&2, CheckCost>) -> List<&2, CheckCost>:
  match xs:
    case Nil{}:
      ys
    case Con{x, rest}:
      match x:
        case CheckCost{+o, +r, +t}:
          cc.merge(rest, cc.add(ys, L.origin.key(o), o, r, t))

# Across a session all the totals accumulate.
def cost.plus(a: Cost, b: Cost) -> Cost:
  match a:
    case Cost{+s, +n, ka, x}:
      match b:
        case Cost{+t, +m, kb, y}:
          Cost{(s + t : U32), (n + m : U32), cc.merge(ka, kb), 0}

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

def enter.check(+o: L.Origin, +body: Co.V, +e: Co.V, ks: List<&2, K>, c: Cost) -> St:
  match c:
    case Cost{+s, b, k, +n}:
      SEval{body, Some{e}, KChecked{o, s, n} <> ks, Cost{s, b, k, 0}}

def enter.if(m: Maybe<&2, L.Origin>, +body: Co.V, +e: Co.V, ks: List<&2, K>, c: Cost) -> St:
  match m:
    case Some{+o}:
      enter.check(o, body, e, ks, step(c))
    case None{}:
      SEval{body, Some{e}, ks, step(c)}

def origin.of(check: Bool, +body: Co.V) -> Maybe<&2, L.Origin>:
  match check:
    case True{}:
      Co.check.origin(body)
    case False{}:
      None{}

# A function runs its body with e as its Env. A refinement check charges its
# steps to where it was written.
def enter(+fi: U32, +body: Co.V, +e: Co.V, ks: List<&2, K>, c: Cost) -> St:
  enter.if(origin.of(U32.is_eq(fi, Co.refinement.tc()), body), body, e, ks, c)

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
    case Co.VDefer{+fi, +body}:
      match e:
        case Co.VAbort{o, m}:
          SRet{Co.VAbort{o, m}, ks, step(c)}
        case +other:
          enter(fi, body, other, ks, c)
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

# A check run: its origin charged the steps it took, less those of the checks
# nested in it (checking).
def checked(+o: L.Origin, +entry: U32, +outer: U32, c: Cost) -> Cost:
  match c:
    case Cost{+s, b, k, +n}:
      +inclusive = (s - entry : U32)
      Cost{s, b, cc.add(k, L.origin.key(o), o, 1, (inclusive - n : U32)), (outer + inclusive : U32)}

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
        case KChecked{o, entry, outer}:
          SRet{v, rest, checked(o, entry, outer, c)}

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
  run.go(U32.to_nat(4294967295), SEval{x, None{}, [], cost.none()})

# One iteration: main applied to its input (funWrap's `app fun input`).
def iteration(+main: Co.V, input: Co.D) -> St:
  run(Co.app(main, Co.of.data(input)))

# (a * 100) / s, for a at most s and s under 2^31, in words.
def percent.go(k: Nat, +a: U32, +s: U32, +r: U32, +q: U32) -> U32:
  match k:
    case 0n:
      q
    case 1n+j:
      +t = (r + a : U32)
      percent.go(j, a, s, Bool.pick(U32, U32.is_ge(t, s), (t - s : U32), t), Bool.pick(U32, U32.is_ge(t, s), (q + 1 : U32), q))

def percent.if(zero: Bool, +n: U32, +steps: U32) -> String:
  match zero:
    case True{}:
      "-"
    case False{}:
      U32.show(percent.go(100n, n, steps, 0, 0)) ++ "%"

def percent(+n: U32, +steps: U32) -> String:
  percent.if(U32.is_zero(steps), n, steps)

def cc.steps(c: CheckCost) -> U32:
  match c:
    case CheckCost{o, r, s}:
      s

def cc.runs(c: CheckCost) -> U32:
  match c:
    case CheckCost{o, r, s}:
      r

# Most steps first, then by origin.
def cc.le(a: CheckCost, b: CheckCost) -> Bool:
  match a:
    case CheckCost{oa, ra, +sa}:
      match b:
        case CheckCost{ob, rb, +sb}:
          U32.is_gt(sa, sb) || (U32.is_eq(sa, sb) && L.origin.le(oa, ob))

def cc.total.runs(xs: List<&2, CheckCost>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, rest}:
      (cc.runs(x) + cc.total.runs(rest) : U32)

def cc.total.steps(xs: List<&2, CheckCost>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, rest}:
      (cc.steps(x) + cc.total.steps(rest) : U32)

def cc.lines(xs: List<&2, CheckCost>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      match x:
        case CheckCost{o, r, s}:
          "\n  " ++ L.origin.render(o) ++ ": " ++ U32.show(r) ++ " runs, " ++ U32.show(s) ++ " steps" ++ cc.lines(rest)

def cc.report(xs: List<&2, CheckCost>, +steps: U32) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      +all = {x <> rest : List<&2, CheckCost>}
      +t = cc.total.steps(all)
      "\nrefinement checks (measured): " ++ U32.show(cc.total.runs(all)) ++ " runs, " ++ U32.show(t)
        ++ " steps (" ++ percent(t, steps) ++ " of all steps)" ++ cc.lines(all)

# What master's `--meter` prints for a run that cost c (renderMeter).
def render(c: Cost) -> String:
  match c:
    case Cost{+s, b, k, n}:
      "steps (measured): " ++ U32.show(s) ++ "\nnodes built (measured): " ++ U32.show(b)
        ++ cc.report(List.sort(~CheckCost, ~cc.le, k), s)
