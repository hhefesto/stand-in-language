import Base
import ./Core.bend as Co
import ./Loc.bend as L
import ./Term.bend as T

# Running without sizing (`--fast`, master's Telomare.Fast): the program's
# Term3 run as it is, every recursion site unbounded and unrolled on
# demand, every refinement check in place, under a fuel cap. Nothing proves
# such a run terminates, so fuel bounds each iteration: applications and
# unrollings, as master counts them, and the meter reports how many of each
# the session made, and the gate selections.
#
# A recursion site evaluates to a recursion value (VRec), its {t, r, b}
# closed over; forcing it (applying it, gating on it, projecting it)
# unrolls one layer, one approximant step over the next recursion value.
#
# The machine keeps its continuation as a list, as Reference.bend's does.

# The program (FastExpr).
type FX is Data:
  FZero{}
  FPair{+a: FX, +b: FX}
  FEnv{}
  FSetEnv{+x: FX}
  FDefer{+x: FX}
  FGate{}
  FLeft{+x: FX}
  FRight{+x: FX}
  FAbort{+o: L.Origin, +m: FX}
  FUnbounded{+tok: U32}

# Values (Value).
type FV is Data:
  VZero{}
  VPair{+a: FV, +b: FV}
  VDefer{+x: FX}
  VGate{}
  VAborted{+o: L.Origin, +m: Co.D}
  VRec{+tok: U32, +trb: FV}

# A recursion site's unrolls.
type Unroll is Data:
  Unroll{+tok: U32, +n: U32}

# What a run cost (FastMeter): applications, gate selections, and each
# recursion site's unrolls.
type Meter is Data:
  Meter{+applies: U32, +gates: U32, +unrolls: List<&2, Unroll>}

# How a run ended (FastError): stuck, or out of fuel.
type Fault is Data:
  FStuck{+why: String}
  FOutOfFuel{}

type K is Data:
  KPairA{+b: FX, +env: FV}
  KPairB{+a: FV}
  KAbort{+o: L.Origin}
  KGate{+l: FX, +r: FX, +env: FV}
  KLeft{}
  KRight{}
  KSetEnv{}
  KApplyGate{}

# The machine, with the meter and the fuel left (None: no cap).
type St is Data:
  SEval{+x: FX, +env: FV, +ks: List<&2, K>, +m: Meter, +fuel: Maybe<&2, U32>}
  SRet{+v: FV, +ks: List<&2, K>, +m: Meter, +fuel: Maybe<&2, U32>}
  SDone{+v: FV, +m: Meter, +fuel: Maybe<&2, U32>}
  SErr{+f: Fault, +m: Meter}

# Compiling (term3ToFast)
# -----------------------

def app(c: FX, i: FX) -> FX:
  FSetEnv{FSetEnv{FPair{FDefer{FPair{FLeft{FRight{FEnv{}}}, FPair{FLeft{FEnv{}}, FRight{FRight{FEnv{}}}}}}, FPair{i, c}}}}

# A refinement check: master's refinementCheckB, its defers bare.
def checking(+o: L.Origin, tc: FX, c: FX) -> FX:
  FSetEnv{FPair{FDefer{FSetEnv{FPair{FDefer{FSetEnv{FPair{
      FSetEnv{FPair{FSetEnv{FPair{FGate{}, FLeft{FEnv{}}}}, FPair{FDefer{FEnv{}}, FAbort{o, FLeft{FEnv{}}}}}},
      FRight{FEnv{}}}}},
    FPair{app(FLeft{FEnv{}}, FRight{FEnv{}}), FRight{FEnv{}}}}}},
    FPair{tc, c}}}

def of.term3(t: T.C) -> FX:
  match t:
    case T.CZero{loc}:
      FZero{}
    case T.CPair{loc, a, b}:
      FPair{of.term3(a), of.term3(b)}
    case T.CEnv{loc}:
      FEnv{}
    case T.CSetEnv{loc, x}:
      FSetEnv{of.term3(x)}
    case T.CDefer{loc, fi, x}:
      FDefer{of.term3(x)}
    case T.CGate{loc}:
      FGate{}
    case T.CLeft{loc, x}:
      FLeft{of.term3(x)}
    case T.CRight{loc, x}:
      FRight{of.term3(x)}
    case T.CAbort{loc}:
      FAbort{L.unknown.origin(), FZero{}}
    case T.CUnsized{loc, tok}:
      FUnbounded{tok}
    case T.CCheck{loc, o, site, tc, c}:
      checking(o, of.term3(tc), of.term3(c))

# Running
# -------

def meter.none() -> Meter:
  Meter{0, 0, []}



def unrolls.has(us: List<&2, Unroll>, +tok: U32) -> Bool:
  match us:
    case Nil{}:
      False{}
    case Con{u, rest}:
      match u:
        case Unroll{+t, k}:
          U32.is_eq(t, tok) || unrolls.has(rest, tok)

def unrolls.bump(us: List<&2, Unroll>, +tok: U32, +n: U32) -> List<&2, Unroll>:
  match us:
    case Nil{}:
      []
    case Con{u, rest}:
      match u:
        case Unroll{+t, +k}:
          Unroll{t, (k + Bool.pick(U32, U32.is_eq(t, tok), n, 0) : U32)} <> unrolls.bump(rest, tok, n)

def unrolls.add.if(found: Bool, us: List<&2, Unroll>, +tok: U32, +n: U32) -> List<&2, Unroll>:
  match found:
    case True{}:
      unrolls.bump(us, tok, n)
    case False{}:
      List.reverse(&2, Unroll, Unroll{tok, n} <> List.reverse(&2, Unroll, us))

def unrolls.add(+us: List<&2, Unroll>, +tok: U32, +n: U32) -> List<&2, Unroll>:
  unrolls.add.if(unrolls.has(us, tok), us, tok, n)

def unrolls.plus(xs: List<&2, Unroll>, us: List<&2, Unroll>) -> List<&2, Unroll>:
  match xs:
    case Nil{}:
      us
    case Con{x, rest}:
      match x:
        case Unroll{+t, +k}:
          unrolls.plus(rest, unrolls.add(us, t, k))

def meter.plus(a: Meter, b: Meter) -> Meter:
  match a:
    case Meter{+p, +q, us}:
      match b:
        case Meter{+r, +s, vs}:
          Meter{(p + r : U32), (q + s : U32), unrolls.plus(us, vs)}

# Spend one unit of fuel, if there is a cap; None when none is left.
def spent(f: Maybe<&2, U32>) -> Maybe<&2, Maybe<&2, U32>>:
  match f:
    case None{}:
      Some{None{}}
    case Some{+n}:
      Bool.pick(Maybe<&2, Maybe<&2, U32>>, U32.is_zero(n), None{}, Some{Some{(n - 1 : U32)}})

def tick.apply(m: Meter) -> Meter:
  match m:
    case Meter{+a, g, us}:
      Meter{(a + 1 : U32), g, us}

def tick.gate(m: Meter) -> Meter:
  match m:
    case Meter{a, +g, us}:
      Meter{a, (g + 1 : U32), us}

def tick.unroll(m: Meter, +tok: U32) -> Meter:
  match m:
    case Meter{a, g, us}:
      Meter{a, g, unrolls.add(us, tok, 1)}

# The approximant step a recursion value unrolls to: if test input then
# recursive recur input else base input (master's approxBody, with its own
# lazy if).
def approx.body() -> FX:
  +a1 = {FLeft{FEnv{}} : FX}
  +a2 = {FLeft{FRight{FEnv{}}} : FX}
  +a3 = {FLeft{FRight{FRight{FEnv{}}}} : FX}
  +a4 = {FLeft{FRight{FRight{FRight{FEnv{}}}}} : FX}
  +a5 = {FLeft{FRight{FRight{FRight{FRight{FEnv{}}}}}} : FX}
  FSetEnv{FPair{FSetEnv{FPair{FGate{}, app(a3, a1)}}, FPair{app(a5, a1), app(app(a4, a2), a1)}}}

def truncate(v: FV) -> Co.D:
  match v:
    case VPair{a, b}:
      Co.DPair{truncate(a), truncate(b)}
    case _:
      Co.DZero{}

def eval(x: FX, +env: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match x:
    case FZero{}:
      SRet{VZero{}, ks, m, fuel}
    case FEnv{}:
      SRet{env, ks, m, fuel}
    case FAbort{+o, y}:
      SEval{y, env, KAbort{o} <> ks, m, fuel}
    case FDefer{y}:
      SRet{VDefer{y}, ks, m, fuel}
    case FPair{a, b}:
      SEval{a, env, KPairA{b, env} <> ks, m, fuel}
    case FGate{}:
      SRet{VGate{}, ks, m, fuel}
    case FLeft{y}:
      SEval{y, env, KLeft{} <> ks, m, fuel}
    case FRight{y}:
      SEval{y, env, KRight{} <> ks, m, fuel}
    case FSetEnv{FPair{FSetEnv{FPair{FGate{}, s}}, FPair{l, r}}}:
      SEval{s, env, KGate{l, r, env} <> ks, m, fuel}
    case FSetEnv{y}:
      SEval{y, env, KSetEnv{} <> ks, m, fuel}
    case FUnbounded{+tok}:
      match env:
        case VPair{trb, rest}:
          SRet{VRec{tok, trb}, ks, m, fuel}
        case _:
          SErr{FStuck{"unexpected environment at a recursion site (encoding drift?)"}, m}

def forced.rec(+tok: U32, +trb: FV, f: Maybe<&2, Maybe<&2, U32>>, ks: List<&2, K>, m: Meter) -> St:
  match f:
    case None{}:
      SErr{FOutOfFuel{}, m}
    case Some{fuel}:
      SRet{VPair{VDefer{approx.body()}, VPair{VRec{tok, trb}, trb}}, ks, m, fuel}

# A value for the continuation, forced first where the continuation looks
# at it (forceValue): a recursion value unrolls, costing a unit of fuel.
def forced(v: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match v:
    case VRec{+tok, +trb}:
      forced.rec(tok, trb, spent(fuel), ks, tick.unroll(m, tok))
    case other:
      SRet{other, ks, m, fuel}

# What the continuation does with a forced value.
def project(v: FV, left: Bool, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match v:
    case VAborted{o, d}:
      SRet{VAborted{o, d}, ks, m, fuel}
    case VPair{a, b}:
      SRet{Bool.pick(FV, left, a, b), ks, m, fuel}
    case VZero{}:
      SRet{VZero{}, ks, m, fuel}
    case _:
      SErr{FStuck{Bool.pick(String, left, "left of something that is not a pair", "right of something that is not a pair")}, m}

def chose(v: FV, l: FX, r: FX, +env: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match v:
    case VZero{}:
      SEval{l, env, ks, tick.gate(m), fuel}
    case VPair{a, b}:
      SEval{r, env, ks, tick.gate(m), fuel}
    case VAborted{o, d}:
      SRet{VAborted{o, d}, ks, tick.gate(m), fuel}
    case _:
      SErr{FStuck{"gate on a non-data scrutinee"}, tick.gate(m)}

def applied.fuel(f: Maybe<&2, Maybe<&2, U32>>, d: FX, +arg: FV, ks: List<&2, K>, m: Meter) -> St:
  match f:
    case None{}:
      SErr{FOutOfFuel{}, m}
    case Some{fuel}:
      SEval{d, arg, ks, m, fuel}

def apply.gate(v: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match v:
    case VZero{}:
      SRet{VDefer{FLeft{FEnv{}}}, ks, m, fuel}
    case VPair{a, b}:
      SRet{VDefer{FRight{FEnv{}}}, ks, m, fuel}
    case VAborted{o, d}:
      SRet{VAborted{o, d}, ks, m, fuel}
    case _:
      SErr{FStuck{"gate applied to non-data"}, m}

# applyRaw, its function forced: a function runs its body on the argument
# (an application, a unit of fuel); a gate selects on the argument, forced.
def apply(fun: FV, +arg: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match fun:
    case VDefer{d}:
      applied.fuel(spent(fuel), d, arg, ks, tick.apply(m))
    case VAborted{o, d}:
      SRet{VAborted{o, d}, ks, m, fuel}
    case VGate{}:
      forced(arg, KApplyGate{} <> ks, tick.gate(m), fuel)
    case _:
      SErr{FStuck{"application of something that is not a function"}, m}

def apply.unrolled(+tok: U32, +trb: FV, +e: FV, f: Maybe<&2, Maybe<&2, U32>>, ks: List<&2, K>, m: Meter) -> St:
  match f:
    case None{}:
      SErr{FOutOfFuel{}, m}
    case Some{fuel}:
      apply(VPair{VDefer{approx.body()}, VPair{VRec{tok, trb}, trb}}, e, ks, m, fuel)

# The function forced, then applied.
def apply.forced(f: FV, +e: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match f:
    case VRec{+tok, +trb}:
      apply.unrolled(tok, trb, e, spent(fuel), ks, tick.unroll(m, tok))
    case other:
      apply(other, e, ks, m, fuel)

def setenv(v: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match v:
    case VPair{f, e}:
      apply.forced(f, e, ks, m, fuel)
    case VAborted{o, d}:
      SRet{VAborted{o, d}, ks, m, fuel}
    case _:
      SErr{FStuck{"setenv of something that is not a pair"}, m}

def aborted(+o: L.Origin, v: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match v:
    case VAborted{p, d}:
      SRet{VAborted{p, d}, ks, m, fuel}
    case other:
      SRet{VAborted{o, truncate(other)}, ks, m, fuel}

# A forced value for the frame k.
def frame(k: K, +v: FV, rest: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match k:
    case KAbort{o}:
      aborted(o, v, rest, m, fuel)
    case KGate{l, r, env}:
      chose(v, l, r, env, rest, m, fuel)
    case KLeft{}:
      project(v, True{}, rest, m, fuel)
    case KRight{}:
      project(v, False{}, rest, m, fuel)
    case KSetEnv{}:
      setenv(v, rest, m, fuel)
    case KApplyGate{}:
      apply.gate(v, rest, m, fuel)
    case KPairA{b, env}:
      SEval{b, env, KPairB{v} <> rest, m, fuel}
    case KPairB{a}:
      SRet{VPair{a, v}, rest, m, fuel}

# Whether the frame looks at its value (and so forces it first).
def forcing(k: K) -> Bool:
  match k:
    case KPairA{b, env}:
      False{}
    case KPairB{a}:
      False{}
    case _:
      True{}

def ret.forced(force: Bool, +v: FV, k: K, rest: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match force:
    case True{}:
      match v:
        case VRec{+tok, +trb}:
          forced.rec(tok, trb, spent(fuel), k <> rest, tick.unroll(m, tok))
        case other:
          frame(k, other, rest, m, fuel)
    case False{}:
      frame(k, v, rest, m, fuel)

def ret(+v: FV, ks: List<&2, K>, m: Meter, fuel: Maybe<&2, U32>) -> St:
  match ks:
    case Nil{}:
      SDone{v, m, fuel}
    case Con{+k, rest}:
      ret.forced(forcing(k), v, k, rest, m, fuel)

def run.go(n: Nat, st: St) -> St:
  match n:
    case 0n:
      match st:
        case SDone{v, m, fuel}:
          SDone{v, m, fuel}
        case SErr{f, m}:
          SErr{f, m}
        case SEval{x, env, ks, m, fuel}:
          SErr{FStuck{"evaluation did not finish"}, m}
        case SRet{v, ks, m, fuel}:
          SErr{FStuck{"evaluation did not finish"}, m}
    case 1n+k:
      match st:
        case SEval{x, +env, ks, m, fuel}:
          run.go(k, eval(x, env, ks, m, fuel))
        case SRet{+v, ks, m, fuel}:
          run.go(k, ret(v, ks, m, fuel))
        case SDone{v, m, fuel}:
          SDone{v, m, fuel}
        case SErr{f, m}:
          SErr{f, m}

def run(st: St) -> St:
  run.go(U32.to_nat(4294967295), st)

def of.data(d: Co.D) -> FV:
  match d:
    case Co.DZero{}:
      VZero{}
    case Co.DPair{a, b}:
      VPair{of.data(a), of.data(b)}

# One iteration (iterateMain): the program evaluated to main's closure,
# then the closure applied to the input (an application), each iteration
# with the whole cap.
def closure.applied(st: St, input: FV) -> St:
  match st:
    case SDone{v, m, fuel}:
      match v:
        case VPair{VDefer{d}, clo}:
          applied.fuel(spent(fuel), d, VPair{input, clo}, [], tick.apply(m))
        case _:
          SErr{FStuck{"main is not a closure"}, m}
    case other:
      other

# The input: 0 first, then the line read and the state the last iteration
# left, which need not be data here.
def iteration(+prog: FX, input: FV, +cap: Maybe<&2, U32>) -> St:
  run(closure.applied(run(SEval{prog, VZero{}, [], meter.none(), cap}), input))

# A string as a value (s2v).
def of.string(s: String) -> FV:
  of.data(Co.of.string(s))

# The leftmost aborted value in a result, not looking inside closures or
# recursion values (findAbort).
type Found is Data:
  Found{+o: L.Origin, +m: Co.D}

def found.first(a: Maybe<&2, Found>, b: Maybe<&2, Found>) -> Maybe<&2, Found>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

def find.abort(v: FV) -> Maybe<&2, Found>:
  match v:
    case VAborted{o, d}:
      Some{Found{o, d}}
    case VPair{a, b}:
      found.first(find.abort(a), find.abort(b))
    case _:
      None{}

# A value as data, if it is data (v2b).
def data.pair(a: Maybe<&2, Co.D>, b: Maybe<&2, Co.D>) -> Maybe<&2, Co.D>:
  match a:
    case Some{x}:
      match b:
        case Some{y}:
          Some{Co.DPair{x, y}}
        case None{}:
          None{}
    case None{}:
      None{}

def data(v: FV) -> Maybe<&2, Co.D>:
  match v:
    case VZero{}:
      Some{Co.DZero{}}
    case VPair{a, b}:
      data.pair(data(a), data(b))
    case _:
      None{}

# What the session prints when a run breaks (renderFastError); cap is the
# fuel each iteration had.
def fault.text(f: Fault, +cap: U32, commas: String) -> String:
  match f:
    case FStuck{why}:
      "runtime error (stuck): " ++ why
    case FOutOfFuel{}:
      "runtime error: out of fuel after " ++ commas ++ " applications and unrollings.\n"
        ++ "This run is not sized, so nothing proved it terminates. Raise the cap with --fuel N, or lift it entirely with --fuel 0."
