import Base
import ./Core.bend as Co
import ./Loc.bend as L
import ./Lift.bend as Lf
import ./EALm.bend as EM
import ./Term.bend as T
import ./Expr.bend as E
import ./IC.bend as IC
import ./Meter.bend as Mt
import ./Show.bend as Sh
import ./Reference.bend as Rf

# One iteration's outcome, as the session prints it (master's
# Driver.funWrapWith and evalLoopCore, with IC.icRuntimeResult and
# IR.Base.describeAbort). A program is run on 0 first, then on (line, state)
# for each line read, while it answers (display, state) and the state is not
# 0. Before main sees a line, its input prologue runs on it, if it has one
# (Plan.bend): an abort there ends the iteration before main starts.

# Print the display and go on with the state; print it and end; or fail
# as the Haskell did with `error`.
type Outcome is Data:
  Continue{+display: String, +state: Co.D}
  Stop{+display: String}
  Crash{+msg: String}

def maybe.int(m: Maybe<&2, U32>) -> String:
  match m:
    case Some{n}:
      "Just " ++ U32.show(n)
    case None{}:
      "Nothing"

def user.abort(+s: Co.D, m: Maybe<&2, String>) -> String:
  match m:
    case Some{t}:
      "user abort: " ++ t
    case None{}:
      "user abort invalid data: " ++ Co.show.data(s)

# convertAbortMessage
def abort.message(+x: Co.D) -> String:
  match x:
    case Co.DPair{Co.DPair{Co.DPair{Co.DPair{Co.DPair{Co.DZero{}, Co.DZero{}}, Co.DZero{}}, Co.DZero{}}, Co.DZero{}}, Co.DZero{}}:
      "a step the evaluator would be stuck on"
    case Co.DPair{Co.DZero{}, t}:
      "recursion overflow (should be caught by other means) for rt: " ++ maybe.int(Co.to.int(t))
    case Co.DPair{Co.DPair{Co.DZero{}, Co.DZero{}}, +s}:
      user.abort(s, Co.to.string.d(s))
    case Co.DPair{Co.DPair{Co.DPair{Co.DZero{}, Co.DZero{}}, Co.DZero{}}, Co.DZero{}}:
      "user abort of all possible abort reasons (non-deterministic input)"
    case other:
      "unexpected abort: " ++ Co.show.data(other)

def value.string(+v: Co.D, s: Maybe<&2, String>) -> String:
  match s:
    case Some{t}:
      Sh.string(t)
    case None{}:
      Co.show.data(v)

# A failing check's value, as it reports it (renderValue).
def value.render(+v: Co.D, i: Maybe<&2, U32>) -> String:
  match i:
    case Some{n}:
      U32.show(n)
    case None{}:
      value.string(v, Co.to.string.d(v))

# A failing check aborts with the value that failed it, as `abort` does with a
# message.
def check.message(+x: Co.D) -> String:
  match x:
    case Co.DPair{Co.DPair{Co.DZero{}, Co.DZero{}}, +v}:
      "check failed on " ++ value.render(v, Co.to.int(v))
    case other:
      abort.message(other)

def message.of(k: L.AbortKind, +m: Co.D) -> String:
  match k:
    case L.KRefine{}:
      check.message(m)
    case _:
      abort.message(m)

# An abort's message and what raised it (describeAbort).
def abort.text(+o: L.Origin, +m: Co.D) -> String:
  message.of(L.Origin.kind(o), m) ++ L.origin.suffix(o)

# An abort that fired: what raised it and its message.
type Fired is Data:
  Fired{+o: L.Origin, +m: Co.D}

def first.fired(a: Maybe<&2, Fired>, b: Maybe<&2, Fired>) -> Maybe<&2, Fired>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

# An abort message as data: anything that is neither 0 nor a pair (a
# closure, say) reads as 0 (messageData).
def message.data(v: Co.V) -> Co.D:
  match v:
    case Co.VPair{a, b}:
      Co.DPair{message.data(a), message.data(b)}
    case _:
      Co.DZero{}

# The leftmost abort that has fired in the result (firedAbort): one
# outside every defer, since one under a defer is code that has not run.
# An abort inside another's message is the one that counts.
def fired(x: Co.V) -> Maybe<&2, Fired>:
  match x:
    case Co.VAbort{+o, +m}:
      first.fired(fired(m), Some{Fired{o, message.data(m)}})
    case Co.VPair{a, b}:
      first.fired(fired(a), fired(b))
    case Co.VSetEnv{a}:
      fired(a)
    case Co.VLeft{a}:
      fired(a)
    case Co.VRight{a}:
      fired(a)
    case _:
      None{}

# "Aborted, " and what the abort says (AbortRunTime's show, describeAbort).
def fired.text(f: Fired) -> String:
  match f:
    case Fired{+o, +m}:
      "Aborted, " ++ abort.text(o, m)

def static.text(m: Maybe<&2, Fired>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{f}:
      match f:
        case Fired{+o, +m2}:
          Some{"StaticCheckError " ++ Sh.string(abort.text(o, m2))}

def static.of(st: Rf.St) -> Maybe<&2, String>:
  match st:
    case Rf.SDone{+v, c}:
      static.text(fired(v))
    case _:
      None{}

# What compiling an expression rejects (runStaticChecks, evalStaticCheck): an
# abort that fires evaluating it.
def static.check(+x: Co.V) -> Maybe<&2, String>:
  static.of(Rf.run(x))

# A state of 0 ends the session after this display.
def next(+text: String, st: Co.D) -> Outcome:
  match st:
    case Co.DZero{}:
      Stop{text}
    case other:
      Continue{text, other}

# The display shown, and the state carried on, which must be data.
def shown(+d: Co.V, m: Maybe<&2, String>, st: Maybe<&2, Co.D>) -> Outcome:
  match m:
    case Some{text}:
      match st:
        case Some{s}:
          next(text, s)
        case None{}:
          Crash{"funWrap conversion error3"}
    case None{}:
      Stop{"error converting display value:\n" ++ Co.pretty(d)}

def converted(abort: Bool, +x: Co.V) -> Outcome:
  match abort:
    case True{}:
      Stop{"error converting iteration value:\n" ++ Co.show(x)}
    case False{}:
      match x:
        case Co.VZero{}:
          Stop{"aborted"}
        case Co.VPair{+d, st}:
          shown(d, Co.to.string(d), Co.data(st))
        case _:
          Crash{"Telomare.Driver.funWrapWith: unexpected iteration value"}

def value(m: Maybe<&2, Fired>, +x: Co.V) -> Outcome:
  match m:
    case Some{f}:
      Stop{"runtime error:\n" ++ fired.text(f)}
    case None{}:
      converted(False{}, x)

# How a program runs: sized, under the IC's default fuel; or unsized
# (--fast), each iteration capped at fuel interactions, 0 for no cap (the
# most a U32 counts).
type How is Data:
  Sized{}
  Fast{+fuel: U32}

def fuel(h: How) -> U32:
  match h:
    case Sized{}:
      IC.default.fuel()
    case Fast{+n}:
      Bool.pick(U32, U32.is_zero(n), 4294967295, n)

def failed(f: IC.Fault) -> Outcome:
  Stop{"runtime error:\nGeneric Runtime Error: IC runtime: " ++ IC.fault.show(f) ++ " -- " ++ Co.show(Co.VZero{})}

# Out of fuel, an unsized run says why nothing stopped it sooner.
def failed.fast(f: IC.Fault) -> Outcome:
  match f:
    case IC.FuelExhausted{n}:
      Stop{"runtime error: out of fuel after " ++ Mt.commas(n) ++ " interactions.\n"
        ++ "This run is not sized, so nothing proved it terminates. Raise the cap with --fuel N, or lift it entirely with --fuel 0."}
    case other:
      failed(other)

def failed.how(h: How, f: IC.Fault) -> Outcome:
  match h:
    case Sized{}:
      failed(f)
    case Fast{n}:
      failed.fast(f)

def prologue.aborted(m: Maybe<&2, Fired>) -> Maybe<&2, Outcome>:
  match m:
    case Some{f}:
      Some{Stop{"runtime error:\n" ++ fired.text(f)}}
    case None{}:
      None{}

# What the prologue's run says: nothing when the line passes, else how the
# session ends: with the first failing check's abort, or the runtime's failure.
def prologue.verdict(h: How, r: IC.RB) -> Maybe<&2, Outcome>:
  match r:
    case IC.RBErr{f}:
      Some{failed.how(h, f)}
    case IC.RBOk{x}:
      prologue.aborted(fired(x))

# What an iteration's result means for the session.
def outcome(h: How, r: IC.RB) -> Outcome:
  match r:
    case IC.RBErr{f}:
      failed.how(h, f)
    case IC.RBOk{+x}:
      value(fired(x), x)

# EAL's capture layouts for a sized program, inferred over it
# (ealCaptureLayouts of inferEALCompiled).
def layouts(+expr: Co.V) -> Map<&2, Lf.Shape>:
  EM.lr.layouts(EM.lr.of(False{}, Lf.defer.lift.expr(expr)))

# The input prologue's certificate: a program of its own, certified on its own,
# its guidance added to main's and its refusal named (programWith).
def prologue.plan(p: Maybe<&2, Co.V>) -> Result<&2, &2, String, Map<&2, Lf.Shape>>:
  match p:
    case None{}:
      Done{Map.new(&2, Lf.Shape)}
    case Some{+v}:
      EM.lr.plan(EM.lr.full(False{}, Lf.defer.lift.expr(v)))

def plans(m: Result<&2, &2, String, Map<&2, Lf.Shape>>, p: Result<&2, &2, String, Map<&2, Lf.Shape>>) -> Result<&2, &2, String, Map<&2, Lf.Shape>>:
  match m:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      match p:
        case Fail{e}:
          Fail{"input prologue: " ++ e}
        case Done{b}:
          Done{Map.union(&2, Lf.Shape, a, b)}

# programPlan of certifiedProgramFrom: the capture layouts compiling gives a
# sized program (plain: Size's Sized.plain), derived from the faithful
# certificate of the program it was sized from (run, sized with counts, with
# the checks the analysis erased gone), since plain is that program under the
# sizing substitution, else inferred over plain; or, when the sized main or
# its prologue does not certify, the refusal the IC runtime gives instead of a
# session. The session runs Sized.expr, plain with what the erasure checker
# proved erased: its bodies that plain shares (by hash) run under these
# layouts, the erased ones under none.
def plan.from(+run: T.C, +counts: List<&2, E.TS>, +keep: Maybe<&2, Set()>, +plain: Co.V, +prologue: Maybe<&2, Co.V>) -> Result<&2, &2, String, Map<&2, Lf.Shape>>:
  plans(EM.lr.plan(EM.certified.program(Lf.defer.lift(run), counts, keep, plain)), prologue.plan(prologue))

# A compile's layouts; a program that does not certify has none.
def layouts.of(r: Result<&2, &2, String, Map<&2, Lf.Shape>>) -> Map<&2, Lf.Shape>:
  match r:
    case Done{ls}:
      ls
    case Fail{why}:
      Map.new(&2, Lf.Shape)

# prepareEntry: the sized program prepared for runs under EAL's capture
# layouts for it, so closures are copied as EAL planned.
def prepared(+expr: Co.V) -> IC.Prog:
  IC.prepare(expr, layouts(expr))

# What the session runs: main, and the input prologue it runs on each line
# before main, if main has one.
type Prog is Data:
  Prog{+main: IC.Prog, +prologue: Maybe<&2, IC.Prog>}

# A program no prologue comes before.
def alone(p: IC.Prog) -> Prog:
  Prog{p, None{}}

def prologue.prog(p: Maybe<&2, Co.V>, +ls: Map<&2, Lf.Shape>) -> Maybe<&2, IC.Prog>:
  match p:
    case None{}:
      None{}
    case Some{+v}:
      Some{IC.prepare(v, ls)}

# What the session runs, from main's sized program and its prologue, under the
# layouts compiling gave them.
def session(+main: Co.V, +ls: Map<&2, Lf.Shape>, p: Maybe<&2, Co.V>) -> Prog:
  Prog{IC.prepare(main, ls), prologue.prog(p, ls)}

# The session (evalSessionCore)
# -----------------------------
#
# One iteration at a time, between the effects the drivers own: Main reads
# standard input and prints, the tests feed given lines and keep the
# displays. Every turn carries what the session has spent so far, which is
# what `--meter` reports.

# What the session has spent: interactions and, unsized, each recursion
# site's unrolls.
type Cost is Data:
  Cost{+spent: U32, +unrolls: List<&2, IC.Unroll>}

def cost.none() -> Cost:
  Cost{0, []}

def cost.spent(c: Cost) -> U32:
  match c:
    case Cost{spent, unrolls}:
      spent

# vs's unrolls added to us.
def unrolls.plus(vs: List<&2, IC.Unroll>, us: List<&2, IC.Unroll>) -> List<&2, IC.Unroll>:
  match vs:
    case Nil{}:
      us
    case Con{v, rest}:
      match v:
        case IC.Unroll{tok, n}:
          unrolls.plus(rest, IC.unroll.add(us, tok, n))

def cost.plus(c: Cost, +spent: U32, us: List<&2, IC.Unroll>) -> Cost:
  match c:
    case Cost{+before, vs}:
      Cost{(before + spent : U32), unrolls.plus(us, vs)}

# A display to show, then either a line to read for the next iteration,
# the end of the session, or a failure.
type Turn is Type:
  Asks{net: IC.Net, display: String, state: Co.D, cost: Cost}
  Ends{display: String, cost: Cost}
  Fails{msg: String, cost: Cost}

def turn.of(net: IC.Net, o: Outcome, cost: Cost) -> Turn:
  match o:
    case Continue{display, st}:
      Asks{net, display, st, cost}
    case Stop{display}:
      Ends{display, cost}
    case Crash{msg}:
      Fails{msg, cost}

def turn(h: How, r: IC.Run, before: Cost) -> Turn:
  match r:
    case IC.Run{net, out, +spent, unrolls}:
      turn.of(net, outcome(h, out), cost.plus(before, spent, unrolls))

# The first iteration runs on 0, with no prologue.
def start(p: Prog, +h: How) -> Turn:
  match p:
    case Prog{+m, g}:
      turn(h, IC.run(m, IC.net.new(m), Co.DZero{}, fuel(h)), cost.none())

def checked(v: Maybe<&2, Outcome>, +h: How, +m: IC.Prog, net: IC.Net, +input: Co.D, +cost: Cost) -> Turn:
  match v:
    case None{}:
      turn(h, IC.run(m, net, input, fuel(h)), cost)
    case Some{o}:
      turn.of(net, o, cost)

# Main on input, once the prologue's run r passes it. The prologue's
# interactions count; its unrolls do not, since its recursion sites are its own
# and the meter's table locates main's.
def guarded(r: IC.Run, +h: How, +m: IC.Prog, net: IC.Net, +input: Co.D, cost: Cost) -> Turn:
  match r:
    case IC.Run{gnet, out, +spent, unrolls}:
      checked(prologue.verdict(h, out), h, m, net, input, cost.plus(cost, spent, []))

def answered(g: Maybe<&2, IC.Prog>, +h: How, +m: IC.Prog, net: IC.Net, +input: Co.D, cost: Cost) -> Turn:
  match g:
    case None{}:
      turn(h, IC.run(m, net, input, fuel(h)), cost)
    case Some{+gp}:
      guarded(IC.run(gp, IC.net.new(gp), input, fuel(h)), h, m, net, input, cost)

# The next iteration runs on the line read and the state the last one left,
# once the prologue passes them.
def answer(p: Prog, +h: How, net: IC.Net, +line: String, st: Co.D, cost: Cost) -> Turn:
  match p:
    case Prog{+m, g}:
      answered(g, h, m, net, Co.DPair{Co.of.string(line), st}, cost)

# The same iterations as the command runs them, in IO: the IC run by ~rt,
# IC.run itself (run.pure) or bend/Native.bend's, whose loop is C
# (bend/effs/ic.c) and gives the same run.

def Runner() -> Type:
  IC.Prog -> IC.Net -> Co.D -> U32 -> IO(IC.Run)

def run.pure(p: IC.Prog, net: IC.Net, input: Co.D, fuel: U32) -> IO(IC.Run):
  IO.pure(IC.Run, IC.run(p, net, input, fuel))

def turn.by(~rt: Runner(), +h: How, +m: IC.Prog, net: IC.Net, +input: Co.D, cost: Cost) -> IO(Turn):
  do IO<Turn>:
    r : IC.Run <- rt(m, net, input, fuel(h))
    return turn(h, r, cost)

def start.by(~rt: Runner(), p: Prog, +h: How) -> IO(Turn):
  match p:
    case Prog{+m, g}:
      turn.by(~rt, h, m, IC.net.new(m), Co.DZero{}, cost.none())

def checked.by(~rt: Runner(), v: Maybe<&2, Outcome>, +h: How, +m: IC.Prog, net: IC.Net, +input: Co.D, +cost: Cost) -> IO(Turn):
  match v:
    case None{}:
      turn.by(~rt, h, m, net, input, cost)
    case Some{o}:
      IO.pure(Turn, turn.of(net, o, cost))

def guarded.by(~rt: Runner(), r: IC.Run, +h: How, +m: IC.Prog, net: IC.Net, +input: Co.D, cost: Cost) -> IO(Turn):
  match r:
    case IC.Run{gnet, out, +spent, unrolls}:
      checked.by(~rt, prologue.verdict(h, out), h, m, net, input, cost.plus(cost, spent, []))

def answered.by(~rt: Runner(), g: Maybe<&2, IC.Prog>, +h: How, +m: IC.Prog, net: IC.Net, +input: Co.D, cost: Cost) -> IO(Turn):
  match g:
    case None{}:
      turn.by(~rt, h, m, net, input, cost)
    case Some{+gp}:
      do IO<Turn>:
        r : IC.Run <- rt(gp, IC.net.new(gp), input, fuel(h))
        guarded.by(~rt, r, h, m, net, input, cost)

def answer.by(~rt: Runner(), p: Prog, +h: How, net: IC.Net, +line: String, st: Co.D, cost: Cost) -> IO(Turn):
  match p:
    case Prog{+m, g}:
      answered.by(~rt, g, h, m, net, Co.DPair{Co.of.string(line), st}, cost)

# A session on given lines, for the tests: the displays, newest first, and
# what it spent. It ends where the session would, or where the lines run
# out.
type Replay is Data:
  Replay{+shown: List<&2, String>, +cost: Cost}

# What the session showed when it stopped: the turn's display (or its
# failure) and what it spent.
def replay.end(t: Turn, +shown: List<&2, String>) -> Replay:
  match t:
    case Asks{net, display, st, cost}:
      Replay{display <> shown, cost}
    case Ends{display, cost}:
      Replay{display <> shown, cost}
    case Fails{msg, cost}:
      Replay{msg <> shown, cost}

def replay.go(lines: List<&2, String>, +p: Prog, +h: How, t: Turn, +shown: List<&2, String>) -> Replay:
  match lines:
    case Nil{}:
      replay.end(t, shown)
    case Con{line, rest}:
      match t:
        case Asks{net, display, st, cost}:
          replay.go(rest, p, h, answer(p, h, net, line, st, cost), display <> shown)
        case other:
          replay.end(other, shown)

def replay(+p: Prog, +h: How, lines: List<&2, String>) -> Replay:
  replay.go(lines, p, h, start(p, h), [])
