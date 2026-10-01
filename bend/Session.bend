import Base
import ./Expr.bend as E
import ./Lift.bend as Lf
import ./EAL.bend as EAL
import ./IC.bend as IC

# One iteration's outcome, as the session prints it (haskell-final's
# Driver.funWrapWith and evalSessionCore, with IC.icRuntimeResult and
# IR.Base.convertAbortMessage). A program is run on 0 first, then on
# (line, state) for each line read, while it answers (display, state) and
# the state is not 0.

# Print the display and go on with the state; print it and end; or fail
# as the Haskell did with `error`.
type Outcome is Data:
  Continue{+display: String, +state: E.X}
  Stop{+display: String}
  Crash{+msg: String}

def maybe.int(m: Maybe<&2, U32>) -> String:
  match m:
    case Some{n}:
      "Just " ++ U32.show(n)
    case None{}:
      "Nothing"

def user.abort(+s: E.X, m: Maybe<&2, String>) -> String:
  match m:
    case Some{t}:
      "user abort: " ++ t
    case None{}:
      "user abort invalid data: " ++ E.show(s)

# convertAbortMessage
def abort.message(+x: E.X) -> String:
  match x:
    case E.XPair{E.XZero{}, t}:
      "recursion overflow (should be caught by other means) for rt: " ++ maybe.int(E.to.int(t))
    case E.XPair{E.XPair{E.XZero{}, E.XZero{}}, +s}:
      user.abort(s, E.to.string(s))
    case E.XPair{E.XPair{E.XPair{E.XZero{}, E.XZero{}}, E.XZero{}}, E.XZero{}}:
      "user abort of all possible abort reasons (non-deterministic input)"
    case other:
      "unexpected abort: " ++ E.show(other)

def first.aborted(a: Maybe<&2, E.X>, b: Maybe<&2, E.X>) -> Maybe<&2, E.X>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

# The leftmost aborted message anywhere in the result (icRuntimeResult).
def aborted(x: E.X) -> Maybe<&2, E.X>:
  match x:
    case E.XAborted{m}:
      Some{m}
    case E.XPair{a, b}:
      first.aborted(aborted(a), aborted(b))
    case E.XDefer{fi, b}:
      aborted(b)
    case E.XSetEnv{a}:
      aborted(a)
    case E.XLeft{a}:
      aborted(a)
    case E.XRight{a}:
      aborted(a)
    case _:
      None{}

# An Abort left in the result (a CompiledExpr that is no StuckExpr).
def has.abort(x: E.X) -> Bool:
  match x:
    case E.XAbort{}:
      True{}
    case E.XPair{a, b}:
      has.abort(a) || has.abort(b)
    case E.XDefer{fi, b}:
      has.abort(b)
    case E.XSetEnv{a}:
      has.abort(a)
    case E.XLeft{a}:
      has.abort(a)
    case E.XRight{a}:
      has.abort(a)
    case _:
      False{}

def is.data(x: E.X) -> Bool:
  match x:
    case E.XZero{}:
      True{}
    case E.XPair{a, b}:
      is.data(a) && is.data(b)
    case _:
      False{}

# A state of 0 ends the session after this display.
def next(+text: String, st: E.X) -> Outcome:
  match st:
    case E.XZero{}:
      Stop{text}
    case other:
      Continue{text, other}

def shown(+d: E.X, +st: E.X, m: Maybe<&2, String>, data: Bool) -> Outcome:
  match m:
    case Some{text}:
      match data:
        case True{}:
          next(text, st)
        case False{}:
          Crash{"funWrap conversion error3"}
    case None{}:
      Stop{"error converting display value:\n" ++ E.pretty(d)}

def converted(abort: Bool, +x: E.X) -> Outcome:
  match abort:
    case True{}:
      Stop{"error converting iteration value:\n" ++ E.show(x)}
    case False{}:
      match x:
        case E.XZero{}:
          Stop{"aborted"}
        case E.XPair{+d, +st}:
          shown(d, st, E.to.string(d), is.data(st))
        case _:
          Crash{"Telomare.Driver.funWrapWith: unexpected iteration value"}

def value(m: Maybe<&2, E.X>, +x: E.X) -> Outcome:
  match m:
    case Some{msg}:
      Stop{"runtime error:\nAborted, " ++ abort.message(msg)}
    case None{}:
      converted(has.abort(x), x)

# What an iteration's result means for the session.
def outcome(r: IC.RB) -> Outcome:
  match r:
    case IC.RBErr{e}:
      Stop{"runtime error:\nGeneric Runtime Error: IC runtime: " ++ e ++ " -- " ++ E.show(E.XZero{})}
    case IC.RBOk{+x}:
      value(aborted(x), x)

# prepareEntry: the sized program prepared for runs under EAL's capture
# layouts for it, so closures are copied as EAL planned.
def prepared(+expr: E.X) -> IC.Prog:
  IC.prepare(expr, EAL.layouts(Lf.defer.lift(Lf.of.expr(expr))))

# The session (evalSessionCore)
# -----------------------------
#
# One iteration at a time, between the effects the drivers own: Main reads
# standard input and prints, the tests feed given lines and keep the
# displays. Every turn carries the interactions the session has spent so
# far, which is what `--meter` reports.

# A display to show, then either a line to read for the next iteration,
# the end of the session, or a failure.
type Turn is Type:
  Asks{net: IC.Net, display: String, state: E.X, spent: U32}
  Ends{display: String, spent: U32}
  Fails{msg: String, spent: U32}

def turn.of(net: IC.Net, o: Outcome, +spent: U32) -> Turn:
  match o:
    case Continue{display, st}:
      Asks{net, display, st, spent}
    case Stop{display}:
      Ends{display, spent}
    case Crash{msg}:
      Fails{msg, spent}

def turn(r: IC.Run, +before: U32) -> Turn:
  match r:
    case IC.Run{net, out, spent}:
      turn.of(net, outcome(out), (before + spent : U32))

# The first iteration runs on 0.
def start(+p: IC.Prog) -> Turn:
  turn(IC.run(p, IC.net.new(p), E.XZero{}, IC.default.fuel()), 0)

# The next iteration runs on the line read and the state the last one left.
def answer(+p: IC.Prog, net: IC.Net, +line: String, st: E.X, +spent: U32) -> Turn:
  turn(IC.run(p, net, E.XPair{E.of.string(line), st}, IC.default.fuel()), spent)

# A session on given lines, for the tests: the displays, newest first, and
# the interactions spent. It ends where the session would, or where the
# lines run out.
type Replay is Data:
  Replay{+shown: List<&2, String>, +spent: U32}

# What the session showed when it stopped: the turn's display (or its
# failure) and what it spent.
def replay.end(t: Turn, +shown: List<&2, String>) -> Replay:
  match t:
    case Asks{net, display, st, spent}:
      Replay{display <> shown, spent}
    case Ends{display, spent}:
      Replay{display <> shown, spent}
    case Fails{msg, spent}:
      Replay{msg <> shown, spent}

def replay.go(lines: List<&2, String>, +p: IC.Prog, t: Turn, +shown: List<&2, String>) -> Replay:
  match lines:
    case Nil{}:
      replay.end(t, shown)
    case Con{line, rest}:
      match t:
        case Asks{net, display, st, spent}:
          replay.go(rest, p, answer(p, net, line, st, spent), display <> shown)
        case other:
          replay.end(other, shown)

def replay(+p: IC.Prog, lines: List<&2, String>) -> Replay:
  replay.go(lines, p, start(p), [])
