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

# A session on given lines (evalLoopIC with its inputs), for the tests: the
# displays, newest first, and the interactions every iteration spent. It
# ends where the session would, or where the lines run out.
type Replay is Data:
  Replay{+shown: List<&2, String>, +spent: U32}

type RS is Type:
  RSRun{net: IC.Net, input: E.X}
  RSOut{net: IC.Net, o: Outcome, spent: U32}

def ran(r: IC.Run) -> RS:
  match r:
    case IC.Run{net, out, spent}:
      RSOut{net, outcome(out), spent}

def replay.go(fuel: Nat, +p: IC.Prog, s: RS, lines: List<&2, String>, +shown: List<&2, String>, +spent: U32) -> Replay:
  match fuel:
    case 0n:
      Replay{shown, spent}
    case 1n+k:
      match s:
        case RSRun{net, input}:
          replay.go(k, p, ran(IC.run(p, net, input, IC.default.fuel())), lines, shown, spent)
        case RSOut{net, o, n}:
          match o:
            case Continue{display, st}:
              match lines:
                case Nil{}:
                  Replay{display <> shown, (spent + n : U32)}
                case Con{line, rest}:
                  replay.go(k, p, RSRun{net, E.XPair{E.of.string(line), st}}, rest, display <> shown, (spent + n : U32))
            case Stop{display}:
              Replay{display <> shown, (spent + n : U32)}
            case Crash{msg}:
              Replay{msg <> shown, (spent + n : U32)}

def replay(+p: IC.Prog, lines: List<&2, String>) -> Replay:
  replay.go(U32.to_nat(65536), p, RSRun{IC.net.new(p), E.XZero{}}, lines, [], 0)
