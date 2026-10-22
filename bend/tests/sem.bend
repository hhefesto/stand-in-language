import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Core.bend as Co
import ../IC.bend as IC
import ../Lift.bend as Lf
import ../Session.bend as Ss
import ../Sem.bend as Sm
import ../Text.bend as Tx

# The meaning against the runtime: a program's session, run by Sem (the
# definition LAWS.bend is stated over) and by the IC, shows the same
# displays. This is the evidence that Sem means what the IC does (DESIGN
# §6: the reference the one runtime is checked against). One `ok NAME`
# line per group (FAIL NAME when it breaks). Run from the source root.

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

def all(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      b && all(rest)

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def same(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      List.is_empty(&2, String, ys)
    case Con{x, rest}:
      match ys:
        case Nil{}:
          False{}
        case Con{y, more}:
          String.eq(x, y) && same(rest, more)

# Sem's answer as the IC reads its result back
# -------------------------------------------

def stuck(o: Sm.O) -> Bool:
  match o:
    case Sm.OStuck{}:
      True{}
    case Sm.OPair{a, b}:
      stuck(a) || stuck(b)
    case _:
      False{}

def data(o: Sm.O) -> Co.D:
  match o:
    case Sm.OPair{a, b}:
      Co.DPair{data(a), data(b)}
    case _:
      Co.DZero{}

def value(o: Sm.O) -> Co.V:
  match o:
    case Sm.OZero{}:
      Co.VZero{}
    case Sm.OPair{a, b}:
      Co.VPair{value(a), value(b)}
    case Sm.OCode{fi}:
      Co.VDefer{fi, Co.VZero{}}
    case Sm.OGate{}:
      Co.VGate{}
    case Sm.OAbort{}:
      Co.VAbort{}
    case Sm.OAborted{at, m}:
      Co.VAborted{data(m)}
    case Sm.OStuck{}:
      Co.VZero{}
    case Sm.OHole{p}:
      Co.VZero{}

def read.of(is.stuck: Bool, +o: Sm.O) -> IC.RB:
  match is.stuck:
    case True{}:
      IC.RBErr{IC.Stuck{"stuck (Sem)"}}
    case False{}:
      IC.RBOk{value(o)}

def rb(r: Sm.R) -> IC.RB:
  match r:
    case Sm.Obs{+o}:
      read.of(stuck(o), o)
    case Sm.Spent{}:
      IC.RBErr{IC.FuelExhausted{0}}
    case _:
      IC.RBErr{IC.Stuck{"not a plain run (Sem)"}}

def run(+main: E.X, input: Co.D) -> IC.RB:
  rb(Sm.run(Sm.fuel(), Sm.plain(), main, Sm.of.data(input)))

# A session, run by Sem
# ---------------------

type Prog is Data:
  Prog{+main: E.X, +guard: Maybe<&2, E.X>}

def checked(v: Maybe<&2, Ss.Outcome>, +m: E.X, +input: Co.D) -> Ss.Outcome:
  match v:
    case None{}:
      Ss.outcome(Ss.Sized{}, run(m, input))
    case Some{o}:
      o

def answered(g: Maybe<&2, E.X>, +m: E.X, +input: Co.D) -> Ss.Outcome:
  match g:
    case None{}:
      Ss.outcome(Ss.Sized{}, run(m, input))
    case Some{+gx}:
      checked(Ss.guard.verdict(Ss.Sized{}, run(gx, input)), m, input)

def answer(p: Prog, +line: String, st: Co.D) -> Ss.Outcome:
  match p:
    case Prog{+m, g}:
      answered(g, m, Co.DPair{Co.of.string(line), st})

def ended(o: Ss.Outcome, +shown: List<&2, String>) -> List<&2, String>:
  match o:
    case Ss.Continue{display, st}:
      display <> shown
    case Ss.Stop{display}:
      display <> shown
    case Ss.Crash{msg}:
      msg <> shown

def replay.go(lines: List<&2, String>, +p: Prog, o: Ss.Outcome, +shown: List<&2, String>) -> List<&2, String>:
  match lines:
    case Nil{}:
      ended(o, shown)
    case Con{line, rest}:
      match o:
        case Ss.Continue{display, st}:
          replay.go(rest, p, answer(p, line, st), display <> shown)
        case other:
          ended(other, shown)

def start(p: Prog) -> Ss.Outcome:
  match p:
    case Prog{+m, g}:
      Ss.outcome(Ss.Sized{}, run(m, Co.DZero{}))

def replay(+p: Prog, lines: List<&2, String>) -> List<&2, String>:
  replay.go(lines, p, start(p), [])

# The same session on the IC
# --------------------------

def ic.prog(+expr: Co.V) -> IC.Prog:
  IC.prepare(expr, Map.new(&2, Lf.Shape))

def ic.guard(g: Maybe<&2, Co.V>) -> Maybe<&2, IC.Prog>:
  match g:
    case None{}:
      None{}
    case Some{+x}:
      Some{ic.prog(x)}

def shown(r: Ss.Replay) -> List<&2, String>:
  match r:
    case Ss.Replay{s, cost}:
      s

def ic.replay(+main: Co.V, g: Maybe<&2, Co.V>, lines: List<&2, String>) -> List<&2, String>:
  shown(Ss.replay(Ss.Prog{ic.prog(main), ic.guard(g)}, Ss.Sized{}, lines))

def sem.guard(g: Maybe<&2, Co.V>) -> Maybe<&2, E.X>:
  match g:
    case None{}:
      None{}
    case Some{x}:
      Some{Sm.of.core(x)}

# Both sessions agree.
def agree(+main: Co.V, +g: Maybe<&2, Co.V>, +lines: List<&2, String>) -> Bool:
  same(replay(Prog{Sm.of.core(main), sem.guard(g)}, lines), ic.replay(main, g, lines))

# Compiling, as the command does
# ------------------------------

def guard.sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Maybe<&2, Co.V>:
  match r:
    case Fail{f}:
      None{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks}:
          Some{expr}

def guard.of(m: Maybe<&2, T.C>) -> Maybe<&2, Co.V>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      guard.sized(Sz.size(65536, True{}, E.of.term3(t)))

def sized(g: Maybe<&2, Co.V>, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, +lines: List<&2, String>) -> Bool:
  match r:
    case Fail{f}:
      False{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, +expr, checks}:
          agree(expr, g, lines)

def compiled(r: Result<&2, &2, String, Fr.Program>, +lines: List<&2, String>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{p}:
      match p:
        case Fr.Program{run, +g, +boundary}:
          sized(guard.of(g), Sz.size.guarded(65536, boundary, g, E.of.term3(run)), lines)

def agrees(srcs: List<&2, Fr.Src>, +entry: String, +lines: List<&2, String>) -> Bool:
  compiled(Fr.compile.program(srcs, entry), lines)

def report(+prelude: String, +plus: String, +tc: String, +ttt: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("sem-tc_ultra_minimal", agrees([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal", [])))
    IO.print(verdict("sem-simpleplus", all([
      agrees([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus", ["3 4"]),
      agrees([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus", ["9 9"]),
      agrees([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus", ["9 a"])])))
    IO.print(verdict("sem-tictactoe", all([
      agrees([Fr.Src{"Prelude", prelude}, Fr.Src{"tictactoe", ttt}], "tictactoe", ["1", "4", "2", "5", "3"]),
      agrees([Fr.Src{"Prelude", prelude}, Fr.Src{"tictactoe", ttt}], "tictactoe", ["1", "9", "2", "8", "3"]),
      agrees([Fr.Src{"Prelude", prelude}, Fr.Src{"tictactoe", ttt}], "tictactoe", ["5", "5", "x", "10", "", "q"])])))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("simpleplus.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    report(text(prelude), text(plus), text(tc), text(ttt))
