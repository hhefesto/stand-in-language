import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Plan.bend as Pl
import ../Expr.bend as E
import ../Core.bend as Co

# `plantime [MODULE]`: sizing with the check plan, then the check analysis's
# runs alone, timed, with the steps each took: main on its symbolic input
# (the plan's), and the two that decide the loop's calls (master's
# reachableFailures, since 98c963c2's merge): main on 0, and the step
# program. MODULE is tictactoe by default; run it where MODULE.tel is.

def ms(+t0: Nat, +t1: Nat) -> String:
  U32.show(U32.from_nat((t1 - t0 : Nat))) ++ " ms"

def timed(+name: String, +s: String, +t0: Nat) -> IO(Nat):
  do IO<Nat>:
    IO.print(name ++ ": " ++ s)
    +t1 : Nat <- IO.now()
    IO.print("  " ++ ms(t0, t1))
    return t1

def analysed(r: Result<&2, &2, String, Co.V>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("no core: " ++ e)
    case Done{+v}:
      do IO<Unit>:
        +t1 : Nat <- timed("main", Pl.stats(v), t0)
        +t2 : Nat <- timed("main on 0", Pl.stats.of(Pl.run.prog(Pl.VlZero{}, v)), t1)
        +t3 : Nat <- timed("the step program", Pl.stats.of(Pl.run.prog(Pl.step.input(), Pl.step.program(v))), t2)
        IO.print("done")

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, +run: T.C, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{+counts, expr, checks, plain, p}:
          do IO<Unit>:
            IO.print("counts " ++ Nat.show(List.length(&2, E.TS, counts)))
            +t1 : Nat <- IO.now()
            IO.print("size and plan " ++ ms(t0, t1))
            analysed(E.core(E.origins(run), Sz.program(counts, None{}, False{}, E.app(E.of.term3(run), E.XVar{""}), True{})), t1)

def termed(r: Result<&2, &2, String, T.C>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{+run}:
      do IO<Unit>:
        +t0 : Nat <- IO.now()
        sized(Sz.size.checked(65536, True{}, run, Sz.WantPlain{}), run, t0)

def loaded(+entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{srcs}:
      termed(Fr.compile(srcs, entry))

def entry.of(xs: List<String>) -> String:
  match xs:
    case self <> m <> rest:
      m
    case _:
      "tictactoe"

def go(+m: String) -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(m)
    loaded(m, r)

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    go(entry.of(xs))
