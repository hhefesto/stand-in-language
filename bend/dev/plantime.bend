import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Plan.bend as Pl
import ../Expr.bend as E
import ../Core.bend as Co

# `plantime MODULE`: sizing with the check plan, and the check analysis's run
# alone, timed, with the steps it took.

def ms(+t0: Nat, +t1: Nat) -> String:
  U32.show(U32.from_nat((t1 - t0 : Nat))) ++ " ms"

def analysed(r: Result<&2, &2, String, Co.V>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("no core: " ++ e)
    case Done{v}:
      do IO<Unit>:
        +s : String = Pl.stats(v)
        IO.print(s)
        +t1 : Nat <- IO.now()
        IO.print("the analysis's run " ++ ms(t0, t1))

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

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules("tictactoe")
    loaded("tictactoe", r)
