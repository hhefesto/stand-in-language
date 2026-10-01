import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EAL.bend as EAL
import ../IC.bend as IC
import ../Session.bend as Ss

# `phases MODULE [LINE...]`: the command's stages one after another, each
# timed: the front end, certification, sizing, the capture layouts, the
# net's preparation and the session on those lines.

def ms(+t0: Nat, +t1: Nat) -> String:
  U32.show(U32.from_nat((t1 - t0 : Nat))) ++ " ms"

def spent(r: Ss.Replay) -> U32:
  match r:
    case Ss.Replay{xs, n}:
      n

def verdict(m: Maybe<&2, EAL.Err>) -> String:
  match m:
    case None{}:
      "ok"
    case Some{e}:
      "fails"

def run(+expr: E.X, lines: List<&2, String>, +t2: Nat) -> IO(Unit):
  do IO<Unit>:
    +lay : Map<&2, Lf.Shape> = EAL.layouts(Lf.defer.lift(Lf.of.expr(expr)))
    +t3 : Nat <- IO.now()
    IO.print("layouts " ++ ms(t2, t3) ++ ": " ++ U32.show(U32.from_nat(Map.size(&2, Lf.Shape, lay))))
    +p : IC.Prog = IC.prepare(expr, lay)
    +t4 : Nat <- IO.now()
    IO.print("prepare " ++ ms(t3, t4))
    +n : U32 = spent(Ss.replay(p, lines))
    t5 : Nat <- IO.now()
    IO.print("session " ++ ms(t4, t5) ++ ": " ++ U32.show(n) ++ " interactions")

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, lines: List<&2, String>, +t2: Nat) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          run(expr, lines, t2)

def compiled(r: Result<&2, &2, String, Fr.Terms>, lines: List<&2, String>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          do IO<Unit>:
            +t1 : Nat <- IO.now()
            IO.print("front " ++ ms(t0, t1))
            +c : String = verdict(EAL.certify(Lf.defer.lift(cert)))
            +t2 : Nat <- IO.now()
            IO.print("certify " ++ ms(t1, t2) ++ ": " ++ c)
            +z : Result<&2, &2, Sz.SizeFail, Sz.Sized> = Sz.size(65536, True{}, E.of.term3(run))
            +t3 : Nat <- IO.now()
            IO.print("size " ++ ms(t2, t3))
            sized(z, lines, t3)

def loaded(+entry: String, lines: List<&2, String>, r: Result<&1, &1, String, List<&2, Fr.Src>>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      compiled(Fr.compile(srcs, entry), lines, t0)

def lines.of(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      x <> lines.of(rest)

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +entry <> rest:
      do IO<Unit>:
        +t0 : Nat <- IO.now()
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, lines.of(rest), r, t0)
    case _:
      IO.print("usage: phases MODULE [LINE...]")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
