import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EAL.bend as EAL
import ../Session.bend as Ss

# `guarded MODULE`: for main sized as a guarded session sizes it, for main
# sized alone, and for the guard: EAL's verdict on the sized term, and how
# many capture layouts it gives.

def verdict(m: Maybe<&2, EAL.Err>) -> String:
  match m:
    case None{}:
      "certified"
    case Some{e}:
      "not certified"

def of.sized(+name: String, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      name ++ ": sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{cs, +expr, checks}:
          +l = Lf.defer.lift(Lf.of.expr(expr))
          name ++ ": " ++ verdict(EAL.certify(l)) ++ ", " ++ U32.show(U32.from_nat(Map.size(&2, Lf.Shape, Ss.layouts(expr)))) ++ " layouts"

def guard.of(g: Maybe<&2, T.C>) -> String:
  match g:
    case None{}:
      "no guard"
    case Some{t}:
      of.sized("guard", Sz.size(65536, True{}, E.of.term3(t)))

def shown(r: Result<&2, &2, String, Fr.Program>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{p}:
      match p:
        case Fr.Program{+run, +g, +boundary}:
          of.sized("main, guarded", Sz.size.guarded(65536, boundary, g, E.of.term3(run))) ++ "\n"
            ++ of.sized("main, alone", Sz.size(65536, True{}, E.of.term3(run))) ++ "\n" ++ guard.of(g)

def run(+entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{srcs}:
      IO.print(shown(Fr.compile.program(srcs, entry)))

def run.args(a: List<String>) -> IO(Unit):
  match a:
    case self <> +m <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(m)
        run(m, r)
    case _:
      IO.print("usage: guarded MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    a : List<String> <- IO.args()
    run.args(a)
