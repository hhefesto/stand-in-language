import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EAL.bend as EAL

# `bodyerrs MODULE`: every lifted body's standalone verdict (summarizeBody),
# on the certified term and on the sized one, with the failure's text.

def verdict(m: Maybe<&2, EAL.Err>) -> String:
  match m:
    case None{}:
      "ok"
    case Some{e}:
      EAL.render(e)

def bd.show(m: Maybe<&2, EAL.Bd>, +p: EAL.P) -> String:
  match m:
    case None{}:
      "missing"
    case Some{b}:
      match b:
        case EAL.Bd{+h, +fi, +dup, +t}:
          h ++ " " ++ verdict(EAL.standalone(p, EAL.Bd{h, fi, dup, t}))

def each(k: Nat, +p: EAL.P, +r: U32) -> IO(Unit):
  match k:
    case 0n:
      IO.print("end")
    case 1n+j:
      do IO<Unit>:
        IO.print(bd.show(EAL.body.at(p, r), p))
        each(j, p, (r + 1 : U32))

def all(t: Lf.Lifted) -> IO(Unit):
  match t:
    case Lf.Lifted{+bodies, main}:
      each(U32.to_nat(EAL.p.n(EAL.program(bodies, EAL.ranks(bodies)))), EAL.program(bodies, EAL.ranks(bodies)), 0)

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          all(Lf.defer.lift(Lf.of.expr(expr)))

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          do IO<Unit>:
            all(Lf.defer.lift(cert))
            sized(Sz.size(65536, True{}, E.of.term3(run)))

def loaded(+entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      compiled(Fr.compile(srcs, entry))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +entry <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, r)
    case _:
      IO.print("usage: bodyerrs MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
