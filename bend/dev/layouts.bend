import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EAL.bend as EAL

# `layouts MODULE`: the certification's verdict and every capture layout
# EAL gives the sized term, one `hash shape` line each: a fingerprint to
# compare builds by.

def verdict(m: Maybe<&2, EAL.Err>) -> String:
  match m:
    case None{}:
      "certified"
    case Some{e}:
      EAL.render(e)

def lines(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Shape>>) -> IO(Unit):
  match kvs:
    case Nil{}:
      IO.print("end")
    case Con{kv, rest}:
      match kv:
        case (k, v):
          do IO<Unit>:
            IO.print(k ++ " " ++ Lf.shape.show(v, False{}))
            lines(rest)

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          lines(Map.to_list(&2, Lf.Shape, EAL.layouts(Lf.defer.lift(Lf.of.expr(expr)))))

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          do IO<Unit>:
            IO.print(verdict(EAL.certify(Lf.defer.lift(cert))))
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
      IO.print("usage: layouts MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
