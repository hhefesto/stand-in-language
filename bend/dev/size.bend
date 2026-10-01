import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Term.bend as T
import ../Loc.bend as L

def counts(xs: List<&2, E.TS>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{t, rest}:
      match t:
        case E.TS{tok, n}:
          "#" ++ U32.show(tok) ++ "<=" ++ U32.show(n) ++ " " ++ counts(rest)

def size.of(+t: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("SIZING FAILED:\n" ++ Sz.render(f, t, 65536))
    case Done{s}:
      match s:
        case Sz.Sized{cs, expr}:
          IO.print("counts: " ++ counts(cs))

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, +run}:
          size.of(run, Sz.size(65536, True{}, E.of.term3(run)))

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
      IO.print("usage: size MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
