import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../Term.bend as T

def keys(xs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (k, b):
          match b:
            case Lf.Body{fi, body}:
              k ++ " " ++ U32.show(fi) ++ "\n" ++ keys(rest)

def dump(l: Lf.Lifted) -> String:
  match l:
    case Lf.Lifted{bodies, main}:
      keys(Map.to_list(&2, Lf.Body, bodies)) ++ "main " ++ Lf.show(main)

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          dump(Lf.defer.lift(Lf.of.expr(expr)))

def defers(t: T.C) -> U32:
  match t:
    case T.CPair{loc, a, b}:
      (defers(a) + defers(b) : U32)
    case T.CSetEnv{loc, x}:
      defers(x)
    case T.CDefer{loc, fi, x}:
      (1 + defers(x) : U32)
    case T.CLeft{loc, x}:
      defers(x)
    case T.CRight{loc, x}:
      defers(x)
    case T.CCheck{loc, cloc, tc, c}:
      (defers(tc) + defers(c) : U32)
    case _:
      0

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          do IO<Unit>:
            IO.print("defers " ++ U32.show(defers(cert)))
            IO.print("cert\n" ++ dump(Lf.defer.lift(cert)))

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
      IO.print("usage: lift MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
