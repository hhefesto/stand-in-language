import Base
import ../Text.bend as Tx
import ../Expr.bend as E
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../IC.bend as IC
import ../Session.bend as Ss

# tplcount MODULE: how many templates the prepared program has.
def count(p: IC.Prog) -> String:
  match p:
    case IC.Prog{entry, bodies, words, maxk}:
      match words:
        case Con{t, rest}:
          "templates: " ++ U32.show(t)
        case Nil{}:
          "templates: none"

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          count(Ss.prepared(expr))

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          sized(Sz.size(65536, True{}, E.of.term3(run)))

def loaded(r: Result<&1, &1, String, List<&2, Fr.Src>>, +m: String) -> String:
  match r:
    case Fail{e}:
      e
    case Done{srcs}:
      compiled(Fr.compile(srcs, m))

def go(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +m <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(m)
        IO.print(loaded(r, m))
    case _:
      IO.print("usage: tplcount MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    go(xs)
