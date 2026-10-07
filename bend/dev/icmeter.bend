import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Session.bend as Ss
import ../Core.bend as Co

# `icmeter MODULE [LINE...]`: the session on those lines, as the command
# runs it (main's input refinements by the guard first, both guided); its
# displays and the interactions spent, to set against haskell-final's
# `--ic --meter`.

def shown(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, rest}:
      do IO<Unit>:
        u : Unit <- shown(rest)
        IO.print(x)

def report(r: Ss.Replay) -> IO(Unit):
  match r:
    case Ss.Replay{xs, c}:
      do IO<Unit>:
        u : Unit <- shown(xs)
        IO.print("IC interactions: " ++ U32.show(Ss.cost.spent(c)))

def sized.expr(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Maybe<&2, Co.V>:
  match r:
    case Fail{f}:
      None{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks}:
          Some{expr}

def guard.expr(m: Maybe<&2, T.C>) -> Maybe<&2, Co.V>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      sized.expr(Sz.size(65536, True{}, E.of.term3(t)))

def sized(g: Maybe<&2, Co.V>, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, lines: List<&2, String>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, +expr, checks}:
          report(Ss.replay(Ss.session(expr, g), Ss.Sized{}, lines))

def compiled(r: Result<&2, &2, String, Fr.Program>, lines: List<&2, String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{p}:
      match p:
        case Fr.Program{run, g, +boundary}:
          sized(guard.expr(g), Sz.size.at(65536, True{}, boundary, E.of.term3(run)), lines)

def loaded(+entry: String, lines: List<&2, String>, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      compiled(Fr.compile.program(srcs, entry), lines)

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
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, lines.of(rest), r)
    case _:
      IO.print("usage: icmeter MODULE [LINE...]")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
