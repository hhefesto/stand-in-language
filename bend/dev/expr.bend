import Base
import ../Parse.bend as P
import ../Syntax.bend as S
import ../Text.bend as T

def parsed(+text: String, r: Result<&2, &2, P.PErr, S.Surf>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("FAIL\n" ++ P.render("E", text, e))
    case Done{t}:
      IO.print("OK")

def got(r: Result<&1, &1, String, String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("read error: " ++ e)
    case Done{+s}:
      parsed(s, P.expression("E", s))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> file <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, String> <- T.read_file(file)
        got(r)
    case _:
      IO.print("usage: expr FILE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
