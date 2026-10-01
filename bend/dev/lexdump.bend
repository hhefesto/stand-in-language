import Base
import ../Lex.bend as Lx
import ../Text.bend as T
import ../Loc.bend as L

def kind(k: Lx.TK) -> String:
  match k:
    case Lx.KId{name}:
      "id " ++ name
    case Lx.KKw{word}:
      "kw " ++ word
    case Lx.KNat{n}:
      "nat " ++ U32.show(n)
    case Lx.KChurch{n}:
      "church " ++ U32.show(n)
    case Lx.KStr{s}:
      "str " ++ s
    case Lx.KSym{c}:
      "sym " ++ U32.show(c)
    case Lx.KBad{c}:
      "bad " ++ U32.show(c)
    case Lx.KEnd{}:
      "end"

def pos(p: L.Pos) -> String:
  match p:
    case L.Pos{line, col, off}:
      U32.show(line) ++ ":" ++ U32.show(col) ++ "@" ++ U32.show(off)

def nlmark(b: Bool) -> String:
  match b:
    case True{}:
      " NL"
    case False{}:
      ""

def show(t: Lx.Tok) -> String:
  match t:
    case Lx.Tok{k, at, ws, nl}:
      pos(at) ++ " ws=" ++ pos(ws) ++ nlmark(nl) ++ " " ++ kind(k)

def dump(ts: List<&2, Lx.Tok>) -> IO(Unit):
  match ts:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{t, rest}:
      do IO<Unit>:
        IO.print(show(t))
        dump(rest)

def lexed(r: Result<&2, &2, Lx.LexErr, List<&2, Lx.Tok>>) -> IO(Unit):
  match r:
    case Fail{e}:
      match e:
        case Lx.LexErr{at, msg}:
          IO.print("lex error at " ++ pos(at) ++ ": " ++ msg)
    case Done{ts}:
      dump(ts)

def got(r: Result<&1, &1, String, String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("read error: " ++ e)
    case Done{s}:
      lexed(Lx.lex(s))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> file <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, String> <- T.read_file(file)
        got(r)
    case _:
      IO.print("usage: lexdump FILE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
