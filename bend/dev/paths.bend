import Base
import ../Front.bend as Fr
import ../Resolve.bend as Rs
import ../Desugar.bend as D
import ../Lower.bend as Lw
import ../Term.bend as T
import ../Syntax.bend as S

def tshow(+fuel: Nat, t: T.T) -> String:
  match fuel:
    case 0n:
      "..."
    case 1n+f:
      match t:
        case T.TZero{a}:
          "0"
        case T.TPair{a, x, y}:
          "(" ++ tshow(f, x) ++ "," ++ tshow(f, y) ++ ")"
        case T.TVar{a, n}:
          n
        case T.TIdx{a, i}:
          "#" ++ Nat.show(i)
        case T.TApp{a, x, y}:
          "(" ++ tshow(f, x) ++ " " ++ tshow(f, y) ++ ")"
        case T.TLam{a, k, n, b}:
          match k:
            case T.Open{}:
              "(\\o" ++ n ++ ". " ++ tshow(f, b) ++ ")"
            case T.Closed{}:
              "(\\c" ++ n ++ ". " ++ tshow(f, b) ++ ")"
            case T.LetB{c}:
              "(\\let" ++ Nat.show(c) ++ " " ++ n ++ ". " ++ tshow(f, b) ++ ")"
        case T.TLeft{a, x}:
          "L" ++ tshow(f, x)
        case T.TRight{a, x}:
          "R" ++ tshow(f, x)
        case T.TRep{a}:
          "REP"
        case T.TRec{a, x, y, z}:
          "{" ++ tshow(f, x) ++ ", " ++ tshow(f, y) ++ ", " ++ tshow(f, z) ++ "}"
        case T.TIte{a, x, y, z}:
          "(if " ++ tshow(f, x) ++ " " ++ tshow(f, y) ++ " " ++ tshow(f, z) ++ ")"
        case T.TCheck{a, x, y}:
          "(check " ++ tshow(f, x) ++ " " ++ tshow(f, y) ++ ")"
        case T.TChurch{a, n}:
          "$" ++ U32.show(n)
        case _:
          "?"

def res(r: Result<&2, &2, Rs.ResErr, T.T>) -> String:
  match r:
    case Fail{e}:
      "ERR " ++ Rs.render(e)
    case Done{t}:
      tshow(U32.to_nat(100000), t)

def go(+t: S.Surf) -> IO(Unit):
  do IO<Unit>:
    IO.print("process: " ++ res(Lw.process(t)))
    IO.print("let:     " ++ res(Lw.process.let(t)))

def mained(r: Result<&2, &2, Rs.ResErr, S.Surf>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("main: " ++ Rs.render(e))
    case Done{t}:
      go(D.desugar(t))

def modsd(+entry: String, m: Fr.Mods) -> IO(Unit):
  match m:
    case Fr.Mods{mods, errs}:
      mained(Rs.main(mods, entry))

def loaded(+entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      modsd(entry, Fr.all(srcs))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +entry <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, r)
    case _:
      IO.print("usage: paths MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
