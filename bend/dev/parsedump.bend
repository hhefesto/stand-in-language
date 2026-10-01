import Base
import ../Parse.bend as P
import ../Syntax.bend as S
import ../Text.bend as T
import ../Loc.bend as L

def lc(l: L.Loc) -> String:
  match l:
    case L.Src{file, start, stop}:
      match start:
        case L.Pos{line, col, off}:
          "@" ++ U32.show(line) ++ ":" ++ U32.show(col)
    case _:
      "@?"

type N is Data:
  NS{t: S.Surf}
  NP{p: S.Pat}
  ND{d: S.Def}
  NSs{xs: List<&2, S.Surf>}
  NDs{xs: List<&2, S.Def>}
  NLPs{xs: List<&2, S.LPat>}
  NAs{xs: List<&2, S.Alt>}

def pr(+fuel: Nat, n: N) -> String:
  match fuel:
    case 0n:
      "..."
    case 1n+f:
      match n:
        case NS{t}:
          match t:
            case S.SVar{loc, name}:
              name
            case S.SApp{loc, a, b}:
              "(" ++ pr(f, NS{a}) ++ " " ++ pr(f, NS{b}) ++ ")" ++ lc(loc)
            case S.SLam{loc, v, body}:
              "(\\" ++ L.Name.text(v) ++ " " ++ pr(f, NS{body}) ++ ")"
            case S.SLamPat{loc, pats, body}:
              "(\\[" ++ pr(f, NLPs{pats}) ++ "] " ++ pr(f, NS{body}) ++ ")" ++ lc(loc)
            case S.SZero{loc}:
              "0"
            case S.SPair{loc, a, b}:
              "(" ++ pr(f, NS{a}) ++ ", " ++ pr(f, NS{b}) ++ ")"
            case S.SCheck{loc, a, b}:
              "(check " ++ pr(f, NS{a}) ++ " " ++ pr(f, NS{b}) ++ ")" ++ lc(loc)
            case S.SIte{loc, i, a, e}:
              "(if " ++ pr(f, NS{i}) ++ " " ++ pr(f, NS{a}) ++ " " ++ pr(f, NS{e}) ++ ")"
            case S.SLeft{loc, x}:
              "(left " ++ pr(f, NS{x}) ++ ")"
            case S.SRight{loc, x}:
              "(right " ++ pr(f, NS{x}) ++ ")"
            case S.STrace{loc, x}:
              "(trace " ++ pr(f, NS{x}) ++ ")"
            case S.SHash{loc, x}:
              "(# " ++ pr(f, NS{x}) ++ ")"
            case S.SChurch{loc, k}:
              "$" ++ U32.show(k)
            case S.SRec{loc, a, r, b}:
              "{" ++ pr(f, NS{a}) ++ ", " ++ pr(f, NS{r}) ++ ", " ++ pr(f, NS{b}) ++ "}" ++ lc(loc)
            case S.SLet{loc, binds, body}:
              "(let ... " ++ pr(f, NS{body}) ++ ")"
            case S.SLetSugar{loc, defs, body}:
              "(let [" ++ pr(f, NDs{defs}) ++ "] " ++ pr(f, NS{body}) ++ ")" ++ lc(loc)
            case S.SList{loc, xs}:
              "[" ++ pr(f, NSs{xs}) ++ "]"
            case S.SInt{loc, k}:
              U32.show(k)
            case S.SStr{loc, s}:
              "\"" ++ s ++ "\""
            case S.SCase{loc, scrut, alts}:
              "(case " ++ pr(f, NS{scrut}) ++ " " ++ pr(f, NAs{alts}) ++ ")"
        case NP{p}:
          match p:
            case S.PVar{name}:
              L.Name.text(name)
            case S.PAnn{q, t}:
              "(" ++ pr(f, NP{q}) ++ " : " ++ pr(f, NS{t}) ++ ")"
            case S.PInt{k}:
              U32.show(k)
            case S.PStr{s}:
              "\"" ++ s ++ "\""
            case S.PIgnore{}:
              "_"
            case S.PPair{a, b}:
              "(" ++ pr(f, NP{a}) ++ ", " ++ pr(f, NP{b}) ++ ")"
        case ND{d}:
          match d:
            case S.DSingle{name, body}:
              L.Name.text(name) ++ " = " ++ pr(f, NS{body})
            case S.DChecked{name, cloc, check, body}:
              L.Name.text(name) ++ " :" ++ lc(cloc) ++ " " ++ pr(f, NS{check}) ++ " = " ++ pr(f, NS{body})
            case S.DList{loc, names, body}:
              "[list] = " ++ pr(f, NS{body})
        case NSs{xs}:
          match xs:
            case Nil{}:
              ""
            case Con{h, t}:
              pr(f, NS{h}) ++ "; " ++ pr(f, NSs{t})
        case NDs{xs}:
          match xs:
            case Nil{}:
              ""
            case Con{h, t}:
              pr(f, ND{h}) ++ "; " ++ pr(f, NDs{t})
        case NLPs{xs}:
          match xs:
            case Nil{}:
              ""
            case Con{h, t}:
              match h:
                case S.LPat{loc, p}:
                  pr(f, NP{p}) ++ lc(loc) ++ " " ++ pr(f, NLPs{t})
        case NAs{xs}:
          match xs:
            case Nil{}:
              ""
            case Con{h, t}:
              match h:
                case S.Alt{p, body}:
                  pr(f, NP{p}) ++ " -> " ++ pr(f, NS{body}) ++ "; " ++ pr(f, NAs{t})

def items(xs: List<&2, S.Item>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      match h:
        case S.IImport{imp}:
          do IO<Unit>:
            IO.print("import")
            items(t)
        case S.IDef{d}:
          do IO<Unit>:
            IO.print(pr(U32.to_nat(100000), ND{d}))
            items(t)

def parsed(+text: String, r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(P.render("M", text, e))
    case Done{xs}:
      items(xs)

def got(r: Result<&1, &1, String, String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("read error: " ++ e)
    case Done{+s}:
      parsed(s, P.module("M", s))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> file <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, String> <- T.read_file(file)
        got(r)
    case _:
      IO.print("usage: parsedump FILE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
