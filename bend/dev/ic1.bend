import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../IC.bend as IC
import ../Session.bend as Ss

def x.show(+fuel: Nat, x: E.X) -> String:
  match fuel:
    case 0n:
      "..."
    case 1n+f:
      match x:
        case E.XZero{}:
          "0"
        case E.XPair{a, b}:
          "(" ++ x.show(f, a) ++ "," ++ x.show(f, b) ++ ")"
        case E.XDefer{fi, b}:
          "<closure>"
        case E.XAborted{m}:
          "ABORTED " ++ x.show(f, m)
        case _:
          "?"

def out.got(+s: E.X, m: Maybe<&2, String>) -> String:
  match m:
    case Some{t}:
      "string: " ++ t
    case None{}:
      x.show(100n, s)

def out(+s: E.X) -> String:
  out.got(s, E.to.string(s))

def show.run(r: IC.Run) -> String:
  match r:
    case IC.Run{net, o, spent}:
      match o:
        case IC.RBOk{x}:
          match x:
            case E.XPair{d, st}:
              "display: " ++ out(d) ++ "\nstate: " ++ x.show(40n, st) ++ "\ninteractions: " ++ U32.show(spent)
            case other:
              "result: " ++ x.show(40n, other) ++ "\ninteractions: " ++ U32.show(spent)
        case IC.RBErr{e}:
          "error: " ++ e ++ "\ninteractions: " ++ U32.show(spent)

def go(+p: IC.Prog) -> IO(Unit):
  IO.print(show.run(IC.run(p, IC.net.new(p), E.XZero{}, IC.default.fuel())))

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{cs, expr}:
          go(Ss.prepared(expr))

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
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
      IO.print("usage: ic1 MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
