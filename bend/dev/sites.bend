import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Loc.bend as L

type Site is Data:
  Site{+tok: U32, +loc: String}

type N is Data:
  N1{t: T.C}

def loc.text(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      s
    case None{}:
      "?"

def walk(+fuel: Nat, t: T.C, acc: List<&2, Site>) -> List<&2, Site>:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match t:
        case T.CUnsized{loc, tok}:
          Site{tok, loc.text(L.render_compact(loc))} <> acc
        case T.CPair{a, x, y}:
          walk(f, y, walk(f, x, acc))
        case T.CSetEnv{a, x}:
          walk(f, x, acc)
        case T.CDefer{a, fi, x}:
          walk(f, x, acc)
        case T.CLeft{a, x}:
          walk(f, x, acc)
        case T.CRight{a, x}:
          walk(f, x, acc)
        case T.CCheck{a, c, x, y}:
          walk(f, y, walk(f, x, acc))
        case _:
          acc

def count(+fuel: Nat, t: T.C) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      match t:
        case T.CPair{a, x, y}:
          1n+Nat.add(count(f, x), count(f, y))
        case T.CSetEnv{a, x}:
          1n+count(f, x)
        case T.CDefer{a, fi, x}:
          1n+count(f, x)
        case T.CLeft{a, x}:
          1n+count(f, x)
        case T.CRight{a, x}:
          1n+count(f, x)
        case T.CCheck{a, c, x, y}:
          1n+Nat.add(count(f, x), count(f, y))
        case _:
          1n

def ins.pick(le: Bool, +s: Site, x: Site, rest: List<&2, Site>, later: List<&2, Site>) -> List<&2, Site>:
  match le:
    case True{}:
      s <> x <> rest
    case False{}:
      x <> later

def tok.of(s: Site) -> U32:
  match s:
    case Site{tok, loc}:
      tok

def ins(xs: List<&2, Site>, +s: Site) -> List<&2, Site>:
  match xs:
    case Nil{}:
      [s]
    case Con{+x, +rest}:
      ins.pick(U32.is_le(tok.of(s), tok.of(x)), s, x, rest, ins(rest, s))

def sort(xs: List<&2, Site>, acc: List<&2, Site>) -> List<&2, Site>:
  match xs:
    case Nil{}:
      acc
    case Con{x, rest}:
      sort(rest, ins(acc, x))

def show(xs: List<&2, Site>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{s, rest}:
      match s:
        case Site{tok, loc}:
          do IO<Unit>:
            IO.print("  " ++ loc ++ " (#" ++ U32.show(tok) ++ ")")
            show(rest)

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, +run}:
          do IO<Unit>:
            IO.print("cert nodes: " ++ Nat.show(count(U32.to_nat(4000000000), cert)))
            IO.print("run nodes: " ++ Nat.show(count(U32.to_nat(4000000000), run)))
            show(sort(walk(U32.to_nat(4000000000), run, []), []))

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
      IO.print("usage: sites MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
