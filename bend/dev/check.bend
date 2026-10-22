import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Sem.bend as Sm
import ../Check.bend as Ck

# `check MODULE [STEPS]`: the erasure checker (Check.bend) on MODULE's
# main, guarded as the command guards it: its verdict, what it watched, and
# the evaluation steps it took (at most STEPS, by default the compiler's
# budget, Size.bend's check.work).

def verdict(v: Ck.Verdict) -> String:
  match v:
    case Ck.Proven{}:
      "proven: no input fires an erased site"
    case Ck.Fires{+i, at}:
      "fires " ++ Ck.at.name(at) ++ " on input " ++ Ck.show(i)
    case Ck.Unknown{why}:
      "unknown: " ++ why

def ints(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      " " ++ U32.show(x) ++ ints(rest)

def seen(+runs: Nat, s: Ck.Seen) -> String:
  match s:
    case Ck.Seen{v, left}:
      verdict(v) ++ "\nsteps: " ++ Nat.show(Nat.sub(runs, left))

def guard.sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Maybe<&2, E.X>:
  match r:
    case Fail{f}:
      None{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks}:
          Some{Sm.of.core(expr)}

def guard.of(m: Maybe<&2, T.C>) -> Maybe<&2, E.X>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      guard.sized(Sz.size(65536, True{}, E.of.term3(t)))

def watched(+runs: Nat, +x: E.X, +counts: List<&2, E.TS>, g: Maybe<&2, E.X>, +erasable: List<&2, U32>) -> String:
  "erasable checks:" ++ ints(erasable) ++ "\n"
    ++ seen(runs, Ck.check(U32.to_nat(100000), Sm.fuel(), Sm.Pol{Sm.Watch{}, erasable}, Ck.witness(counts, x), g, runs))

def proven(+runs: Nat, +x: E.X, +counts: List<&2, E.TS>, g: Maybe<&2, E.X>, cs: Sz.Checks) -> String:
  match cs:
    case Sz.Checks{v, +boundary, +reaching, +opening, proven, e}:
      match proven:
        case False{}:
          "sizing did not prove main for every input: nothing is erased"
        case True{}:
          watched(runs, x, counts, g, Ck.erasable(x, Sz.minus(Set.to_list(reaching), boundary, opening)))

def sized(+runs: Nat, +x: E.X, g: Maybe<&2, E.X>, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{+counts, expr, checks}:
          proven(runs, x, counts, g, checks)

def program(+runs: Nat, r: Result<&2, &2, String, Fr.Program>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{p}:
      match p:
        case Fr.Program{run, +g, +boundary}:
          +x = E.of.term3(run)
          sized(runs, x, guard.of(g), Sz.size.guarded(65536, boundary, g, x))

def run(+runs: Nat, +entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(e)
    case Done{srcs}:
      IO.print(program(runs, Fr.compile.program(srcs, entry)))

def runs.of(m: Maybe<&2, U32>) -> Nat:
  match m:
    case Some{n}:
      U32.to_nat(n)
    case None{}:
      Sz.check.work()

def run.args(a: List<String>) -> IO(Unit):
  match a:
    case self <> +m <> n <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(m)
        run(runs.of(U32.read(n)), m, r)
    case self <> +m <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(m)
        run(Sz.check.work(), m, r)
    case _:
      IO.print("usage: check MODULE [STEPS]")

def main() -> IO(Unit):
  do IO<Unit>:
    a : List<String> <- IO.args()
    run.args(a)
