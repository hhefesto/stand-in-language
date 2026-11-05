import Base
import ../Loc.bend as L
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Term.bend as T
import ../Core.bend as Co
import ../Text.bend as Tx

# Sizing: every certificate golden's counts, haskell-final's SizingTests
# (an unbounded input is reported as such, an exhausted budget as that, and
# the same program sizes under the full budget), and what sizing proves of
# refinement checks. One `ok NAME` line per group (FAIL NAME when it
# breaks). Run from the source root.

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

def all(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      b && all(rest)

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def counts(xs: List<&2, E.TS>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{t, rest}:
      match t:
        case E.TS{tok, n}:
          match rest:
            case Nil{}:
              U32.show(n)
            case Con{r, more}:
              U32.show(n) ++ " " ++ counts(Con{r, more})

def sized(+max: U32, +t: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      Sz.render(f, t, max)
    case Done{s}:
      match s:
        case Sz.Sized{cs, expr, checks, pl, pro}:
          counts(cs)

def size.term(+max: U32, r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{+run}:
      sized(max, run, Sz.size.checked(max, True{}, run, Sz.WantCounts{}))

# The counts, in token order, or the failure as the command reports it.
def size(+max: U32, srcs: List<&2, Fr.Src>, +entry: String) -> String:
  size.term(max, Fr.compile(srcs, entry))

def with.prelude(+name: String, t: String, +prelude: String) -> List<&2, Fr.Src>:
  [Fr.Src{"Prelude", prelude}, Fr.Src{name, t}]

# Checks
# ------

def keys(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      match rest:
        case Nil{}:
          x
        case Con{y, more}:
          x ++ "," ++ keys(Con{y, more})

# The kinds of the aborts in a program (remainingChecks).
def kinds.add(x: Co.V, acc: Set()) -> Set():
  match x:
    case Co.VAbort{o, m}:
      kinds.add(m, Set.add(acc, L.kind.show(L.Origin.kind(o))))
    case Co.VPair{a, b}:
      kinds.add(b, kinds.add(a, acc))
    case Co.VDefer{fi, b}:
      kinds.add(b, acc)
    case Co.VSetEnv{a}:
      kinds.add(a, acc)
    case Co.VLeft{a}:
      kinds.add(a, acc)
    case Co.VRight{a}:
      kinds.add(a, acc)
    case _:
      acc

def kinds(x: Co.V) -> String:
  keys(Set.to_list(kinds.add(x, Set.new())))

def kinds.of(g: Maybe<&2, Co.V>) -> String:
  match g:
    case Some{x}:
      kinds(x)
    case None{}:
      ""

def placed.of(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{cs, expr, checks, pl, g}:
          kinds(pl) ++ "/" ++ kinds.of(g)

def placed.term(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{+run}:
      placed.of(Sz.size.checked(65536, True{}, run, Sz.WantPlain{}))

# The kinds of the checks master's main still makes, and those its input
# prologue makes.
def placed(srcs: List<&2, Fr.Src>, +entry: String) -> String:
  placed.term(Fr.compile(srcs, entry))

# Whether an Abort is left in the code that runs.
def has.abort(x: Co.V) -> Bool:
  match x:
    case Co.VAbort{o, m}:
      True{}
    case Co.VPair{a, b}:
      has.abort(a) || has.abort(b)
    case Co.VDefer{fi, b}:
      has.abort(b)
    case Co.VSetEnv{a}:
      has.abort(a)
    case Co.VLeft{a}:
      has.abort(a)
    case Co.VRight{a}:
      has.abort(a)
    case _:
      False{}

def aborts.of(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{cs, expr, checks, pl, g}:
          Bool.pick(String, has.abort(expr), "Abort", "none")

def aborts.term(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{run}:
      aborts.of(Sz.size(65536, True{}, run))

# Whether the sized program holds an Abort.
def aborts(srcs: List<&2, Fr.Src>, +entry: String) -> String:
  aborts.term(Fr.compile(srcs, entry))

def case.of(+prelude: String, +scrutinee: String) -> List<&2, Fr.Src>:
  with.prelude("cased", "import Prelude\nmain = \\input -> (case " ++ scrutinee
    ++ " of\n  0 -> \"zero\"\n  1 -> \"one\", 0)\n", prelude)

# Which alternatives filter.at keeps of a superposition at q (left 0, right
# a pair), in the branch a choice at n took: haskell-final's filterLeft and
# filterRight.
def kept(x: E.X) -> String:
  match x:
    case E.XZero{}:
      "a"
    case E.XPair{l, r}:
      "b"
    case E.XEither{k, l, r}:
      "both"
    case _:
      "other"

def filtered(+q: String, left: Bool, +n: String) -> String:
  kept(Sz.filter.at(Some{q}, left, n, E.XZero{}, E.XPair{E.XZero{}, E.XZero{}}))

def report(+prelude: String, +ttt: String, +plus: String, +tc: String, +over: String, +unb: String, +cor: String, +anti: String, +ninp: String, +misl: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("size-tc_ultra_minimal", String.eq(
      size(65536, [Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal"), "1")))
    IO.print(verdict("size-simpleplus", String.eq(
      size(65536, with.prelude("simpleplus", plus, prelude), "simpleplus"), "11 7 10 10")))
    IO.print(verdict("size-tictactoe", String.eq(
      size(65536, with.prelude("tictactoe", ttt, prelude), "tictactoe"),
      "79 32 10 127 9 10 10 9 4 4 4 78 78 3 2 2")))
    IO.print(verdict("size-over-budget", String.eq(
      size(65536, with.prelude("over-budget-recursion", over, prelude), "over-budget-recursion"), "34")))
    IO.print(verdict("size-budget-exhausted", String.eq(
      size(5, with.prelude("over-budget-recursion", over, prelude), "over-budget-recursion"),
      "could not size recursion #0 at over-budget-recursion:30:34:\n  its test had still not stopped after 6 unrollings.\n  Either it needs a deeper recursion than the sizing budget allows, or\n  its test never stops.")))
    IO.print(verdict("size-unbounded-input", String.eq(
      size(65536, with.prelude("unbounded-input-recursion", unb, prelude), "unbounded-input-recursion"),
      "could not size recursion #0 at unbounded-input-recursion:27:34:\n  its test depends on input that nothing bounds, so no finite iteration\n  count can be proven for it. Constrain that input with a refinement\n  (`x : somePredicate`) before recursing on it.")))
    IO.print(verdict("size-mislabeled", String.eq(
      size(65536, with.prelude("mislabeled-size", misl, prelude), "mislabeled-size"), "9")))
    IO.print(verdict("size-where-checks-go", all([
      String.eq(placed(with.prelude("simpleplus", plus, prelude), "simpleplus"), "/RefinementAbort"),
      String.eq(placed(with.prelude("correlated-check", cor, prelude), "correlated-check"), "/"),
      String.eq(placed(with.prelude("anticorrelated-check", anti, prelude), "anticorrelated-check"), "RefinementAbort/"),
      String.eq(placed(with.prelude("notinput", ninp, prelude), "notinput"), "/RefinementAbort")])))
    IO.print(verdict("size-filter", all([
      String.eq(filtered("R", True{}, "L"), "both"),
      String.eq(filtered("L", True{}, "L"), "a"),
      String.eq(filtered("LL", True{}, "L"), "a"),
      String.eq(filtered("L", True{}, "LL"), "both"),
      String.eq(filtered("L", False{}, "L"), "b"),
      String.eq(filtered("L", False{}, "LL"), "b"),
      String.eq(filtered("R", False{}, "L"), "both")])))
    # The net's program, where the erasure checker proves it: a case on a
    # constant that matches holds no abort, one that does not keeps it, and
    # simpleplus's only check runs before main.
    IO.print(verdict("size-erased", all([
      String.eq(aborts(case.of(prelude, "0"), "cased"), "none"),
      String.eq(aborts([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal"), "none"),
      String.eq(aborts(case.of(prelude, "3"), "cased"), "Abort"),
      String.eq(aborts(with.prelude("simpleplus", plus, prelude), "simpleplus"), "none")])))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("test/programs/simpleplus.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    over : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/over-budget-recursion.tel")
    unb : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/unbounded-input-recursion.tel")
    cor : Result<&1, &1, String, String> <- Tx.read_file("test/programs/correlated-check.tel")
    anti : Result<&1, &1, String, String> <- Tx.read_file("test/programs/anticorrelated-check.tel")
    ninp : Result<&1, &1, String, String> <- Tx.read_file("test/programs/notinput.tel")
    misl : Result<&1, &1, String, String> <- Tx.read_file("test/programs/mislabeled-size.tel")
    report(text(prelude), text(ttt), text(plus), text(tc), text(over), text(unb), text(cor), text(anti), text(ninp), text(misl))
