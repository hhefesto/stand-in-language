import Base
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
        case Sz.Sized{cs, expr, checks}:
          counts(cs)

def size.term(+max: U32, r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{+run}:
      sized(max, run, Sz.size(max, True{}, E.of.term3(run)))

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

def checks.text(c: Sz.Checks) -> String:
  match c:
    case Sz.Checks{v, b, r, o, p, e}:
      "validating " ++ keys(Set.to_list(v)) ++ "; boundary " ++ keys(Set.to_list(b)) ++ "; reaching " ++ keys(Set.to_list(r))
        ++ "; opening " ++ keys(Set.to_list(o)) ++ Bool.pick(String, p, "; proven", "")

def checked(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{cs, expr, checks}:
          checks.text(checks)

def checked.term(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{run}:
      checked(Sz.size(65536, True{}, E.of.term3(run)))

# What sizing proved of the checks, by number, with no guard.
def checks(srcs: List<&2, Fr.Src>, +entry: String) -> String:
  checked.term(Fr.compile(srcs, entry))

def guarded.program(r: Result<&2, &2, String, Fr.Program>) -> Result<&2, &2, Sz.SizeFail, Sz.Sized>:
  match r:
    case Fail{e}:
      Fail{Sz.Internal{e}}
    case Done{p}:
      match p:
        case Fr.Program{run, +g, +boundary}:
          Sz.size.guarded(65536, boundary, g, E.of.term3(run))

def guarded.sized(srcs: List<&2, Fr.Src>, +entry: String) -> Result<&2, &2, Sz.SizeFail, Sz.Sized>:
  guarded.program(Fr.compile.program(srcs, entry))

# What sizing proved of the checks, by number, as the command sizes main:
# its input refinements run by the session's guard.
def guarded.checks(srcs: List<&2, Fr.Src>, +entry: String) -> String:
  checked(guarded.sized(srcs, entry))

# Whether an Abort is left in the code that runs.
def has.abort(x: Co.V) -> Bool:
  match x:
    case Co.VAbort{}:
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
        case Sz.Sized{cs, expr, checks}:
          Bool.pick(String, has.abort(expr), "Abort", "none")

def aborts.term(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{run}:
      aborts.of(Sz.size(65536, True{}, E.of.term3(run)))

# Whether the sized program holds an Abort.
def aborts(srcs: List<&2, Fr.Src>, +entry: String) -> String:
  aborts.term(Fr.compile(srcs, entry))

# Whether main, sized as the command sizes it, holds an Abort.
def guarded.aborts(srcs: List<&2, Fr.Src>, +entry: String) -> String:
  aborts.of(guarded.sized(srcs, entry))

def case.of(+prelude: String, +scrutinee: String) -> List<&2, Fr.Src>:
  with.prelude("cased", "import Prelude\nmain = \\input -> (case " ++ scrutinee
    ++ " of\n  0 -> \"zero\"\n  1 -> \"one\", 0)\n", prelude)

# A case on a constant: Prelude's abort is its one check.
def cased(+prelude: String, +scrutinee: String) -> String:
  checks(case.of(prelude, scrutinee), "cased")

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

def report(+prelude: String, +ttt: String, +plus: String, +tc: String, +over: String, +unb: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("size-tc_ultra_minimal", String.eq(
      size(65536, [Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal"), "1")))
    IO.print(verdict("size-simpleplus", String.eq(
      size(65536, with.prelude("simpleplus", plus, prelude), "simpleplus"), "11 7 10 10")))
    IO.print(verdict("size-tictactoe", String.eq(
      size(65536, with.prelude("tictactoe", ttt, prelude), "tictactoe"),
      "79 32 10 127 9 10 9 4 4 4 78 78 2 2")))
    IO.print(verdict("size-over-budget", String.eq(
      size(65536, with.prelude("over-budget-recursion", over, prelude), "over-budget-recursion"), "34")))
    IO.print(verdict("size-budget-exhausted", String.eq(
      size(5, with.prelude("over-budget-recursion", over, prelude), "over-budget-recursion"),
      "could not size recursion #0 at over-budget-recursion:30:34:\n  its test had still not stopped after 6 unrollings.\n  Either it needs a deeper recursion than the sizing budget allows, or\n  its test never stops.")))
    IO.print(verdict("size-unbounded-input", String.eq(
      size(65536, with.prelude("unbounded-input-recursion", unb, prelude), "unbounded-input-recursion"),
      "could not size recursion #0 at unbounded-input-recursion:27:34:\n  its test depends on input that nothing bounds, so no finite iteration\n  count can be proven for it. Constrain that input with a refinement\n  (`x : someValidator`) or an `assert` before recursing on it.")))
    IO.print(verdict("size-checks", all([
      String.eq(checks(with.prelude("simpleplus", plus, prelude), "simpleplus"), "validating 0; boundary ; reaching ; opening "),
      String.eq(checks(with.prelude("tictactoe", ttt, prelude), "tictactoe"), "validating 0,1,2; boundary ; reaching ; opening "),
      String.eq(cased(prelude, "0"), "validating ; boundary ; reaching ; opening ; proven"),
      String.eq(cased(prelude, "3"), "validating ; boundary ; reaching 0; opening ; proven")])))
    IO.print(verdict("size-boundary", all([
      String.eq(guarded.checks(with.prelude("simpleplus", plus, prelude), "simpleplus"),
        "validating 0; boundary 0; reaching ; opening ; proven"),
      String.eq(guarded.checks(with.prelude("tictactoe", ttt, prelude), "tictactoe"),
        "validating 0,1,2; boundary 0,1,2; reaching ; opening ; proven")])))
    IO.print(verdict("size-filter", all([
      String.eq(filtered("R", True{}, "L"), "both"),
      String.eq(filtered("L", True{}, "L"), "a"),
      String.eq(filtered("LL", True{}, "L"), "a"),
      String.eq(filtered("L", True{}, "LL"), "both"),
      String.eq(filtered("L", False{}, "L"), "b"),
      String.eq(filtered("L", False{}, "LL"), "b"),
      String.eq(filtered("R", False{}, "L"), "both")])))
    # tictactoe keeps its aborts: the erasure checker spends its budget on
    # it and gives up (SIZING-PROOF.md §5, D3).
    IO.print(verdict("size-erased", all([
      String.eq(aborts(case.of(prelude, "0"), "cased"), "none"),
      String.eq(aborts([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal"), "none"),
      String.eq(aborts(case.of(prelude, "3"), "cased"), "Abort"),
      String.eq(aborts(with.prelude("simpleplus", plus, prelude), "simpleplus"), "Abort"),
      String.eq(guarded.aborts(with.prelude("simpleplus", plus, prelude), "simpleplus"), "none"),
      String.eq(guarded.aborts(with.prelude("tictactoe", ttt, prelude), "tictactoe"), "Abort")])))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("test/programs/simpleplus.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    over : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/over-budget-recursion.tel")
    unb : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/unbounded-input-recursion.tel")
    report(text(prelude), text(ttt), text(plus), text(tc), text(over), text(unb))
