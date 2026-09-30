import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Term.bend as T
import ../Text.bend as Tx

# Sizing: every certificate golden's counts, and haskell-final's
# SizingTests (an unbounded input is reported as such, an exhausted budget
# as that, and the same program sizes under the full budget). One `ok NAME`
# line per group (FAIL NAME when it breaks). Run from the source root.

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

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
        case Sz.Sized{cs, expr}:
          counts(cs)

def size.terms(+max: U32, r: Result<&2, &2, String, Fr.Terms>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, +run}:
          sized(max, run, Sz.size(max, True{}, E.of.term3(run)))

# The counts, in token order, or the failure as the command reports it.
def size(+max: U32, srcs: List<&2, Fr.Src>, +entry: String) -> String:
  size.terms(max, Fr.compile(srcs, entry))

def with.prelude(+name: String, t: String, +prelude: String) -> List<&2, Fr.Src>:
  [Fr.Src{"Prelude", prelude}, Fr.Src{name, t}]

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

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("simpleplus.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    over : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/over-budget-recursion.tel")
    unb : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/unbounded-input-recursion.tel")
    report(text(prelude), text(ttt), text(plus), text(tc), text(over), text(unb))
