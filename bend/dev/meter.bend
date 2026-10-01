import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../IC.bend as IC
import ../Session.bend as Ss
import ../Text.bend as Tx

# The IC runtime: haskell-final's ICTests on closed terms (application,
# projection, duplication, gates, abort, church numerals, fuel, branch
# laziness), and whole sessions' interaction counts against the
# .ic-meter goldens. One `ok NAME` line per group (FAIL NAME when it
# breaks). Run from the source root.

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

# Term construction (ICTests' helpers)
# ------------------------------------

def z() -> E.X:
  E.XZero{}

def p(a: E.X, b: E.X) -> E.X:
  E.XPair{a, b}

def se(x: E.X) -> E.X:
  E.XSetEnv{x}

def d(+n: U32, x: E.X) -> E.X:
  E.XDefer{n, x}

def env() -> E.X:
  E.XEnv{}

def left(x: E.X) -> E.X:
  E.XLeft{x}

# \f x -> f (f x), a closed closure: the church numeral two.
def church.two() -> E.X:
  p(d(20, p(d(21, E.app(E.var(1n), E.app(E.var(1n), E.var(0n)))), env())), z())

# \x -> (0, x)
def succ.c() -> E.X:
  p(d(22, p(z(), E.var(0n))), z())

def num(n: Nat) -> E.X:
  match n:
    case 0n:
      z()
    case 1n+k:
      p(z(), num(k))

# Unapplied, a value; applied to itself, it never stops.
def omega() -> E.X:
  d(1, se(p(left(env()), env())))

def omega.applied() -> E.X:
  se(p(omega(), p(omega(), z())))

# Outcomes
# --------

# What icEval gives: the value, the abort it carries, or the runtime error.
def result.of(m: Maybe<&2, E.X>, +x: E.X) -> String:
  match m:
    case Some{msg}:
      "abort " ++ E.show(msg)
    case None{}:
      E.show(x)

def result(r: IC.Run) -> String:
  match r:
    case IC.Run{net, out, spent}:
      match out:
        case IC.RBOk{+x}:
          result.of(Ss.aborted(x), x)
        case IC.RBErr{e}:
          "error " ++ e

def eval(t: E.X, +fuel: U32) -> String:
  +prog = IC.prepare.closed(t)
  result(IC.run(prog, IC.net.new(prog), z(), fuel))

def gives(t: E.X, v: E.X) -> Bool:
  String.eq(eval(t, IC.default.fuel()), E.show(v))

def aborts(t: E.X, m: E.X) -> Bool:
  String.eq(eval(t, IC.default.fuel()), "abort " ++ E.show(m))

def runs.dry(t: E.X, +fuel: U32) -> Bool:
  String.starts_with(eval(t, fuel), "error ICFuelExhausted")

def all(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      b && all(rest)

# Sessions
# --------

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{f}:
      Ss.Replay{["sizing failed"], 0}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          Ss.replay(Ss.prepared(expr), lines)

def compiled(r: Result<&2, &2, String, Fr.Terms>, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{e}:
      Ss.Replay{[e], 0}
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          sized(Sz.size(65536, True{}, E.of.term3(run)), lines)

def session(srcs: List<&2, Fr.Src>, +entry: String, lines: List<&2, String>) -> Ss.Replay:
  compiled(Fr.compile(srcs, entry), lines)

def spent(r: Ss.Replay) -> U32:
  match r:
    case Ss.Replay{shown, n}:
      n

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def meter(+prelude: String, +plus: String, +tc: String) -> IO(Unit):
  do IO<Unit>:
    IO.print("tc " ++ U32.show(spent(session([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal", []))))
    IO.print("plus " ++ U32.show(spent(session([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus", ["3 4"]))))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("simpleplus.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    meter(text(prelude), text(plus), text(tc))
