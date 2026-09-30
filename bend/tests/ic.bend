import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../IC.bend as IC
import ../Session.bend as Ss
import ../Text.bend as Tx

# The IC runtime: haskell-final's ICTests on closed terms (application,
# projection, duplication, gates, abort, church numerals, fuel, branch
# laziness), and whole sessions' interaction counts, guided by EAL as the
# command runs them, against the .ic-meter goldens. One `ok NAME` line per group (FAIL NAME when it
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

def report(+prelude: String, +tc: String, +plus: String, +ttt: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("ic-application", all([
      gives(se(p(d(100, env()), z())), z()),
      gives(se(p(d(107, z()), p(z(), z()))), z()),
      gives(E.app(p(d(106, left(env())), z()), p(z(), z())), p(z(), z())),
      gives(se(p(d(108, p(d(109, left(env())), env())), z())), p(d(109, left(env())), z()))])))
    IO.print(verdict("ic-projection", all([
      gives(left(p(p(z(), z()), z())), p(z(), z())),
      gives(E.XRight{p(p(z(), z()), z())}, z()),
      gives(left(z()), z()),
      gives(left(se(p(d(112, env()), p(z(), p(z(), z()))))), z())])))
    IO.print(verdict("ic-duplication", all([
      gives(se(p(d(101, p(env(), env())), p(z(), z()))), p(p(z(), z()), p(z(), z()))),
      gives(se(p(d(102, p(env(), env())), d(103, env()))), p(d(103, env()), d(103, env()))),
      gives(se(p(d(110, p(se(p(env(), z())), se(p(env(), p(z(), z()))))), d(111, env()))),
        p(z(), p(z(), z())))])))
    IO.print(verdict("ic-gates", all([
      gives(E.gate.switch(p(z(), z()), z(), z()), p(z(), z())),
      gives(E.gate.switch(p(z(), z()), z(), p(z(), z())), z()),
      gives(E.gate.switch(d(105, env()), z(), p(z(), z())), z()),
      gives(E.gate.switch(z(), p(z(), z()), se(p(d(113, env()), p(z(), z())))), p(z(), z()))])))
    IO.print(verdict("ic-abort", all([
      gives(se(p(E.XAbort{}, z())), d(E.abort.ind(), env())),
      gives(se(p(se(p(E.XAbort{}, z())), p(z(), z()))), p(z(), z())),
      aborts(se(p(E.XAbort{}, p(z(), z()))), p(z(), z())),
      aborts(left(se(p(E.XAbort{}, p(z(), z())))), p(z(), z())),
      gives(E.gate.switch(z(), left(se(p(E.XAbort{}, p(z(), z())))), z()), z())])))
    IO.print(verdict("ic-church", all([
      gives(E.app(E.app(church.two(), succ.c()), z()), num(2n)),
      gives(E.app(E.app(church.two(), E.app(church.two(), succ.c())), z()), num(4n)),
      gives(E.app(E.app(church.two(), E.app(church.two(), E.app(church.two(), succ.c()))), z()), num(8n))])))
    IO.print(verdict("ic-fuel", runs.dry(E.app(E.app(church.two(), succ.c()), z()), 3)))
    IO.print(verdict("ic-laziness", all([
      gives(se(p(d(200, E.ite(p(z(), z()), left(env()), omega.applied())), p(z(), z()))), z()),
      runs.dry(se(p(d(201, se(p(se(p(E.XGate{}, p(z(), z()))), p(omega.applied(), left(env()))))), p(z(), z()))), 50000),
      gives(se(p(d(202, se(p(se(p(E.XGate{}, p(z(), z()))), p(se(p(p(z(), z()), z())), left(env()))))), p(z(), z()))), z())])))
    IO.print(verdict("ic-omega", runs.dry(omega.applied(), 100000)))
    IO.print(verdict("ic-meter-tc_ultra_minimal", U32.is_eq(
      spent(session([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal", [])),
      524)))
    IO.print(verdict("ic-meter-simpleplus", U32.is_eq(
      spent(session([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus", ["3 4"])),
      1517868)))
    IO.print(verdict("ic-meter-tictactoe", U32.is_eq(
      spent(session([Fr.Src{"Prelude", prelude}, Fr.Src{"tictactoe", ttt}], "tictactoe", ["1", "4", "2", "5", "3"])),
      15168230)))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("simpleplus.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    report(text(prelude), text(tc), text(plus), text(ttt))
