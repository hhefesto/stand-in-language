import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Core.bend as Co
import ../Lift.bend as Lf
import ../IC.bend as IC
import ../Session.bend as Ss
import ../Text.bend as Tx

# The IC runtime: haskell-final's ICTests on closed terms (application,
# projection, duplication, gates, abort, church numerals, fuel, branch
# laziness); whole sessions' interaction counts, guided by EAL as the
# command runs them, against the .ic-meter goldens; and programs the
# goldens do not cover (CaseTests, UDTTests, a pattern lambda, a qualified
# import): their displays and, guided, haskell-final's `--ic --meter`
# counts. One `ok NAME` line per group (FAIL NAME when it breaks). Run from
# the source root.

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

# Term construction (ICTests' helpers)
# ------------------------------------

def z() -> Co.V:
  Co.VZero{}

def p(a: Co.V, b: Co.V) -> Co.V:
  Co.VPair{a, b}

def se(x: Co.V) -> Co.V:
  Co.VSetEnv{x}

def d(+n: U32, x: Co.V) -> Co.V:
  Co.VDefer{n, x}

def env() -> Co.V:
  Co.VEnv{}

def left(x: Co.V) -> Co.V:
  Co.VLeft{x}

# \f x -> f (f x), a closed closure: the church numeral two.
def church.two() -> Co.V:
  p(d(20, p(d(21, Co.app(Co.var(1n), Co.app(Co.var(1n), Co.var(0n)))), env())), z())

# \x -> (0, x)
def succ.c() -> Co.V:
  p(d(22, p(z(), Co.var(0n))), z())

def num(n: Nat) -> Co.V:
  match n:
    case 0n:
      z()
    case 1n+k:
      p(z(), num(k))

# Unapplied, a value; applied to itself, it never stops.
def omega() -> Co.V:
  d(1, se(p(left(env()), env())))

def omega.applied() -> Co.V:
  se(p(omega(), p(omega(), z())))

# Outcomes
# --------

# What icEval gives: the value, the abort it carries, or the runtime error.
def result.of(m: Maybe<&2, Co.D>, +x: Co.V) -> String:
  match m:
    case Some{msg}:
      "abort " ++ Co.show.data(msg)
    case None{}:
      Co.show(x)

def result(r: IC.Run) -> String:
  match r:
    case IC.Run{net, out, spent}:
      match out:
        case IC.RBOk{+x}:
          result.of(Ss.aborted(x), x)
        case IC.RBErr{e}:
          "error " ++ e

def eval(t: Co.V, +fuel: U32) -> String:
  +prog = IC.prepare.closed(t)
  result(IC.run(prog, IC.net.new(prog), Co.DZero{}, fuel))

def gives(t: Co.V, v: Co.V) -> Bool:
  String.eq(eval(t, IC.default.fuel()), Co.show(v))

def aborts(t: Co.V, m: Co.V) -> Bool:
  String.eq(eval(t, IC.default.fuel()), "abort " ++ Co.show(m))

def runs.dry(t: Co.V, +fuel: U32) -> Bool:
  String.starts_with(eval(t, fuel), "error ICFuelExhausted")

def all(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      b && all(rest)

# Sessions
# --------

def prepared(guided: Bool, +expr: Co.V) -> IC.Prog:
  match guided:
    case True{}:
      Ss.prepared(expr)
    case False{}:
      IC.prepare(expr, Map.new(&2, Lf.Shape))

def sized(guided: Bool, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{f}:
      Ss.Replay{["sizing failed"], 0}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          Ss.replay(prepared(guided, expr), lines)

def compiled(guided: Bool, r: Result<&2, &2, String, Fr.Terms>, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{e}:
      Ss.Replay{[e], 0}
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          sized(guided, Sz.size(65536, True{}, E.of.term3(run)), lines)

# A session as the command runs it: guided by EAL.
def session(srcs: List<&2, Fr.Src>, +entry: String, lines: List<&2, String>) -> Ss.Replay:
  compiled(True{}, Fr.compile(srcs, entry), lines)

# The same session unguided: the same displays, sooner (no EAL).
def plain(srcs: List<&2, Fr.Src>, +entry: String, lines: List<&2, String>) -> Ss.Replay:
  compiled(False{}, Fr.compile(srcs, entry), lines)

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

# The last display (displays are newest first).
def last(r: Ss.Replay) -> String:
  match r:
    case Ss.Replay{shown, n}:
      match shown:
        case Con{x, rest}:
          x
        case Nil{}:
          ""

def unlines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      x ++ "\n" ++ unlines(rest)

# Programs the goldens do not cover
# ---------------------------------

# CaseTests' programs: a case on a pair of leaves.
def case.program(+scrut: String, alts: List<&2, String>) -> String:
  unlines(List.append(&2, String,
    ["import Prelude", "main =", "  let toCase = " ++ scrut, "      caseTest =", "        case toCase of"],
    List.append(&2, String, alts, ["  in \\input -> (caseTest, 0)"])))

def case.ints() -> String:
  case.program("(0,(8,2))", ["          (0, (1,2)) -> \"False\"", "          (1, (8,2)) -> \"False\"",
                             "          (0,(8,2)) -> \"True\""])

def case.strings() -> String:
  case.program("(\"a string\",(\"hi, sam\",\"str\"))",
    ["          (\"a string\", (\"hi, sam\",2)) -> \"False\"", "          (1, (8,2)) -> \"False\"",
     "          (\"a string\",(\"hi, sam\",\"str\")) -> \"True\""])

def case.all() -> String:
  case.program("(\"a string\",(\"Hi, sam!\",\"str\"))",
    ["          (\"a string\", (\"Hi, sam!\",2)) -> \"False\"", "          (1, (8,2)) -> \"False\"",
     "          (\"a string\",(x,\"str\")) -> x"])

# The property tests' two shapes, on one pattern: it is reachable, and an
# ignore before it takes everything.
def case.reachable() -> String:
  case.program("((3,\"s1\"),(0,0))", ["          ((3,\"s1\"),(var0,var1)) -> \"True\"", "          _ -> \"False\""])

def case.ignore() -> String:
  case.program("((3,\"s1\"),(0,0))", ["          _ -> \"True\"", "          ((3,\"s1\"),(var0,var1)) -> \"False\""])

def case.nonexhaustive() -> String:
  unlines(["import Prelude", "main = \\input ->", "  let r = case 3 of", "            0 -> \"zero\"",
           "            1 -> \"one\"", "  in (r, 0)"])

def pattern.lambda() -> String:
  unlines(["import Prelude", "main = \\input -> let f = \\(a, b) -> b", "                 in (f (0, \"pat\"), 0)"])

# UDTTests: the Prelude's Rational, and NatUDTTests' Nat.
def rational() -> String:
  unlines(["import Prelude",
    "main = \\input -> (if dEqual (left (right (rPlus (fromRational 1 2) (fromRational 1 2)))) 1 then \"ok\" else \"bad\", 0)"])

def nat() -> String:
  unlines(["import Prelude",
    "[Nat, toNat, fromNat, nPlus, nMinus] = \\h ->",
    "  [ \\x -> (h, x)",
    "  , \\(x : Nat) -> x",
    "  , \\(aa : Nat) (bb : Nat) -> (h, d2c aa succ bb)",
    "  , \\(aa : Nat) (bb : Nat) ->",
    "      let sLeft = \\x -> case x of",
    "                          (l, _) -> l",
    "                          y      -> abort \"can't subtract larger number from smaller one\"",
    "      in (h, d2c bb sLeft aa)",
    "  ]",
    "main = \\input -> (if dEqual (right (nPlus (toNat 2) (toNat 3))) 5 then \"ok\" else \"bad\", 0)"])

# UDTTests' natural arithmetic, a digit per case.
def arithmetic() -> String:
  unlines(["import Prelude",
    "b = \\x -> if x then \"1\" else \"0\"",
    "main = \\input ->",
    "  ( concat [ b (dEqual (dPlus 1 2) 3), b (dEqual (dMinus 5 3) 2), b (dEqual (dMinus 0 1) 0)",
    "           , b (dEqual (dTimes 3 4) 12), b (dEqual (dDiv 8 2) 4), b (dEqual (dEqual 3 3) 1)",
    "           , b (dEqual (dEqual 3 4) 0), b (dEqual (dMod 10 3) 1)",
    "           ]",
    "  , 0)"])

def qualified() -> String:
  unlines(["import Prelude", "import qualified Other as O",
           "main = \\input -> (if dEqual O.foo 3 then \"ok\" else \"bad\", 0)"])

def with.prelude(+prelude: String, +name: String, text: String) -> List<&2, Fr.Src>:
  [Fr.Src{"Prelude", prelude}, Fr.Src{name, text}]

def shows(+prelude: String, text: String, +out: String) -> Bool:
  String.eq(last(plain(with.prelude(prelude, "M", text), "M", [])), out)

def costs(+prelude: String, text: String, +n: U32) -> Bool:
  U32.is_eq(spent(session(with.prelude(prelude, "M", text), "M", [])), n)

def report(+prelude: String, +tc: String, +plus: String, +ttt: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("ic-application", all([
      gives(se(p(d(100, env()), z())), z()),
      gives(se(p(d(107, z()), p(z(), z()))), z()),
      gives(Co.app(p(d(106, left(env())), z()), p(z(), z())), p(z(), z())),
      gives(se(p(d(108, p(d(109, left(env())), env())), z())), p(d(109, left(env())), z()))])))
    IO.print(verdict("ic-projection", all([
      gives(left(p(p(z(), z()), z())), p(z(), z())),
      gives(Co.VRight{p(p(z(), z()), z())}, z()),
      gives(left(z()), z()),
      gives(left(se(p(d(112, env()), p(z(), p(z(), z()))))), z())])))
    IO.print(verdict("ic-duplication", all([
      gives(se(p(d(101, p(env(), env())), p(z(), z()))), p(p(z(), z()), p(z(), z()))),
      gives(se(p(d(102, p(env(), env())), d(103, env()))), p(d(103, env()), d(103, env()))),
      gives(se(p(d(110, p(se(p(env(), z())), se(p(env(), p(z(), z()))))), d(111, env()))),
        p(z(), p(z(), z())))])))
    IO.print(verdict("ic-gates", all([
      gives(Co.gate.switch(p(z(), z()), z(), z()), p(z(), z())),
      gives(Co.gate.switch(p(z(), z()), z(), p(z(), z())), z()),
      gives(Co.gate.switch(d(105, env()), z(), p(z(), z())), z()),
      gives(Co.gate.switch(z(), p(z(), z()), se(p(d(113, env()), p(z(), z())))), p(z(), z()))])))
    IO.print(verdict("ic-abort", all([
      gives(se(p(Co.VAbort{}, z())), d(Co.abort.ind(), env())),
      gives(se(p(se(p(Co.VAbort{}, z())), p(z(), z()))), p(z(), z())),
      aborts(se(p(Co.VAbort{}, p(z(), z()))), p(z(), z())),
      aborts(left(se(p(Co.VAbort{}, p(z(), z())))), p(z(), z())),
      gives(Co.gate.switch(z(), left(se(p(Co.VAbort{}, p(z(), z())))), z()), z())])))
    IO.print(verdict("ic-church", all([
      gives(Co.app(Co.app(church.two(), succ.c()), z()), num(2n)),
      gives(Co.app(Co.app(church.two(), Co.app(church.two(), succ.c())), z()), num(4n)),
      gives(Co.app(Co.app(church.two(), Co.app(church.two(), Co.app(church.two(), succ.c()))), z()), num(8n))])))
    IO.print(verdict("ic-fuel", runs.dry(Co.app(Co.app(church.two(), succ.c()), z()), 3)))
    IO.print(verdict("ic-laziness", all([
      gives(se(p(d(200, Co.ite(p(z(), z()), left(env()), omega.applied())), p(z(), z()))), z()),
      runs.dry(se(p(d(201, se(p(se(p(Co.VGate{}, p(z(), z()))), p(omega.applied(), left(env()))))), p(z(), z()))), 50000),
      gives(se(p(d(202, se(p(se(p(Co.VGate{}, p(z(), z()))), p(se(p(p(z(), z()), z())), left(env()))))), p(z(), z()))), z())])))
    IO.print(verdict("ic-omega", runs.dry(omega.applied(), 100000)))
    IO.print(verdict("ic-case", all([
      shows(prelude, case.ints(), "True"),
      shows(prelude, case.strings(), "True"),
      shows(prelude, case.all(), "Hi, sam!"),
      shows(prelude, case.reachable(), "True"),
      shows(prelude, case.ignore(), "True"),
      shows(prelude, case.nonexhaustive(), "runtime error:\nAborted, user abort: Non-exhaustive patterns in case"),
      shows(prelude, pattern.lambda(), "pat")])))
    IO.print(verdict("ic-udt", all([
      shows(prelude, rational(), "ok"),
      shows(prelude, nat(), "ok"),
      shows(prelude, arithmetic(), "11111111"),
      String.eq(last(plain([Fr.Src{"Prelude", prelude}, Fr.Src{"Other", "foo = 3\n"}, Fr.Src{"M", qualified()}], "M", [])), "ok")])))
    IO.print(verdict("ic-meter-case-udt", all([
      costs(prelude, case.nonexhaustive(), 10361),
      costs(prelude, pattern.lambda(), 24276),
      costs(prelude, rational(), 6774269),
      U32.is_eq(spent(session([Fr.Src{"Prelude", prelude}, Fr.Src{"Other", "foo = 3\n"}, Fr.Src{"M", qualified()}], "M", [])), 1252)])))
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
