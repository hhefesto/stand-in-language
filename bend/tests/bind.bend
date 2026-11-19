import Base
import ../Front.bend as Fr
import ../Bind.bend as B
import ../Size.bend as Sz
import ../Session.bend as Ss
import ../Term.bend as T
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EALm.bend as EM
import ../Core.bend as Co
import ../Text.bend as Tx

# The name binder (bend/Bind.bend, master's 98c963c2): master's
# NameBinderTests, numbered as section 10 of telomare-name-binder-spec.txt
# numbers them, with master's own answers: the display a program makes, the
# resolver's error as the command prints it, and the warnings it prints on
# stderr. One `ok NAME` line per group (FAIL NAME when it breaks). Run from
# the source root.

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

def unlines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      x ++ "\n" ++ unlines(rest)

# Programs
# --------

def last(r: Ss.Replay) -> String:
  match r:
    case Ss.Replay{shown, c}:
      match shown:
        case Con{x, rest}:
          x
        case Nil{}:
          ""

# Main, and its prologue, prepared under the layouts compiling gives them
# (certifiedProgramFrom), as tests/ic.bend has it, or unguided.
def layouts(guided: Bool, +run: T.C, +counts: List<&2, E.TS>, +checks: Sz.Checks, +pl: Co.V, +pro: Maybe<&2, Co.V>) -> Map<&2, Lf.Shape>:
  match guided:
    case True{}:
      Ss.layouts.of(Ss.plan.from(EM.budget.default(), run, counts, Sz.checks.keep(checks), pl, pro))
    case False{}:
      Map.new(&2, Lf.Shape)

def sized(guided: Bool, +run: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{+counts, +expr, +checks, +pl, +pro}:
          last(Ss.replay(Ss.session(expr, layouts(guided, run, counts, checks, pl, pro), pro), Ss.Sized{}, []))

# The first display a program makes on no input, or the error compiling it
# gives, as the command prints it.
def outcome(+guided: Bool, r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{+run}:
      sized(guided, run, Sz.size(65536, True{}, run))

# Modules M1, M2, ... and Main, over the Prelude.
def srcs(+prelude: String, ms: List<&2, Fr.Src>) -> List<&2, Fr.Src>:
  Fr.Src{"Prelude", prelude} <> ms

def runs(+prelude: String, ms: List<&2, Fr.Src>) -> String:
  outcome(False{}, Fr.compile(srcs(prelude, ms), "Main"))

# Guided by EAL, as the command runs it.
def runs.guided(+prelude: String, ms: List<&2, Fr.Src>) -> String:
  outcome(True{}, Fr.compile(srcs(prelude, ms), "Main"))

def main.of(+prelude: String, ls: List<&2, String>) -> String:
  runs(prelude, [Fr.Src{"Main", unlines("import Prelude" <> ls)}])

# The warnings, one a line, as the command prints them on stderr.
def warned(m: Fr.Mods) -> String:
  match m:
    case Fr.Mods{+mods, errs}:
      unlines(B.warnings(mods, True{}, "Main"))

def warns(+prelude: String, ms: List<&2, Fr.Src>) -> String:
  warned(Fr.all(srcs(prelude, ms)))

def warns.main(+prelude: String, ls: List<&2, String>) -> String:
  warns(prelude, [Fr.Src{"Main", unlines("import Prelude" <> ls)}])

def t02() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "             in let x = \"one\"",
   "                in (f 0, 0)"]

def t03() -> List<&2, String>:
  ["main = \\i -> let x = \"outer\"",
   "             in let f = \\n -> x",
   "                in let x = \"inner\"",
   "                   in (f 0, 0)"]

def t04() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "                 g = \\n -> f n",
   "             in let x = \"prop\"",
   "                in (g 0, 0)"]

def t05() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "                 x = \"sib\"",
   "             in (f 0, 0)"]

def t06() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "             in (\\x -> (f 0, 0)) \"lam\""]

def t06w() -> List<&2, String>:
  ["f = \\n -> x",
   "g = \\x -> f 0",
   "main = \\i -> let x = \"top\" in (g 1, 0)"]

def t07() -> List<&2, String>:
  ["h = \\n -> le n",
   "g = \\n -> h n",
   "main = \\i -> (g 0, 0)"]

def t08() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "             in let x = f 0",
   "                in (x, 0)"]

def t09() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "             in let x = y",
   "                in let y = \"why\"",
   "                   in (f 0, 0)"]

def t10() -> List<&2, String>:
  ["main = \\i -> let r : chk = \"checked\"",
   "             in let chk = \\v -> 1",
   "                in (r, 0)"]

def sort.mod() -> Fr.Src:
  Fr.Src{"Sort", "pick = \\a b -> if le a b then a else b\n"}

def t11(+le: String) -> Fr.Src:
  Fr.Src{"Main", unlines(["import Prelude", "import Sort", "main = \\i -> let le = " ++ le,
                          "             in (pick \"first\" \"second\", 0)"])}

def t12() -> List<&2, String>:
  ["f = \\n -> x",
   "main = \\i -> (listPlus (let x = \"a\" in f 0) (let x = \"b\" in f 0), 0)"]

def t13() -> List<&2, String>:
  ["main = \\i -> (listPlus ((\\x -> let x = \"let\" in x) 0)",
   "                        (let x = \"let\" in (\\x -> x) \"lam\"), 0)"]

def t14() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "             in let x = \"let\"",
   "                in (\\x -> (listPlus (f 0) x, 0)) \"lam\""]

def t15() -> List<&2, String>:
  ["main = \\i -> let f = \\n -> x",
   "             in (\\(x : Bool) -> (f 0, 0)) 1"]

def t16(extra: List<&2, String>) -> List<&2, Fr.Src>:
  [Fr.Src{"A", "k = \"a\"\n"}, Fr.Src{"B", "k = \"b\"\n"},
   Fr.Src{"Main", unlines(List.append(&2, String, ["import A", "import B"], List.append(&2, String, extra, ["main = \\i -> (k, 0)"])))}]

def t17.base() -> Fr.Src:
  Fr.Src{"Base", "v = \"v\"\n"}

def t17.mid() -> Fr.Src:
  Fr.Src{"Mid", "import Base\nw = v\n"}

def t20() -> List<&2, String>:
  ["f = \\p -> left p",
   "main = \\i -> let left = \\x -> \"fake\"",
   "             in (f (\"real\", 0), 0)"]

def t21a() -> List<&2, String>:
  ["main = \\i -> let a = \"1\"",
   "                 a = \"2\"",
   "             in (a, 0)"]

def t21b() -> List<&2, String>:
  ["a = \"1\"",
   "a = \"2\"",
   "main = \\i -> (a, 0)"]

def t22() -> List<&2, String>:
  ["g = \\l -> map (\\c -> sep) l",
   "main = \\i -> (listPlus (let sep = 65 in g \"ab\") (let sep = 66 in g \"ab\"), 0)"]

def report(+prelude: String) -> IO(Unit):
  do IO<Unit>:
    # T2, T4, T5, T9: a requirement supplied by the binder around a mention,
    # inherited, by a sibling, or by an open entry; T10: inside a refinement;
    # T12: one open entry instantiated twice
    IO.print(verdict("bind-supply", all([
      String.eq(main.of(prelude, t02()), "one"),
      String.eq(main.of(prelude, t04()), "prop"),
      String.eq(main.of(prelude, t05()), "sib"),
      String.eq(main.of(prelude, t09()), "why"),
      String.eq(main.of(prelude, t10()), "checked"),
      String.eq(main.of(prelude, t12()), "ab"),
      String.eq(warns.main(prelude, t02()), "")])))
    # T3: the definition site wins, with a shadowing and an unused warning
    IO.print(verdict("bind-definition-site", all([
      String.eq(main.of(prelude, t03()), "outer"),
      String.eq(warns.main(prelude, t03()), unlines([
        "warning: \"x\" shadows the binding at Main:2:18 at Main:4:24",
        "warning: \"x\" is never used at Main:4:24"]))])))
    # T6, T15: lambdas, annotated or not, never supply; T7: the chain an
    # unsupplied requirement came through
    IO.print(verdict("bind-unsupplied", all([
      String.eq(main.of(prelude, t06()),
        "RE (\"x\" (at line 2, column 28)\n  is required by \"f\" (line 2, column 18)\n  is required by \"main\" (line 2, column 1)\n  and is not defined)"),
      String.eq(warns.main(prelude, t06w()),
        "warning: variable \"x\" does not supply the requirement \"x\" of what its body mentions at Main:3:6\n"),
      String.eq(main.of(prelude, t15()),
        "RE (\"x\" (at line 2, column 28)\n  is required by \"f\" (line 2, column 18)\n  is required by \"main\" (line 2, column 1)\n  and is not defined)"),
      String.eq(main.of(prelude, t07()),
        "RE (\"le\" (at line 2, column 11)\n  is required by \"h\" (line 2, column 1)\n  is required by \"g\" (line 3, column 1)\n  is required by \"main\" (line 4, column 1)\n  and is not defined)")])))
    # T8: a cycle through a requirement; T21: duplicate keys
    IO.print(verdict("bind-errors", all([
      String.eq(main.of(prelude, t08()), "RE (DefinitionCycle [\"x\",\"x\"])"),
      String.eq(main.of(prelude, t21a()), "RE (\"a\" is defined more than once in one block, at line 3, column 18)"),
      String.eq(main.of(prelude, t21b()), "RE (\"a\" is defined more than once in one block, at line 3, column 1)")])))
    # T13: the nearest binder classifies; T14: a supplied argument is not
    # captured; T20: a builtin is never supplied
    IO.print(verdict("bind-scopes", all([
      String.eq(main.of(prelude, t13()), "letlam"),
      String.eq(warns.main(prelude, t13()), unlines([
        "warning: \"x\" shadows the binding at Main:2:27 at Main:2:36",
        "warning: \"x\" shadows the binding at Main:3:30 at Main:3:45",
        "warning: \"x\" is never used at Main:3:30"])),
      String.eq(main.of(prelude, t14()), "letlam"),
      String.eq(main.of(prelude, t20()), "real"),
      String.eq(warns.main(prelude, t20()), "warning: \"left\" is never used at Main:3:18\n")])))
    # T11: dictionary style across modules; T16: a later import and the
    # module's own definitions shadow; T17: a diamond binds once; T18: no
    # re-export; T19: qualified names
    IO.print(verdict("bind-modules", all([
      String.eq(runs(prelude, [sort.mod(), t11("\\a b -> 1")]), "first"),
      String.eq(runs(prelude, [sort.mod(), t11("\\a b -> 0")]), "second"),
      String.eq(runs(prelude, t16([])), "b"),
      String.eq(runs(prelude, t16(["k = \"m\""])), "m"),
      String.eq(warns(prelude, t16([])), "warning: \"k\" shadows the binding at A:1:1 at Main:2:1\n"),
      String.eq(runs(prelude, [t17.base(), t17.mid(), Fr.Src{"Main", "import Base\nimport Mid\nmain = \\i -> (w, 0)\n"}]), "v"),
      String.eq(runs(prelude, [t17.base(), t17.mid(), Fr.Src{"Main", "import Mid\nmain = \\i -> (v, 0)\n"}]),
        "RE (missing definition \"v\" at line 2, column 15)"),
      String.eq(runs(prelude, [Fr.Src{"Base", "v = \"qv\"\n"}, Fr.Src{"Main", "import qualified Base as Q\nmain = \\i -> (Q.v, 0)\n"}]), "qv"),
      String.eq(runs(prelude, [Fr.Src{"Base", "v = \"qv\"\n"}, Fr.Src{"Main", "import qualified Base as Q\nmain = \\i -> (Q.missing, 0)\n"}]),
        "RE (qualified name \"Q.missing\" is not defined, at line 2, column 15)")])))
    # T22/T23: unsized recursion in an open entry, two instantiations
    IO.print(verdict("bind-recursion", all([
      String.eq(main.of(prelude, t22()), "AABB"),
      String.eq(runs.guided(prelude, [Fr.Src{"Main", unlines("import Prelude" <> t22())}]), "AABB")])))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    report(text(prelude))
