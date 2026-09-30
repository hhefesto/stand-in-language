import Base
import ../Loc.bend as L
import ../Syntax.bend as S
import ../Parse.bend as P
import ../Expand.bend as E
import ../Front.bend as Fr
import ../Term.bend as T
import ../Text.bend as Tx

# The front end: haskell-final's ParserTests cases the port can answer,
# expansion errors, every shipped program, and the recursion sites and
# resolver error the goldens record. One `ok NAME` line per group (FAIL
# NAME when it breaks). Run from the source root, where the programs are.

# The recursion sites of the run term, as the certificate lists them.

type Site is Data:
  Site{+tok: U32, +loc: String}

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

def all(xs: List<&2, Bool>) -> Bool:
  List.all(~&2, ~Bool, ~(b => b), xs)

def parses(r: Result<&2, &2, P.PErr, S.Surf>) -> Bool:
  Result.is_done(&2, &2, P.PErr, S.Surf, r)

def accepts(text: String) -> Bool:
  parses(P.expression("", text))

def rejects(text: String) -> Bool:
  Bool.not(accepts(text))

def lines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      x ++ "\n" ++ lines(rest)

# ParserTests' accepted expressions.
def accepted() -> List<&2, Bool>:
  [accepts("(foo \"woops\" , 0)"),
   accepts("(foo \"woops\" )"),
   accepts("if 0 then foo \"woops\" else 0"),
   accepts("[ foo \"woops\" ]"),
   accepts("let in_value = 0 in in_value"),
   accepts("[]"),
   accepts("app left (pair zero zero)"),
   accepts("left (\\x y z -> [x, y, z, 0], 0) 1 2 3"),
   accepts("right (\\x y z -> [x, y, z, 0], 0) 1 2 3"),
   accepts("trace (\\x -> (\\y -> (x,y))) 0 0"),
   accepts("app (\\x y z -> x) 0 1 2"),
   accepts("# (\\x -> x)"),
   accepts("(\"Hello World!\", \"0\")"),
   accepts(lines(["if", "  1", "then 1", "else", "  2"])),
   accepts(lines(["if 1", "  then", "                1", "              else 2"])),
   accepts(lines(["if 1", "   then", "                1", "              else 2"])),
   accepts(lines(["if 1", "    then", "                1", "              else 2"])),
   accepts(lines(["if", "    1", "  then (\"Hello, world!\", 0)", "  else", "    (\"Goodbye, world!\", 1)"])),
   accepts(lines(["\\input ->", "  if", "    1", "   then (\"Hello, world!\", 0)", "   else", "    (\"Goodbye, world!\", 1)"])),
   accepts(lines(["[ 0", ", 1", ", 2", "]"])),
   accepts("[0,1,2]"),
   accepts("[ 0 , 1 , 2 ]"),
   accepts(lines(["[ 0 , 1", ", 2 ]"])),
   accepts(lines(["[ 0 , 1", ",2 ]"])),
   accepts(lines(["[ 0,", "  1,", "  2 ]"])),
   accepts(lines(["let x = 0", "    y = 1", "in (x,y)"])),
   accepts("\\(x, y) z -> x"),
   accepts("\\(v : Nat) -> v"),
   accepts("\\0 0 -> 1"),
   accepts("case x of (a, b) -> a"),
   accepts("{-c {- nested -} c-} f -- line\n                        x")]

# ParserTests' rejected expressions: trailing input, a let definition out
# of column, and literals that do not fit (a U32 here, an Int there).
def rejected() -> List<&2, Bool>:
  [rejects("0 ???"),
   rejects(lines(["let x = 0", "  y = 1", "in (x,y)"])),
   rejects(lines(["let x = 0", "      y = 1", "in (x,y)"])),
   rejects("4294967296"),
   rejects("$4294967296"),
   rejects("\\4294967296 -> 0")]

def left.assoc(r: Result<&2, &2, P.PErr, S.Surf>) -> Bool:
  match r:
    case Done{S.SApp{a, S.SApp{b, S.SVar{c, "f"}, S.SVar{d, "x"}}, S.SVar{e, "y"}}}:
      True{}
    case _:
      False{}

def at.pos(l: L.Loc, line: U32, col: U32) -> Bool:
  match l:
    case L.Src{file, L.Pos{+l2, +c2, off}, stop}:
      U32.is_eq(l2, line) && U32.is_eq(c2, col)
    case _:
      False{}

# Where names start: a variable at its first character, a let binding's
# name and a lambda's binder at theirs.
def spans.var(r: Result<&2, &2, P.PErr, S.Surf>) -> Bool:
  match r:
    case Done{S.SVar{loc, name}}:
      at.pos(loc, 1, 1)
    case _:
      False{}

def spans.let(r: Result<&2, &2, P.PErr, S.Surf>) -> Bool:
  match r:
    case Done{S.SLetSugar{loc, Con{S.DSingle{L.Name{nloc, "foo"}, body}, Nil{}}, b}}:
      at.pos(nloc, 1, 5)
    case _:
      False{}

def spans.lam(r: Result<&2, &2, P.PErr, S.Surf>) -> Bool:
  match r:
    case Done{S.SLamPat{loc, Con{S.LPat{ploc, S.PVar{L.Name{nloc, "foo"}}}, Nil{}}, b}}:
      at.pos(nloc, 1, 2)
    case _:
      False{}

def module.items(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> Bool:
  match r:
    case Done{Con{S.IImport{S.Import{loc, L.Name{ml, "Data.List"}, Some{L.Name{ql, "L"}}}},
               Con{S.IDef{S.DSingle{L.Name{nl, "main"}, body}}, Nil{}}}}:
      True{}
    case _:
      False{}

def module.fails(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> Bool:
  Result.is_fail(&2, &2, P.PErr, List<&2, S.Item>, r)

# Expansion errors
# ----------------

def expanded(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> Result<&2, &2, E.ExpErr, List<&2, S.EItem>>:
  match r:
    case Fail{e}:
      Fail{E.MissingMain{}}
    case Done{items}:
      E.module(items)

def expand(text: String) -> Result<&2, &2, E.ExpErr, List<&2, S.EItem>>:
  expanded(P.module("", text))

def arity(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) -> Bool:
  match r:
    case Fail{E.ListArityMismatch{loc, n, m}}:
      Nat.is_eq(n, 2n) && Nat.is_eq(m, 3n)
    case _:
      False{}

def not.list(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) -> Bool:
  match r:
    case Fail{E.UDTBodyNotList{loc, tname, desc}}:
      String.eq(tname, "T") && String.eq(desc, "IntUPF 0")
    case _:
      False{}

def udt.arity(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) -> Bool:
  match r:
    case Fail{E.UDTArityMismatch{loc, tname, n, m}}:
      Nat.is_eq(n, 2n) && Nat.is_eq(m, 2n)
    case _:
      False{}

def udt.ok(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) -> Bool:
  Result.is_done(&2, &2, E.ExpErr, List<&2, S.EItem>, r)

# Programs
# --------

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def module.parses(+name: String, t: String) -> Bool:
  Result.is_done(&2, &2, P.PErr, List<&2, S.Item>, P.module(name, t))

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

def tok.of(s: Site) -> U32:
  match s:
    case Site{tok, loc}:
      tok

def ins.pick(le: Bool, +s: Site, x: Site, rest: List<&2, Site>, later: List<&2, Site>) -> List<&2, Site>:
  match le:
    case True{}:
      s <> x <> rest
    case False{}:
      x <> later

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

def site.text(s: Site) -> String:
  match s:
    case Site{tok, loc}:
      loc ++ " (#" ++ U32.show(tok) ++ ")"

def sites.text(xs: List<&2, Site>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      match rest:
        case Nil{}:
          site.text(x)
        case Con{y, more}:
          site.text(x) ++ ", " ++ sites.text(Con{y, more})

def sites(r: Result<&2, &2, String, Fr.Terms>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{Fr.Terms{cert, run}}:
      sites.text(sort(walk(U32.to_nat(4000000000), run, []), []))

def error(r: Result<&2, &2, String, Fr.Terms>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{ts}:
      "(compiled)"

def with.prelude(+name: String, t: String, +prelude: String) -> List<&2, Fr.Src>:
  [Fr.Src{"Prelude", prelude}, Fr.Src{name, t}]

def report(+prelude: String, +ttt: String, +plus: String, +tc: String, +tchar: String,
        +over: String, +unb: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("parse-accept", all(accepted())))
    IO.print(verdict("parse-reject", all(rejected())))
    IO.print(verdict("parse-left-assoc", left.assoc(P.expression("", "f x y"))))
    IO.print(verdict("parse-spans", spans.var(P.expression("", "foo   "))
      && spans.let(P.expression("", "let foo = 0 in foo"))
      && spans.lam(P.expression("", "\\foo -> foo"))))
    IO.print(verdict("parse-module", module.items(P.module("Example", "import qualified Data.List as L\nmain = 0\n"))))
    IO.print(verdict("parse-empty-list-def", module.fails(P.module("", "[] = []"))))
    IO.print(verdict("expand-errors", arity(expand("[a, b] = [1, 2, 3]\n"))
      && not.list(expand("[T, mk] = \\h -> 0\n"))
      && udt.arity(expand("[T, mk] = \\h -> [0, 1]\n"))
      && udt.ok(expand("[T] = \\h -> []\n"))))
    IO.print(verdict("programs-parse", all([
      module.parses("Prelude", prelude), module.parses("tictactoe", ttt),
      module.parses("simpleplus", plus), module.parses("tc_ultra_minimal", tc),
      module.parses("testchar", tchar), module.parses("over-budget-recursion", over),
      module.parses("unbounded-input-recursion", unb)])))
    IO.print(verdict("sites-tc_ultra_minimal", String.eq(
      sites(Fr.compile([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal")),
      "tc_ultra_minimal:6:25 (#0)")))
    IO.print(verdict("sites-simpleplus", String.eq(
      sites(Fr.compile(with.prelude("simpleplus", plus, prelude), "simpleplus")),
      "Prelude:30:18 (#0), Prelude:48:23 (#1), simpleplus:12:42 (#2), simpleplus:12:28 (#3)")))
    IO.print(verdict("sites-tictactoe", String.eq(
      sites(Fr.compile(with.prelude("tictactoe", ttt, prelude), "tictactoe")),
      "Prelude:30:18 (#0), Prelude:48:23 (#1), Prelude:62:24 (#2), Prelude:67:42 (#3), tictactoe:31:50 (#4), tictactoe:31:28 (#5), tictactoe:59:65 (#6), tictactoe:59:43 (#7), tictactoe:60:57 (#8), tictactoe:61:57 (#9), tictactoe:74:45 (#10), tictactoe:77:63 (#11), tictactoe:88:51 (#12), tictactoe:96:45 (#13)")))
    IO.print(verdict("sites-limits", String.eq(
      sites(Fr.compile(with.prelude("over-budget-recursion", over, prelude), "over-budget-recursion")),
      "over-budget-recursion:30:34 (#0)") && String.eq(
      sites(Fr.compile(with.prelude("unbounded-input-recursion", unb, prelude), "unbounded-input-recursion")),
      "unbounded-input-recursion:27:34 (#0)")))
    IO.print(verdict("testchar-error", String.eq(
      error(Fr.compile([Fr.Src{"testchar", tchar}], "testchar")),
      "RE (missing definition \"not\" at line 2, column 52)")))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("simpleplus.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    tchar : Result<&1, &1, String, String> <- Tx.read_file("testchar.tel")
    over : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/over-budget-recursion.tel")
    unb : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/unbounded-input-recursion.tel")
    report(text(prelude), text(ttt), text(plus), text(tc), text(tchar), text(over), text(unb))
