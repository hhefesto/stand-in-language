import Base
import ./Text.bend as Tx
import ./Core.bend as Co
import ./Front.bend as Fr
import ./Size.bend as Sz
import ./Reference.bend as Rf

# The REPL (master's app/Repl.hs, `telomare-repl`): an expression over the
# Prelude, compiled as a unit test is (sized uncapped, its aborts made
# inert), evaluated by the reference evaluator, and printed as a number,
# a pair of what it holds, or as the expression it evaluated to
# (PrettyBasic). `telomare-repl --expr EXPR` evaluates one expression and
# exits; with no `--expr`, each line read is one, until `:q` or the end of
# the input. An assignment, `name = expression`, binds name for the lines
# after it.
#
# Not ported yet: `:t` (EAL's verdict), `:d`, `:p`, `:l`, `:r`, and the
# multi-line `:{` `:}`; haskeline's line editing.

# An expression's value, as master's REPL prints it (PrettyBasic): a
# number, a pair, or anything else as the core shows it.
def number(v: Co.V) -> Maybe<&2, U32>:
  match v:
    case Co.VZero{}:
      Some{0}
    case Co.VPair{n, Co.VZero{}}:
      Co.to.int.succ(number(n))
    case _:
      None{}

def pair.text(m: Maybe<&2, U32>, +a: String, +b: String) -> String:
  match m:
    case Some{n}:
      U32.show(n)
    case None{}:
      "(" ++ a ++ "," ++ b ++ ")"

def pretty(+v: Co.V) -> String:
  match v:
    case Co.VZero{}:
      "0"
    case Co.VPair{+a, +b}:
      pair.text(number(Co.VPair{a, b}), pretty(a), pretty(b))
    case other:
      Co.show(other)

# compileUnitTestNoAbort: every abort left in the sized term becomes the
# identity's code, so a value never aborts in the REPL.
def no.abort(v: Co.V) -> Co.V:
  match v:
    case Co.VAbort{o, m}:
      Co.VDefer{Co.neg(9), Co.VEnv{}}
    case Co.VPair{a, b}:
      Co.VPair{no.abort(a), no.abort(b)}
    case Co.VSetEnv{x}:
      Co.VSetEnv{no.abort(x)}
    case Co.VDefer{fi, x}:
      Co.VDefer{fi, no.abort(x)}
    case Co.VLeft{x}:
      Co.VLeft{no.abort(x)}
    case Co.VRight{x}:
      Co.VRight{no.abort(x)}
    case other:
      other

def evaluated(st: Rf.St) -> String:
  match st:
    case Rf.SDone{+v, c}:
      pretty(v)
    case Rf.SErr{msg, c}:
      "error: " ++ msg
    case _:
      "error: evaluation did not finish"

# The expression run as the REPL's backend runs one: its body applied to 0.
def value(+x: Co.V) -> String:
  evaluated(Rf.run(Co.VSetEnv{Co.VPair{Co.VDefer{Co.neg(1), no.abort(x)}, Co.VZero{}}}))

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "error: the expression did not size"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks, +plain}:
          value(plain)

def compiled(r: Result<&2, &2, String, Fr.Program>) -> String:
  match r:
    case Fail{e}:
      e
    case Done{p}:
      match p:
        case Fr.Program{+run, g, boundary}:
          sized(Sz.size(65536, False{}, run))

# The bindings so far, as a module over the Prelude, and the expression to
# evaluate under them.
def module(+binds: String, +expr: String) -> String:
  "import Prelude\n" ++ binds ++ "main = " ++ expr ++ "\n"

def eval(+prelude: String, +binds: String, +expr: String) -> String:
  compiled(Fr.compile.program([Fr.Src{"Prelude", prelude}, Fr.Src{"Repl", module(binds, expr)}], "Repl"))

# Whether a line is an assignment: a name, then `=` (not `==`).
def is.word(+c: U32) -> Bool:
  (U32.is_ge(c, 97) && U32.is_le(c, 122)) || (U32.is_ge(c, 65) && U32.is_le(c, 90))
    || (U32.is_ge(c, 48) && U32.is_le(c, 57)) || U32.is_eq(c, 95)

def after.spaces(s: String) -> String:
  match s:
    case SCon{Chr{+c}, +rest}:
      Bool.pick(String, U32.is_eq(c, 32), after.spaces(rest), SCon{Chr{c}, rest})
    case SNil{}:
      ""

def after.word(s: String) -> String:
  match s:
    case SCon{Chr{+c}, +rest}:
      Bool.pick(String, is.word(c), after.word(rest), SCon{Chr{c}, rest})
    case SNil{}:
      ""

def assigns.at(+rest: String) -> Bool:
  String.starts_with(rest, "=") && Bool.not(String.starts_with(rest, "=="))

def assigns(+s: String) -> Bool:
  Bool.not(String.eq(after.word(s), s)) && assigns.at(after.spaces(after.word(s)))

type St is Type:
  Loop{i: Tx.In, binds: String}
  Quit{}

def stepped(+prelude: String, i: Tx.In, +binds: String, a: Bool, +line: String) -> IO(St):
  match a:
    case True{}:
      IO.pure(St, Loop{i, binds ++ line ++ "\n"})
    case False{}:
      do IO<St>:
        IO.print(eval(prelude, binds, line))
        return Loop{i, binds}

def line(+prelude: String, i: Tx.In, +binds: String, quit: Bool, +text: String) -> IO(St):
  match quit:
    case True{}:
      IO.pure(St, Quit{})
    case False{}:
      stepped(prelude, i, binds, assigns(text), text)

def got(+prelude: String, +binds: String, l: Tx.Line) -> IO(St):
  match l:
    case Tx.Line{i, g}:
      match g:
        case Tx.GLine{+text}:
          line(prelude, i, binds, String.eq(text, ":q"), text)
        case _:
          IO.pure(St, Quit{})

def loop(n: Nat, +prelude: String, s: St) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+k:
      match s:
        case Loop{i, +binds}:
          do IO<Unit>:
            IO.write("telomare> ")
            l : Tx.Line <- Tx.read_line(i)
            next : St <- got(prelude, binds, l)
            loop(k, prelude, next)
        case Quit{}:
          IO.pure(Unit, Unit{})

def expr.or.loop(+prelude: String, args: List<String>) -> IO(Unit):
  match args:
    case "--expr" <> e <> rest:
      IO.print(eval(prelude, "", e))
    case "-e" <> e <> rest:
      IO.print(eval(prelude, "", e))
    case "--haskell" <> rest:
      expr.or.loop(prelude, rest)
    case _:
      loop(U32.to_nat(4294967295), prelude, Loop{Tx.Closed{}, ""})

def with.prelude(r: Result<&1, &1, String, String>, args: List<String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "telomare-repl: Prelude.tel: " ++ e)
    case Done{+prelude}:
      match args:
        case self <> rest:
          expr.or.loop(prelude, rest)
        case _:
          loop(U32.to_nat(4294967295), prelude, Loop{Tx.Closed{}, ""})

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    xs : List<String> <- IO.args()
    with.prelude(r, xs)
