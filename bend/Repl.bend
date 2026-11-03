import Base
import ./Text.bend as Tx
import ./Loc.bend as L
import ./Core.bend as Co
import ./Front.bend as Fr
import ./Size.bend as Sz
import ./Reference.bend as Rf
import ./Syntax.bend as S
import ./Term.bend as T
import ./Parse.bend as P
import ./Expand.bend as E
import ./Resolve.bend as Rs
import ./Desugar.bend as D
import ./Lower.bend as Lw
import ./Split.bend as Sp
import ./Lift.bend as Lf
import ./EALm.bend as EM
import ./Partial.bend as Pe

# The REPL (master's app/Repl.hs, `telomare-repl`). Its bindings are the
# Prelude's definitions, then those of each assignment and loaded file in
# turn (a name keeps its first binding). A line is an assignment, `name =
# expression`, which binds; or an expression, compiled under a let of the
# bindings as a unit test is (sized uncapped, its aborts made inert),
# evaluated by the reference evaluator, and printed as a number, a pair of
# what it holds, or as the expression it evaluated to (PrettyBasic); or a
# parse error, shown (the port's parser's words). `telomare-repl --expr
# EXPR` evaluates one expression and exits; with no `--expr`, the REPL
# reads lines until `:q` or the end of the input. Its commands, as
# master's:
#
#   :d EXPR   the expression alone, compiled, as prettyPrint shows it;
#   :p EXPR   the same, partially evaluated (evalPartial), as PrettyBasic;
#   :t EXPR   EAL's verdict on the expression alone;
#   :l FILE   FILE's definitions (no imports) join the bindings;
#   :r        the bindings become the loaded files' definitions alone,
#             read again (the Prelude's and the assignments' go);
#   :{ ... :} the lines between, as one;
#   :q        quit.
#
# Not ported: haskeline's line editing and history.

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

# `:t`
# ----
# Master's `:t` (renderEALVerdict . inferEALWithLifting): the expression
# alone, parsed from column 1 of a nameless file, with the builtins but
# neither the Prelude nor the bindings so far (resolveBinding' looks up
# `_tmp_` only, so a name from either fails to resolve).
def verdict(r: Result<&2, &2, EM.Err, EM.MR>) -> String:
  match r:
    case Fail{e}:
      "does not certify: " ++ EM.render(e)
    case Done{m}:
      match m:
        case EM.MR{top, defers, max, shape, shapes, levels}:
          "certifies: max box level " ++ U32.show(max) ++ ", input bang " ++ U32.show(top)

def typed.term(r: Result<&2, &2, Rs.ResErr, T.Term2()>) -> String:
  match r:
    case Fail{e}:
      "some sort of error?"
    case Done{t}:
      verdict(EM.lifted.main(Lf.defer.lift(Sp.split(t))))

def program.text(r: Result<&2, &2, Fr.Err, Fr.Program>) -> String:
  compiled(Fr.rendered.program(r))

# Reading a line (runReplParser)
# ------------------------------

# What a line is: an assignment (one definition, parseSingleDefinition, as
# bindings), else an expression; or neither, with the expression's error.
type RS is Data:
  RAssign{+bs: List<&2, Rs.NB>}
  RExpr{+x: S.Expanded()}
  RErr{+msg: String}

def nb.of(it: S.EItem, rest: List<&2, Rs.NB>) -> List<&2, Rs.NB>:
  match it:
    case S.EBind{n, v}:
      Rs.NB{L.Name.text(n), v} <> rest
    case S.EImport{i}:
      rest

def nbs(items: List<&2, S.EItem>) -> List<&2, Rs.NB>:
  match items:
    case []:
      []
    case it <> rest:
      nb.of(it, nbs(rest))

# A parse error as master's errorBundlePretty lays it out for a nameless
# input (the port's parser's words).
def perr(+text: String, +e: P.PErr) -> String:
  String.drop(P.render("", text, e), 1n)

def expr.expanded(r: Result<&2, &2, E.ExpErr, S.Expanded()>) -> RS:
  match r:
    case Fail{e}:
      RErr{E.render(e)}
    case Done{x}:
      RExpr{x}

def perr.off(e: P.PErr) -> U32:
  match e:
    case P.PErr{at, msg}:
      match at:
        case L.Pos{l, c, off}:
          off

# Neither parse: megaparsec reports the error that got further (the
# expression's, when they got as far).
def further(+a: P.PErr, +e: P.PErr) -> P.PErr:
  Bool.pick(P.PErr, U32.is_gt(perr.off(a), perr.off(e)), a, e)

def expr.parsed(+text: String, +a: P.PErr, r: Result<&2, &2, P.PErr, S.Parsed()>) -> RS:
  match r:
    case Fail{e}:
      RErr{perr(text, further(a, e))}
    case Done{p}:
      expr.expanded(E.term(p))

# The expression, after the assignment's parse stopped at a.
def as.expr(+text: String, +a: P.PErr) -> RS:
  expr.parsed(text, a, P.expression("", text))

def no.err() -> P.PErr:
  P.PErr{L.Pos{1, 1, 0}, ""}

def assign.expanded(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>, +text: String) -> RS:
  match r:
    case Fail{e}:
      as.expr(text, no.err())
    case Done{items}:
      RAssign{nbs(items)}

# One `name = body` or `name : check = body` (not a list assignment, not
# an import).
def is.single(items: List<&2, S.Item>) -> Bool:
  match items:
    case [S.IDef{S.DSingle{n, b}}]:
      True{}
    case [S.IDef{S.DChecked{n, l, c, b}}]:
      True{}
    case _:
      False{}

def assign.one(single: Bool, +items: List<&2, S.Item>, +text: String) -> RS:
  match single:
    case True{}:
      assign.expanded(E.module(items), text)
    case False{}:
      as.expr(text, no.err())

def assign.parsed(r: Result<&2, &2, P.PErr, List<&2, S.Item>>, +text: String) -> RS:
  match r:
    case Fail{e}:
      as.expr(text, e)
    case Done{+items}:
      assign.one(is.single(items), items, text)

def step.of(+text: String) -> RS:
  assign.parsed(P.module("", text), text)

# Bindings
# --------

def bound(bs: List<&2, Rs.NB>, +n: String) -> Bool:
  match bs:
    case []:
      False{}
    case Rs.NB{+m, v} <> rest:
      String.eq(m, n) || bound(rest, n)

def bind.add(known: Bool, b: Rs.NB, acc: List<&2, Rs.NB>) -> List<&2, Rs.NB>:
  match known:
    case True{}:
      acc
    case False{}:
      b <> acc

def bind.go(new: List<&2, Rs.NB>, +acc: List<&2, Rs.NB>) -> List<&2, Rs.NB>:
  match new:
    case []:
      acc
    case Rs.NB{+n, +v} <> rest:
      bind.go(rest, bind.add(bound(acc, n), Rs.NB{n, v}, acc))

# The bindings with new after them. A name bound already keeps its first
# binding, as in master's REPL (`x = 1`, then `x = 2`: x is 1).
def bind(+bs: List<&2, Rs.NB>, new: List<&2, Rs.NB>) -> List<&2, Rs.NB>:
  List.reverse(&2, Rs.NB, bind.go(new, List.reverse(&2, Rs.NB, bs)))

# printLastExpr: the expression under a let of every binding (those it
# reaches), compiled as a unit test is, run, and printed.
def run.expr(+bs: List<&2, Rs.NB>, +x: S.Expanded()) -> String:
  program.text(Fr.program.of(D.desugar(Rs.main.let(x, Rs.prune(x, bs), S.loc(Empty, Unit, Empty, x)))))

def alone.sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Maybe<&2, Co.V>:
  match r:
    case Fail{f}:
      None{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, x, checks, plain}:
          Some{no.abort(x)}

# `:d`, `:p`, `:t`: the expression alone (resolveBinding: `_tmp_`, with no
# other binding).
def alone(r: Result<&2, &2, Fr.Err, Fr.Program>) -> Maybe<&2, Co.V>:
  match r:
    case Fail{e}:
      None{}
    case Done{p}:
      match p:
        case Fr.Program{+run, g, boundary}:
          alone.sized(Sz.size(65536, False{}, run))

def dumped(m: Maybe<&2, Co.V>) -> String:
  match m:
    case Some{v}:
      Co.pretty(v)
    case None{}:
      "some sort of error?"

def partial.shown(m: Maybe<&2, Co.V>) -> String:
  match m:
    case Some{v}:
      pretty(Pe.partial(v))
    case None{}:
      "some sort of error?"

def typed.x(+x: S.Expanded()) -> String:
  typed.term(Lw.process(D.desugar(x)))

# The three take an expression; anything else is a parse error.
type Cmd is Data:
  CDump{}
  CPartial{}
  CType{}

def dump.of(r: RS) -> String:
  match r:
    case RExpr{x}:
      dumped(alone(Fr.program.of(D.desugar(x))))
    case _:
      "parse error"

def partial.of(r: RS) -> String:
  match r:
    case RExpr{x}:
      partial.shown(alone(Fr.program.of(D.desugar(x))))
    case _:
      "parse error"

def type.of(r: RS) -> String:
  match r:
    case RExpr{x}:
      typed.x(x)
    case _:
      "parse error"

def command.on(c: Cmd, r: RS) -> String:
  match c:
    case CDump{}:
      dump.of(r)
    case CPartial{}:
      partial.of(r)
    case CType{}:
      type.of(r)

# The REPL
# --------

def after.spaces(s: String) -> String:
  match s:
    case SCon{Chr{+c}, +rest}:
      Bool.pick(String, U32.is_eq(c, 32), after.spaces(rest), SCon{Chr{c}, rest})
    case SNil{}:
      ""

def tail(s: String) -> String:
  match s:
    case SCon{c, +rest}:
      rest
    case SNil{}:
      ""

# What the loop holds: the input, the bindings, the files `:l` loaded
# (sorted, as a Set), and in `:{`, the lines so far (newest first).
type St is Type:
  Loop{i: Tx.In, bs: List<&2, Rs.NB>, files: List<&2, String>}
  Multi{i: Tx.In, bs: List<&2, Rs.NB>, files: List<&2, String>, buf: List<&2, String>}
  Quit{}

# replStep: an assignment binds; an expression is printed; a parse error
# is shown.
def stepped(i: Tx.In, +bs: List<&2, Rs.NB>, +files: List<&2, String>, r: RS) -> IO(St):
  match r:
    case RAssign{new}:
      IO.pure(St, Loop{i, bind(bs, new), files})
    case RExpr{+x}:
      do IO<St>:
        IO.print(run.expr(bs, x))
        return Loop{i, bs, files}
    case RErr{msg}:
      do IO<St>:
        IO.print("Parse error: " ++ msg)
        return Loop{i, bs, files}

# Loading a file of definitions (parseDefinitionsFile)
# ----------------------------------------------------

type Ld is Data:
  LOk{+bs: List<&2, Rs.NB>}
  LErr{+msg: String}

def ld.expanded(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) -> Ld:
  match r:
    case Fail{e}:
      LErr{E.render(e)}
    case Done{items}:
      LOk{nbs(items)}

def first.import(items: List<&2, S.Item>) -> Maybe<&2, L.Loc>:
  match items:
    case []:
      None{}
    case it <> rest:
      match it:
        case S.IImport{imp}:
          match imp:
            case S.Import{l, m, q}:
              Some{l}
        case S.IDef{d}:
          first.import(rest)

def ld.at(m: Maybe<&2, L.Pos>, +text: String) -> String:
  match m:
    case Some{L.Pos{+line, +col, off}}:
      String.drop(P.render.at("", text, line, col, "unexpected \"import\"\nexpecting a definition or end of input"), 1n)
    case None{}:
      "unexpected \"import\""

# Definitions only: an import is refused where it stands.
def ld.items(m: Maybe<&2, L.Loc>, +text: String, items: List<&2, S.Item>) -> Ld:
  match m:
    case None{}:
      ld.expanded(E.module(items))
    case Some{l}:
      LErr{ld.at(L.start(l), text)}

def ld.parsed(r: Result<&2, &2, P.PErr, List<&2, S.Item>>, +text: String) -> Ld:
  match r:
    case Fail{e}:
      LErr{perr(text, e)}
    case Done{+items}:
      ld.items(first.import(items), text, items)

def ld.of(+text: String) -> Ld:
  ld.parsed(P.module("", text), text)

def ld.message(+name: String, l: Ld) -> String:
  match l:
    case LOk{bs}:
      "File " ++ name ++ " successfully loaded."
    case LErr{msg}:
      "Error from loaded file: " ++ msg

def ld.bs(l: Ld) -> List<&2, Rs.NB>:
  match l:
    case LOk{bs}:
      bs
    case LErr{msg}:
      []

def ld.ok(l: Ld) -> Bool:
  match l:
    case LOk{bs}:
      True{}
    case LErr{msg}:
      False{}

def set.add.go(xs: List<&2, String>, +x: String) -> List<&2, String>:
  match xs:
    case []:
      [x]
    case +y <> +rest:
      Bool.pick(List<&2, String>, String.is_lt(x, y), x <> y <> rest,
        Bool.pick(List<&2, String>, String.eq(x, y), y <> rest, y <> set.add.go(rest, x)))

# Set.insert, the list kept sorted.
def set.add(ok: Bool, +xs: List<&2, String>, +x: String) -> List<&2, String>:
  match ok:
    case True{}:
      set.add.go(xs, x)
    case False{}:
      xs

# Strict.readFile's failure ends the REPL, as master's does.
def unreadable(+name: String) -> IO(Unit):
  do IO<Unit>:
    IO.print_err("telomare-repl: " ++ name ++ ": openFile: does not exist (No such file or directory)")
    IO.exit(1)

def loaded(i: Tx.In, +bs: List<&2, Rs.NB>, +files: List<&2, String>, +name: String, r: Result<&1, &1, String, String>) -> IO(St):
  match r:
    case Fail{e}:
      do IO<St>:
        unreadable(name)
        return Quit{}
    case Done{+text}:
      +l = ld.of(text)
      do IO<St>:
        IO.print(ld.message(name, l))
        return Loop{i, bind(bs, ld.bs(l)), set.add(ld.ok(l), files, name)}

# `:l FILE`: its definitions after the bindings.
def load(i: Tx.In, +bs: List<&2, Rs.NB>, +files: List<&2, String>, +name: String) -> IO(St):
  do IO<St>:
    r : Result<&1, &1, String, String> <- Tx.read_file(name)
    loaded(i, bs, files, name, r)

# `:r`: the bindings become the loaded files' alone (the Prelude's and
# the assignments' go), each file read again in turn.
def reload.one(+f: String, r: Result<&1, &1, String, String>) -> Ld:
  match r:
    case Fail{e}:
      LErr{""}
    case Done{+text}:
      ld.of(text)

# A file read, its message not yet printed.
type Pend is Data:
  PNone{}
  PSome{+f: String, +l: Ld}

def pend.say(p: Pend) -> IO(Unit):
  match p:
    case PNone{}:
      IO.pure(Unit, Unit{})
    case PSome{f, l}:
      IO.print(ld.message(f, l))

def pend.acc(+acc: List<&2, Rs.NB>, p: Pend) -> List<&2, Rs.NB>:
  match p:
    case PNone{}:
      acc
    case PSome{f, l}:
      bind(acc, ld.bs(l))

def reload.go(fs: List<&2, String>, +acc: List<&2, Rs.NB>, +p: Pend) -> IO(List<&2, Rs.NB>):
  match fs:
    case []:
      do IO<List<&2, Rs.NB>>:
        pend.say(p)
        return pend.acc(acc, p)
    case +f <> rest:
      do IO<List<&2, Rs.NB>>:
        pend.say(p)
        r : Result<&1, &1, String, String> <- Tx.read_file(f)
        reload.go(rest, pend.acc(acc, p), PSome{f, reload.one(f, r)})

def reload(i: Tx.In, +files: List<&2, String>) -> IO(St):
  do IO<St>:
    bs : List<&2, Rs.NB> <- reload.go(files, [], PNone{})
    return Loop{i, bs, files}

# The loop (replLoop)
# -------------------

# What a line asks for, decided once.
type Ask is Data:
  AQuit{}
  AMulti{}
  ACmd{+c: Cmd}
  AReload{}
  ALoad{}
  AStep{}

def ask.of(+s: String) -> Ask:
  Bool.pick(Ask, String.eq(s, ":q"), AQuit{},
  Bool.pick(Ask, String.eq(s, ":{"), AMulti{},
  Bool.pick(Ask, String.starts_with(s, ":d"), ACmd{CDump{}},
  Bool.pick(Ask, String.starts_with(s, ":p"), ACmd{CPartial{}},
  Bool.pick(Ask, String.starts_with(s, ":t"), ACmd{CType{}},
  Bool.pick(Ask, String.eq(s, ":r"), AReload{},
  Bool.pick(Ask, String.starts_with(s, ":l "), ALoad{}, AStep{})))))))

def line.do(i: Tx.In, +bs: List<&2, Rs.NB>, +files: List<&2, String>, a: Ask, +text: String) -> IO(St):
  match a:
    case AQuit{}:
      IO.pure(St, Quit{})
    case AMulti{}:
      IO.pure(St, Multi{i, bs, files, []})
    case ACmd{c}:
      do IO<St>:
        IO.print(command.on(c, step.of(after.spaces(tail(tail(text))))))
        return Loop{i, bs, files}
    case AReload{}:
      reload(i, files)
    case ALoad{}:
      load(i, bs, files, String.drop(text, 3n))
    case AStep{}:
      stepped(i, bs, files, step.of(text))

def got(+bs: List<&2, Rs.NB>, +files: List<&2, String>, l: Tx.Line) -> IO(St):
  match l:
    case Tx.Line{i, g}:
      match g:
        case Tx.GLine{+text}:
          line.do(i, bs, files, ask.of(text), text)
        case _:
          IO.pure(St, Quit{})

def multi.line(i: Tx.In, +bs: List<&2, Rs.NB>, +files: List<&2, String>, +buf: List<&2, String>, done: Bool, +text: String) -> IO(St):
  match done:
    case True{}:
      stepped(i, bs, files, step.of(String.join(List.reverse(&2, String, buf), "\n")))
    case False{}:
      IO.pure(St, Multi{i, bs, files, text <> buf})

# replMultiline: lines up to `:}`, joined; the end of the input ends it
# with nothing.
def multi.got(+bs: List<&2, Rs.NB>, +files: List<&2, String>, +buf: List<&2, String>, l: Tx.Line) -> IO(St):
  match l:
    case Tx.Line{i, g}:
      match g:
        case Tx.GLine{+text}:
          multi.line(i, bs, files, buf, String.eq(text, ":}"), text)
        case _:
          stepped(Tx.Closed{}, bs, files, step.of(""))

def loop(n: Nat, s: St) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+k:
      match s:
        case Loop{i, +bs, +files}:
          do IO<Unit>:
            IO.write("telomare> ")
            l : Tx.Line <- Tx.read_line(i)
            next : St <- got(bs, files, l)
            loop(k, next)
        case Multi{i, +bs, +files, +buf}:
          do IO<Unit>:
            l : Tx.Line <- Tx.read_line(i)
            next : St <- multi.got(bs, files, buf, l)
            loop(k, next)
        case Quit{}:
          IO.pure(Unit, Unit{})

# startExpr: `--expr EXPR` prints the expression's value, or ends with
# master's `error`.
def start.expr(+bs: List<&2, Rs.NB>, r: RS) -> IO(Unit):
  match r:
    case RExpr{+x}:
      IO.print(run.expr(bs, x))
    case RAssign{new}:
      IO.die(Unit, 1, "telomare-repl: Expression is an assignment")
    case RErr{msg}:
      IO.die(Unit, 1, "telomare-repl: Parse error: " ++ msg)

def expr.or.loop(+bs: List<&2, Rs.NB>, args: List<String>) -> IO(Unit):
  match args:
    case "--expr" <> e <> rest:
      start.expr(bs, step.of(e))
    case "-e" <> e <> rest:
      start.expr(bs, step.of(e))
    case "--haskell" <> rest:
      expr.or.loop(bs, rest)
    case _:
      loop(U32.to_nat(4294967295), Loop{Tx.Closed{}, bs, []})

# The Prelude's definitions are the first bindings (none when it does not
# parse).
def with.prelude(r: Result<&1, &1, String, String>, args: List<String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "telomare-repl: Prelude.tel: " ++ e)
    case Done{+prelude}:
      match args:
        case self <> rest:
          expr.or.loop(ld.bs(ld.of(prelude)), rest)
        case _:
          loop(U32.to_nat(4294967295), Loop{Tx.Closed{}, ld.bs(ld.of(prelude)), []})

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    xs : List<String> <- IO.args()
    with.prelude(r, xs)
