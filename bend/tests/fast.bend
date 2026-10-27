import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Loc.bend as Lc
import ../Core.bend as Co
import ../Lift.bend as Lf
import ../IC.bend as IC
import ../Session.bend as Ss
import ../Text.bend as Tx

# `--fast`: programs run unsized on the IC, every recursion unbounded
# (haskell-final's RunModeTests "running without sizing", and the fast
# halves of ConformanceTests and ResolverTests): the same transcripts as
# the sized runs, a step that does not demand its recursion, unrolls per
# site, a program sizing rejects, and the fuel cap. One `ok NAME` line per
# group (FAIL NAME when it breaks). Run from the source root.

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

def with.prelude(+prelude: String, +name: String, text: String) -> List<&2, Fr.Src>:
  [Fr.Src{"Prelude", prelude}, Fr.Src{name, text}]

# Sessions
# --------

def unguided(r: Result<&2, &2, String, Co.V>) -> Maybe<&2, IC.Prog>:
  match r:
    case Fail{form}:
      None{}
    case Done{v}:
      Some{IC.prepare(v, Map.new(&2, Lf.Shape))}

def fast.guard(m: Maybe<&2, T.C>) -> Maybe<&2, IC.Prog>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      unguided(E.fast(t))

def fast.of(r: Result<&2, &2, String, Co.V>, g: Maybe<&2, IC.Prog>, +h: Ss.How, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{form}:
      Ss.Replay{["left " ++ form], Ss.cost.none()}
    case Done{v}:
      Ss.replay(Ss.Prog{IC.prepare(v, Map.new(&2, Lf.Shape)), g, None{}}, h, lines)

def fast.compiled(r: Result<&2, &2, String, Fr.Program>, +h: Ss.How, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{e}:
      Ss.Replay{[e], Ss.cost.none()}
    case Done{p}:
      match p:
        case Fr.Program{run, g, boundary}:
          fast.of(E.fast(run), fast.guard(g), h, lines)

# A session run unsized, each iteration capped at fuel (0: no cap), main's
# input refinements run first, as the command runs it.
def fast(srcs: List<&2, Fr.Src>, +entry: String, +fuel: U32, lines: List<&2, String>) -> Ss.Replay:
  fast.compiled(Fr.compile.program(srcs, entry), Ss.Fast{fuel}, lines)

def sized.expr(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Maybe<&2, Co.V>:
  match r:
    case Fail{f}:
      None{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks, pl}:
          Some{expr}

def guard.expr(m: Maybe<&2, T.C>) -> Maybe<&2, Co.V>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      sized.expr(Sz.size(65536, True{}, t))

def sized.of(g: Maybe<&2, Co.V>, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{f}:
      Ss.Replay{["sizing failed"], Ss.cost.none()}
    case Done{s}:
      match s:
        case Sz.Sized{counts, +expr, checks, +pl}:
          Ss.replay(Ss.session(expr, g, pl), Ss.Sized{}, lines)

def sized.compiled(r: Result<&2, &2, String, Fr.Program>, lines: List<&2, String>) -> Ss.Replay:
  match r:
    case Fail{e}:
      Ss.Replay{[e], Ss.cost.none()}
    case Done{p}:
      match p:
        case Fr.Program{run, +g, +boundary}:
          sized.of(guard.expr(g), Sz.size.guarded(65536, boundary, g, run), lines)

# The same session sized, as the command runs it.
def sized(srcs: List<&2, Fr.Src>, +entry: String, lines: List<&2, String>) -> Ss.Replay:
  sized.compiled(Fr.compile.program(srcs, entry), lines)

def joined(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      x ++ "\n--\n" ++ joined(rest)

# The displays, newest first, one string.
def shown(r: Ss.Replay) -> String:
  match r:
    case Ss.Replay{xs, c}:
      joined(xs)

def last(r: Ss.Replay) -> String:
  match r:
    case Ss.Replay{xs, c}:
      match xs:
        case Con{x, rest}:
          x
        case Nil{}:
          ""

def agree(srcs: List<&2, Fr.Src>, +entry: String, +lines: List<&2, String>) -> Bool:
  +both = srcs
  String.eq(shown(fast(both, entry, 0, lines)), shown(sized(both, entry, lines)))

# Unrolls
# -------

def unroll.le(a: IC.Unroll, b: IC.Unroll) -> Bool:
  match a:
    case IC.Unroll{ta, na}:
      match b:
        case IC.Unroll{tb, nb}:
          U32.is_le(ta, tb)

def unrolls.text(us: List<&2, IC.Unroll>) -> String:
  match us:
    case Nil{}:
      ""
    case Con{u, rest}:
      match u:
        case IC.Unroll{tok, n}:
          "#" ++ U32.show(tok) ++ " " ++ U32.show(n) ++ ";" ++ unrolls.text(rest)

# Each site's unrolls, by token.
def sites(r: Ss.Replay) -> String:
  match r:
    case Ss.Replay{xs, c}:
      match c:
        case Ss.Cost{spent, us}:
          unrolls.text(List.sort(~IC.Unroll, ~unroll.le, us))

# A step that does not demand its recursion
# -----------------------------------------

def closure(+fi: U32, code: E.X) -> E.X:
  E.XPair{E.XDefer{fi, code}, E.XZero{}}

# Site 0's step closed over {t, r, b}, applied to (0, 0): its test answers
# 0, so it takes its base case, (0, 0), and its recursive branch (0, not a
# function) is never demanded. One unroll.
def base.case() -> Result<&2, &2, String, Co.V>:
  +step = E.limit.code(0)
  +trb = {E.XPair{closure(30, E.XZero{}), E.XPair{E.XZero{}, E.XPair{closure(31, E.XLeft{E.XEnv{}}), E.XZero{}}}} : E.X}
  E.core(Map.new(&2, Lc.Origin), E.app(E.XPair{step, E.XPair{step, trb}}, E.XPair{E.XZero{}, E.XZero{}}))

def base.run(r: IC.Run) -> Bool:
  match r:
    case IC.Run{net, out, spent, us}:
      match out:
        case IC.RBOk{x}:
          String.eq(Co.show(x), Co.show(Co.VPair{Co.VZero{}, Co.VZero{}}))
            && String.eq(unrolls.text(us), "#0 1;")
        case IC.RBErr{f}:
          False{}

def base.ran(r: Result<&2, &2, String, Co.V>) -> Bool:
  match r:
    case Fail{form}:
      False{}
    case Done{v}:
      +p = IC.prepare.closed(v)
      base.run(IC.run(p, IC.net.new(p), Co.DZero{}, 10000))

# The report
# ----------

def size.fails(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Bool:
  match r:
    case Fail{f}:
      True{}
    case Done{s}:
      False{}

# Whether sizing rejects the program.
def unsized.fails(r: Result<&2, &2, String, T.C>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{run}:
      size.fails(Sz.size(65536, True{}, run))

def report(+prelude: String, +tc: String, +plus: String, +ttt: String, +unb: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("fast-agrees", all([
      agree([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal", []),
      agree(with.prelude(prelude, "simpleplus", plus), "simpleplus", ["3 4"]),
      agree(with.prelude(prelude, "tictactoe", ttt), "tictactoe", ["1", "9", "2", "8", "3"])])))
    IO.print(verdict("fast-base-case", base.ran(base.case())))
    IO.print(verdict("fast-sites", String.eq(
      sites(fast(with.prelude(prelude, "simpleplus", plus), "simpleplus", 16777216, ["3 4"])),
      "#0 20;#1 24;#2 6;#3 5;")))
    IO.print(verdict("fast-unsized", all([
      unsized.fails(Fr.compile(with.prelude(prelude, "unbounded-input-recursion", unb), "unbounded-input-recursion")),
      String.eq(shown(fast(with.prelude(prelude, "unbounded-input-recursion", unb), "unbounded-input-recursion", 0, ["a", "a"])),
                "#\n--\n \n--\n")])))
    IO.print(verdict("fast-fuel", all([
      String.starts_with(last(fast(with.prelude(prelude, "simpleplus", plus), "simpleplus", 20, ["3 4"])),
                         "runtime error: out of fuel after 20 interactions.\n"),
      String.eq(last(fast(with.prelude(prelude, "simpleplus", plus), "simpleplus", 0, ["3 4"])), "3 plus 4 is 7")])))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("test/programs/simpleplus.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    unb : Result<&1, &1, String, String> <- Tx.read_file("test/programs/limits/unbounded-input-recursion.tel")
    report(text(prelude), text(tc), text(plus), text(ttt), text(unb))
