import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Loc.bend as Lc
import ../Core.bend as Co
import ../IC.bend as IC
import ../Session.bend as Ss
import ../Text.bend as Tx
import ../Native.bend as Nt

# The IC's loop in C (bend/Native.bend over bend/effs/ic.c) against
# IC.bend's own: every run here is made both ways, and each pair of runs
# must leave the same net, word for word (every agent the run touched, and
# the control words), with the same result and the same interactions
# spent. Closed terms cover the rules C leaves to Bend (stuck values, an
# abort's message, fuel running out); the example programs' sessions, run
# on the same net from one iteration to the next as the command runs them,
# cover the rest, guided copying included. One `ok NAME` line per group
# (FAIL NAME when it breaks). Run from the source root.

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

# Two nets, word for word
# -----------------------

def c.words(c: IC.Ctl) -> List<&2, U32>:
  match c:
    case IC.Ctl{sp, cold, bump, free, label, fuel, err, cap}:
      [sp, bump, free, label, fuel, err, cap, IC.cold.nmsg(IC.c.cold(IC.Ctl{sp, cold, bump, free, label, fuel, err, cap}))]

def words.eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case _:
          False{}
    case Con{+x, xr}:
      match ys:
        case Con{+y, yr}:
          U32.is_eq(x, y) && words.eq(xr, yr)
        case Nil{}:
          False{}

# Words i.. of two nets (r and s: word i read), n of them.
def same.go(n: Nat, +i: U32, r: IC.Net & U32, s: IC.Net & U32, ok: Bool) -> IC.Net & IC.Net & Bool:
  match n:
    case 0n:
      (x, a) = r
      (y, b) = s
      (x, (y, ok))
    case 1n+k:
      (x, +a) = r
      (y, +b) = s
      same.go(k, (i + 1 : U32), IC.rd(x, (i + 1 : U32)), IC.rd(y, (i + 1 : U32)), ok && U32.is_eq(a, b))

def same.ctl(r: IC.Net & IC.Ctl, s: IC.Net & IC.Ctl) -> IC.Net & IC.Net & Bool:
  (x, +c) = r
  (y, +d) = s
  same.go(U32.to_nat((IC.c.bump(c) * 8 : U32)), 0, IC.rd(x, 0), IC.rd(y, 0), words.eq(c.words(c), c.words(d)))

# Whether x and y are the same net: the same control words, and the same
# words for every agent up to the bump.
def same(x: IC.Net, y: IC.Net) -> IC.Net & IC.Net & Bool:
  same.ctl(IC.ctl.of(x), IC.ctl.of(y))

def shown(r: IC.RB) -> String:
  match r:
    case IC.RBOk{x}:
      Co.show(x)
    case IC.RBErr{f}:
      "error " ++ IC.fault.show(f)

# Closed terms
# ------------

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

def church.two() -> Co.V:
  p(d(20, p(d(21, Co.app(Co.var(1n), Co.app(Co.var(1n), Co.var(0n)))), env())), z())

def succ.c() -> Co.V:
  p(d(22, p(z(), Co.var(0n))), z())

def omega() -> Co.V:
  d(1, se(p(left(env()), env())))

def omega.applied() -> Co.V:
  se(p(omega(), p(omega(), z())))

# Two runs agree: the same net, the same interactions, the same result.
def agree(+spent: U32, +spent2: U32, out: IC.RB, out2: IC.RB, r: IC.Net & IC.Net & Bool) -> IC.Net & IC.Net & Bool:
  (x, rest) = r
  (y, ok) = rest
  (x, (y, ok && U32.is_eq(spent, spent2) && String.eq(shown(out), shown(out2))))

def ok.of(r: IC.Net & IC.Net & Bool) -> Bool:
  (x, rest) = r
  (y, ok) = rest
  ok

def both.got(r: IC.Run, s: IC.Run) -> Bool:
  match r:
    case IC.Run{x, out, +spent, us}:
      match s:
        case IC.Run{y, out2, +spent2, us2}:
          ok.of(agree(spent, spent2, out, out2, same(x, y)))

# t run both ways at the given fuel.
def both(t: Co.V, +fuel: U32) -> IO(Bool):
  +prog = IC.prepare.closed(t)
  do IO<Bool>:
    s : IC.Run <- Nt.run(prog, IC.net.new(prog), Co.DZero{}, fuel)
    return both.got(IC.run(prog, IC.net.new(prog), Co.DZero{}, fuel), s)

def all.io(xs: List<&1, IO(Bool)>) -> IO(Bool):
  match xs:
    case Nil{}:
      IO.pure(Bool, True{})
    case Con{x, rest}:
      do IO<Bool>:
        a : Bool <- x
        b : Bool <- all.io(rest)
        return a && b

# Sessions
# --------

# Iterations of main on the lines, both ways, each on the net the last left
# (no guard: its runs are runs like these): what is left to do.
type Next is Type:
  Stop{ok: Bool}
  Again{lines: List<&2, String>, ok: Bool, x: IC.Net, y: IC.Net, input: Co.D}

def again(more: List<&2, String>, +line: String, ok: Bool, o: Ss.Outcome, r: IC.Net & IC.Net & Bool) -> Next:
  match o:
    case Ss.Continue{display, +st}:
      (x, rest) = r
      (y, agreed) = rest
      Again{more, ok && agreed, x, y, Co.DPair{Co.of.string(line), st}}
    case _:
      Stop{ok && ok.of(r)}

def next.of(ls: List<&2, String>, ok: Bool, o: Ss.Outcome, r: IC.Net & IC.Net & Bool) -> Next:
  match ls:
    case Nil{}:
      Stop{ok && ok.of(r)}
    case Con{line, more}:
      again(more, line, ok, o, r)

def next(lines: List<&2, String>, ok: Bool, r: IC.Run, s: IC.Run) -> Next:
  match r:
    case IC.Run{x, +out, +spent, us}:
      match s:
        case IC.Run{y, out2, +spent2, us2}:
          next.of(lines, ok, Ss.outcome(Ss.Sized{}, out), agree(spent, spent2, out, out2, same(x, y)))

def stopped(s: Next) -> Bool:
  match s:
    case Stop{ok}:
      ok
    case _:
      False{}

def iter(n: Nat, +m: IC.Prog, s: Next) -> IO(Bool):
  match n:
    case 0n:
      IO.pure(Bool, stopped(s))
    case 1n+k:
      match s:
        case Stop{ok}:
          IO.pure(Bool, ok)
        case Again{lines, ok, x, y, +input}:
          do IO<Bool>:
            r : IC.Run <- Nt.run(m, y, input, IC.default.fuel())
            iter(k, m, next(lines, ok, IC.run(m, x, input, IC.default.fuel()), r))

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, +lines: List<&2, String>) -> IO(Bool):
  match r:
    case Fail{f}:
      IO.pure(Bool, False{})
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks, pl}:
          +m = Ss.prepared(expr)
          iter(1n+List.length(&2, String, lines), m, Again{lines, True{}, IC.net.new(m), IC.net.new(m), Co.DZero{}})

def compiled(r: Result<&2, &2, String, Fr.Program>, lines: List<&2, String>) -> IO(Bool):
  match r:
    case Fail{e}:
      IO.pure(Bool, False{})
    case Done{p}:
      match p:
        case Fr.Program{run, g, +boundary}:
          sized(Sz.size.guarded(65536, boundary, g, run), lines)

def session(srcs: List<&2, Fr.Src>, +entry: String, lines: List<&2, String>) -> IO(Bool):
  compiled(Fr.compile.program(srcs, entry), lines)

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def report(+prelude: String, +tc: String, +plus: String, +ttt: String) -> IO(Unit):
  do IO<Unit>:
    terms : Bool <- all.io([
      both(Co.app(Co.app(church.two(), Co.app(church.two(), succ.c())), z()), IC.default.fuel()),
      both(se(p(d(102, p(env(), env())), d(103, env()))), IC.default.fuel()),
      both(Co.gate.switch(z(), p(z(), z()), se(p(d(113, env()), p(z(), z())))), IC.default.fuel()),
      both(Co.VAbort{Lc.unknown.origin(), p(z(), z())}, IC.default.fuel()),
      both(left(Co.VAbort{Lc.unknown.origin(), Co.VAbort{Lc.unknown.origin(), z()}}), IC.default.fuel()),
      both(se(p(z(), z())), IC.default.fuel()),
      both(se(z()), IC.default.fuel()),
      both(Co.gate.switch(d(105, env()), z(), p(z(), z())), IC.default.fuel()),
      both(Co.VRight{z()}, IC.default.fuel()),
      both(Co.app(Co.app(church.two(), succ.c()), z()), 3),
      both(omega.applied(), 100000)])
    IO.print(verdict("native-terms", terms))
    sessions : Bool <- all.io([
      session([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal", []),
      session([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus", ["3 4"]),
      session([Fr.Src{"Prelude", prelude}, Fr.Src{"tictactoe", ttt}], "tictactoe", ["1", "4", "2", "5", "3"])])
    IO.print(verdict("native-sessions", sessions))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("test/programs/simpleplus.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    report(text(prelude), text(tc), text(plus), text(ttt))
