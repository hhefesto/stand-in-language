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

def num(n: Nat) -> Co.V:
  match n:
    case 0n:
      z()
    case 1n+k:
      p(z(), num(k))

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

# A closed term and the fuel to run it at. Closed terms cover the rules C
# leaves to Bend (stuck values, an abort's message, fuel running out).
type Case is Data:
  Case{t: Co.V, +fuel: U32}

def closed() -> List<&2, Case>:
  [Case{Co.app(Co.app(church.two(), Co.app(church.two(), succ.c())), z()), IC.default.fuel()},
   Case{se(p(d(102, p(env(), env())), d(103, env()))), IC.default.fuel()},
   Case{Co.gate.switch(z(), p(z(), z()), se(p(d(113, env()), p(z(), z())))), IC.default.fuel()},
   Case{Co.VAbort{Lc.unknown.origin(), p(z(), z())}, IC.default.fuel()},
   Case{left(Co.VAbort{Lc.unknown.origin(), Co.VAbort{Lc.unknown.origin(), z()}}), IC.default.fuel()},
   Case{se(p(z(), z())), IC.default.fuel()},
   Case{se(z()), IC.default.fuel()},
   Case{Co.gate.switch(d(105, env()), z(), p(z(), z())), IC.default.fuel()},
   Case{Co.VRight{z()}, IC.default.fuel()},
   Case{Co.VRight{num(40n)}, IC.default.fuel()},
   Case{left(p(num(3n), num(4n))), IC.default.fuel()},
   Case{se(p(d(130, p(env(), env())), num(40n))), IC.default.fuel()},
   Case{se(p(d(131, z()), num(40n))), IC.default.fuel()},
   Case{se(p(d(132, Co.VRight{env()}), num(3n))), IC.default.fuel()},
   Case{Co.gate.switch(num(4n), z(), num(2n)), IC.default.fuel()},
   Case{Co.VAbort{Lc.unknown.origin(), num(3n)}, IC.default.fuel()},
   Case{Co.app(num(3n), z()), IC.default.fuel()},
   Case{se(num(3n)), IC.default.fuel()},
   Case{Co.app(Co.app(church.two(), succ.c()), z()), 3},
   Case{omega.applied(), 100000}]

def cases.io(cs: List<&2, Case>) -> List<&1, IO(Bool)>:
  match cs:
    case Nil{}:
      []
    case Con{c, rest}:
      match c:
        case Case{t, +fuel}:
          Con{both(t, fuel), cases.io(rest)}

def all.io(xs: List<&1, IO(Bool)>) -> IO(Bool):
  match xs:
    case Nil{}:
      IO.pure(Bool, True{})
    case Con{x, rest}:
      do IO<Bool>:
        a : Bool <- x
        b : Bool <- all.io(rest)
        return a && b

# One pair of every two kinds
# ---------------------------

# The sessions leave some rules unfired, so every two kinds meet here, alone
# on a net, their other ports wired to ext agents. Kinds that would read the
# store (a closure's code applied, a constant opened) are the sessions' to
# cover. `a` and `c`: their first words.
type Meet is Data:
  Meet{+ka: U32, +a: U32, +kb: U32, +c: U32}

def store.rule(r: IC.Rule) -> Bool:
  match r:
    case IC.RApplyRef{}:
      True{}
    case IC.ROpen{}:
      True{}
    case _:
      False{}

def meet.kinds() -> List<&2, U32>:
  [IC.era(), IC.zero(), IC.gate(), IC.konst(), IC.ref(), IC.pair(), IC.aborted(), IC.dup(),
   IC.split(), IC.setenv(), IC.apply(), IC.scrut(), IC.left(), IC.right(), IC.stuck()]

def meet.keep(skip: Bool, +m: Meet, acc: List<&2, Meet>) -> List<&2, Meet>:
  match skip:
    case True{}:
      acc
    case False{}:
      Con{m, acc}

def meet.row(+ka: U32, ks: List<&2, U32>, acc: List<&2, Meet>) -> List<&2, Meet>:
  match ks:
    case Nil{}:
      acc
    case Con{+kb, rest}:
      meet.row(ka, rest, meet.keep(
        store.rule(IC.rule.of(IC.ak.of(ka), IC.ak.of(kb))) || store.rule(IC.rule.of(IC.ak.of(kb), IC.ak.of(ka))),
        Meet{ka, 5, kb, 6}, acc))

def meet.rows(ks: List<&2, U32>, acc: List<&2, Meet>) -> List<&2, Meet>:
  match ks:
    case Nil{}:
      acc
    case Con{+ka, rest}:
      meet.rows(rest, meet.row(ka, meet.kinds(), acc))

# Every two kinds, and two Dups of one label.
def meets() -> List<&2, Meet>:
  meet.rows(meet.kinds(), [Meet{IC.dup(), 5, IC.dup(), 5}])

def aux.one(has: Bool, net: IC.Net, +p: U32, +q: U32) -> IC.Net:
  match has:
    case True{}:
      IC.connect(net, p, q)
    case False{}:
      net

# Agent x of kind k's auxiliary ports, wired to ext agents e and f.
def aux(net: IC.Net, +k: U32, +x: U32, +e: U32, +f: U32) -> IC.Net:
  aux.one(U32.is_ge(IC.arity(k), 3),
          aux.one(U32.is_ge(IC.arity(k), 2), net, IC.port(x, 1), IC.port(e, 0)),
          IC.port(x, 2), IC.port(f, 0))

def meet.wired(+ka: U32, +kb: U32, +n: U32, +m: U32, +e1: U32, +e2: U32, +e3: U32, r: IC.Net & U32) -> IC.Net:
  (net, +e4) = r
  IC.connect(aux(aux(net, ka, n, e1, e2), kb, m, e3, e4), IC.port(n, 0), IC.port(m, 0))

def meet.e3(+ka: U32, +kb: U32, +n: U32, +m: U32, +e1: U32, +e2: U32, r: IC.Net & U32) -> IC.Net:
  (net, +e3) = r
  meet.wired(ka, kb, n, m, e1, e2, e3, IC.alloc(net, IC.ext(), 0, 0))

def meet.e2(+ka: U32, +kb: U32, +n: U32, +m: U32, +e1: U32, r: IC.Net & U32) -> IC.Net:
  (net, +e2) = r
  meet.e3(ka, kb, n, m, e1, e2, IC.alloc(net, IC.ext(), 0, 0))

def meet.e1(+ka: U32, +kb: U32, +n: U32, +m: U32, r: IC.Net & U32) -> IC.Net:
  (net, +e1) = r
  meet.e2(ka, kb, n, m, e1, IC.alloc(net, IC.ext(), 0, 0))

def meet.m(+ka: U32, +kb: U32, +n: U32, r: IC.Net & U32) -> IC.Net:
  (net, +m) = r
  meet.e1(ka, kb, n, m, IC.alloc(net, IC.ext(), 0, 0))

def meet.n(+kb: U32, +c: U32, +ka: U32, r: IC.Net & U32) -> IC.Net:
  (net, +n) = r
  meet.m(ka, kb, n, IC.alloc(net, kb, c, 0))

# The net of a meeting, its one active pair stacked.
def meet.net(+prog: IC.Prog, m: Meet) -> IC.Net:
  match m:
    case Meet{+ka, +a, +kb, +c}:
      meet.n(kb, c, ka, IC.alloc(IC.reset(IC.net.new(prog), IC.default.fuel()), ka, a, 0))

def meet.prog() -> IC.Prog:
  IC.prepare.closed(z())

def most() -> Nat:
  U32.to_nat(4294967295)

def meet.ok(r: IC.Net & IC.Net & Bool) -> Bool:
  ok.of(r)

def meet.both(+prog: IC.Prog, +m: Meet) -> IO(Bool):
  do IO<Bool>:
    y : IC.Net <- Nt.loop(most(), Nt.Firing{meet.net(prog, m)})
    return meet.ok(same(IC.reduce(most(), IC.pop(meet.net(prog, m))), y))

def meets.io(+prog: IC.Prog, ms: List<&2, Meet>) -> List<&1, IO(Bool)>:
  match ms:
    case Nil{}:
      []
    case Con{+m, rest}:
      Con{meet.both(prog, m), meets.io(prog, rest)}

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
        case Sz.Sized{counts, expr, checks, pl, pro}:
          +m = Ss.prepared(expr)
          iter(1n+List.length(&2, String, lines), m, Again{lines, True{}, IC.net.new(m), IC.net.new(m), Co.DZero{}})

def compiled(r: Result<&2, &2, String, T.C>, lines: List<&2, String>) -> IO(Bool):
  match r:
    case Fail{e}:
      IO.pure(Bool, False{})
    case Done{+run}:
      sized(Sz.size(65536, True{}, run), lines)

def session(srcs: List<&2, Fr.Src>, +entry: String, lines: List<&2, String>) -> IO(Bool):
  compiled(Fr.compile(srcs, entry), lines)

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def report(+prelude: String, +tc: String, +plus: String, +ttt: String) -> IO(Unit):
  do IO<Unit>:
    terms : Bool <- all.io(cases.io(closed()))
    IO.print(verdict("native-terms", terms))
    pairs : Bool <- all.io(meets.io(meet.prog(), meets()))
    IO.print(verdict("native-pairs", pairs))
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
