import Base
import ../Core.bend as Co
import ../Lift.bend as Lf
import ../Loc.bend as Lc
import ../IC.bend as IC
import ../Sem.bend as Sm

# Sem against the net, on every small term of the core, ill-shaped ones
# too: each must give the same answer, and no pair of two consumers (two
# input ports, so two Dups among them) may meet. Evidence for what
# NetProof.bend and NetModel.bend begin to prove. One `ok NAME` line per
# group (FAIL NAME when it breaks), and one line per disagreement. Run from
# the source root.

# Sem's answer as text
def stuck(o: Sm.O) -> Bool:
  match o:
    case Sm.OStuck{}:
      True{}
    case Sm.OPair{a, b}:
      stuck(a) || stuck(b)
    case _:
      False{}

def show.o(o: Sm.O) -> String:
  match o:
    case Sm.OZero{}:
      "0"
    case Sm.OPair{a, b}:
      "(" ++ show.o(a) ++ "," ++ show.o(b) ++ ")"
    case Sm.OCode{fi}:
      "C" ++ U32.show(fi)
    case Sm.OGate{}:
      "G"
    case Sm.OAbort{}:
      "Abort"
    case Sm.OAborted{at, m}:
      "A[" ++ show.o(m) ++ "]"
    case Sm.OStuck{}:
      "stuck"
    case Sm.OHole{p}:
      "hole"

def sem.pick(yes: Bool, +o: Sm.O) -> String:
  match yes:
    case True{}:
      "stuck"
    case False{}:
      show.o(o)

def sem.out(r: Sm.R) -> String:
  match r:
    case Sm.Obs{+o}:
      sem.pick(stuck(o), o)
    case Sm.Spent{}:
      "fuel"
    case _:
      "nonplain"

# The net's answer as text
def show.v(v: Co.V) -> String:
  match v:
    case Co.VZero{}:
      "0"
    case Co.VPair{a, b}:
      "(" ++ show.v(a) ++ "," ++ show.v(b) ++ ")"
    case Co.VDefer{fi, x}:
      "C" ++ U32.show(fi)
    case Co.VGate{}:
      "G"
    case Co.VAbort{o, m}:
      "A[" ++ show.v(m) ++ "]"
    case _:
      "?"

def show.t(v: Co.V) -> String:
  match v:
    case Co.VZero{}:
      "0"
    case Co.VPair{a, b}:
      "P(" ++ show.t(a) ++ "," ++ show.t(b) ++ ")"
    case Co.VEnv{}:
      "E"
    case Co.VSetEnv{x}:
      "S(" ++ show.t(x) ++ ")"
    case Co.VDefer{fi, x}:
      "D(" ++ show.t(x) ++ ")"
    case Co.VGate{}:
      "G"
    case Co.VLeft{x}:
      "L(" ++ show.t(x) ++ ")"
    case Co.VRight{x}:
      "R(" ++ show.t(x) ++ ")"
    case Co.VAbort{o, m}:
      "A(" ++ show.t(m) ++ ")"

def fault(f: IC.Fault) -> String:
  match f:
    case IC.FuelExhausted{n}:
      "fuel"
    case IC.Stuck{m}:
      "stuck"
    case IC.Internal{m}:
      "internal:" ++ m

def rb.out(r: IC.RB) -> String:
  match r:
    case IC.RBOk{+x}:
      show.v(x)
    case IC.RBErr{f}:
      fault(f)

def run.out(r: IC.Run) -> String:
  match r:
    case IC.Run{net, out, spent, unrolls}:
      rb.out(out)

# The reduce loop, counting pairs of two consumers
def is.cons(+k: U32) -> Bool:
  U32.is_eq(k, IC.era()) || U32.is_eq(k, IC.dup()) || U32.is_eq(k, IC.split()) || U32.is_eq(k, IC.setenv())
    || U32.is_eq(k, IC.apply()) || U32.is_eq(k, IC.scrut()) || U32.is_eq(k, IC.left()) || U32.is_eq(k, IC.right())

def look.b(+ka: U32, r: IC.Net & U32) -> IC.Net & U32:
  (net, +kb) = r
  (net, Bool.pick(U32, is.cons(ka) && is.cons(kb), 1, 0))

def look.a(+b: U32, r: IC.Net & U32) -> IC.Net & U32:
  (net, +ka) = r
  look.b(ka, IC.kind.of(net, b))

type Sc is Type:
  Sc{st: IC.Popped, +bad: U32}

def fire.c(+a: U32, +b: U32, +bad: U32, r: IC.Net & U32) -> Sc:
  (net, +d) = r
  Sc{IC.pop(IC.fire(net, a, b)), (bad + d : U32)}

def end.of(s: Sc) -> IC.Net & U32:
  match s:
    case Sc{st, +bad}:
      match st:
        case IC.PEmpty{net}:
          (net, bad)
        case IC.PStale{net}:
          (net, bad)
        case IC.PPair{net, a, b}:
          (net, bad)

def scan(fuel: Nat, s: Sc) -> IC.Net & U32:
  match fuel:
    case 0n:
      end.of(s)
    case 1n+f:
      match s:
        case Sc{st, +bad}:
          match st:
            case IC.PEmpty{net}:
              (net, bad)
            case IC.PStale{net}:
              scan(f, Sc{IC.pop(net), bad})
            case IC.PPair{net, +a, +b}:
              scan(f, fire.c(a, b, bad, look.a(b, IC.kind.of(net, a))))

def fin.go(+bodies: IC.Read, +root: U32, r: IC.Net & U32) -> IC.Run & U32:
  (net, +bad) = r
  (IC.finish.root(bodies, root, IC.peer(net, (root * 4 : U32))), bad)

def fin(+bodies: IC.Read, r: IC.CS & U32) -> IC.Run & U32:
  (cs, +root) = r
  fin.go(bodies, root, scan(U32.to_nat(4294967295), Sc{IC.pop(IC.cs.net(cs)), 0}))

def run.scan(p: IC.Prog, net: IC.Net, input: Co.D, +fuel: U32) -> IC.Run & U32:
  match p:
    case IC.Prog{entry, +bodies, words, maxk, +os}:
      fin(IC.Read{bodies, os}, IC.start(entry, input)(IC.CS{IC.reset(net, fuel), Map.new(&2, List<&2, U32>)}))

def verdict.of(+t: String, +s: String, r: IC.Run & U32) -> String:
  (run, +bad) = r
  +i = run.out(run)
  Bool.pick(String, String.eq(s, i) && U32.is_zero(bad), "",
    "M " ++ t ++ " sem=" ++ s ++ " ic=" ++ i ++ " bad=" ++ U32.show(bad))

def closure(+body: Co.V) -> Co.V:
  Co.VPair{Co.VDefer{100, body}, Co.VZero{}}

# One term on one input: "" when both agree and no consumers met.
def one(+main: Co.V, +input: Co.D, +tag: String) -> String:
  +prog = IC.prepare(main, Map.new(&2, Lf.Shape))
  verdict.of(show.t(main) ++ " on " ++ tag,
             sem.out(Sm.run(U32.to_nat(4000000), Sm.plain(), Sm.of.core(main), Sm.of.data(input))),
             run.scan(prog, IC.net.new(prog), input, IC.default.fuel()))

def counted(+s: String) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{c, r}:
      1

def say(+s: String) -> IO(Unit):
  match s:
    case SNil{}:
      IO.pure(Unit, Unit{})
    case SCon{c, r}:
      IO.print(s)

def go(ts: List<&2, Co.V>, +input: Co.D, +tag: String, +n: U32) -> IO(U32):
  match ts:
    case Nil{}:
      IO.pure(U32, n)
    case Con{+t, rest}:
      +line = one(closure(t), input, tag)
      do IO<U32>:
        u : Unit <- say(line)
        go(rest, input, tag, (n + counted(line) : U32))

# Enumeration
def unary(xs: List<&2, Co.V>) -> List<&2, Co.V>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      Co.VLeft{x} <> Co.VRight{x} <> Co.VSetEnv{x} <> Co.VDefer{100, x} <> Co.VAbort{Lc.unknown.origin(), x} <> unary(rest)

def with.a(+a: Co.V, ys: List<&2, Co.V>, acc: List<&2, Co.V>) -> List<&2, Co.V>:
  match ys:
    case Nil{}:
      acc
    case Con{+y, rest}:
      with.a(a, rest, Co.VPair{a, y} <> acc)

def pairs(xs: List<&2, Co.V>, +ys: List<&2, Co.V>, acc: List<&2, Co.V>) -> List<&2, Co.V>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, rest}:
      pairs(rest, ys, with.a(x, ys, acc))

def leaves() -> List<&2, Co.V>:
  [Co.VZero{}, Co.VEnv{}, Co.VGate{}]

def next(+a: List<&2, Co.V>, +b: List<&2, Co.V>) -> List<&2, Co.V>:
  List.append(&2, Co.V, leaves(), List.append(&2, Co.V, unary(a), pairs(a, b, [])))

def t1() -> List<&2, Co.V>:
  next(leaves(), leaves())

def t2() -> List<&2, Co.V>:
  next(t1(), t1())

def app.each(xs: List<&2, Co.V>) -> List<&2, Co.V>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Co.VSetEnv{x} <> app.each(rest)

def fn.each(xs: List<&2, Co.V>, +ys: List<&2, Co.V>) -> List<&2, Co.V>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      List.append(&2, Co.V, app.each(with.a(Co.VDefer{100, x}, ys, [])), fn.each(rest, ys))

def ifs.r(+s: Co.V, +l: Co.V, ys: List<&2, Co.V>, acc: List<&2, Co.V>) -> List<&2, Co.V>:
  match ys:
    case Nil{}:
      acc
    case Con{+r, rest}:
      ifs.r(s, l, rest, Co.gate.switch(l, r, s) <> acc)

def ifs.l(+s: Co.V, xs: List<&2, Co.V>, +ys: List<&2, Co.V>, acc: List<&2, Co.V>) -> List<&2, Co.V>:
  match xs:
    case Nil{}:
      acc
    case Con{+l, rest}:
      ifs.l(s, rest, ys, ifs.r(s, l, ys, acc))

def ifs(ss: List<&2, Co.V>, +xs: List<&2, Co.V>, acc: List<&2, Co.V>) -> List<&2, Co.V>:
  match ss:
    case Nil{}:
      acc
    case Con{+s, rest}:
      ifs(rest, xs, ifs.l(s, xs, xs, acc))

def zero() -> Co.D:
  Co.DZero{}

def pr() -> Co.D:
  Co.DPair{Co.DZero{}, Co.DPair{Co.DZero{}, Co.DZero{}}}

def verdict(+name: String, +bad: U32) -> IO(Unit):
  IO.print(Bool.pick(String, U32.is_zero(bad), "ok ", "FAIL ") ++ name)

def groups(+a: List<&2, Co.V>, +b: List<&2, Co.V>) -> IO(Unit):
  do IO<Unit>:
    n0 : U32 <- go(next(b, a), zero(), "0", 0)
    verdict("netsem-terms-on-zero", n0)
    n1 : U32 <- go(pairs(a, b, []), zero(), "0", 0)
    verdict("netsem-pairs-on-zero", n1)
    n2 : U32 <- go(fn.each(b, a), zero(), "0", 0)
    verdict("netsem-functions", n2)
    n3 : U32 <- go(app.each(pairs(b, a, [])), pr(), "pr", 0)
    verdict("netsem-applications", n3)
    n4 : U32 <- go(ifs(a, a, []), pr(), "pr", 0)
    verdict("netsem-ifs", n4)
    n5 : U32 <- go(next(b, a), pr(), "pr", 0)
    verdict("netsem-terms-on-pair", n5)

def main() -> IO(Unit):
  groups(t1(), t2())
