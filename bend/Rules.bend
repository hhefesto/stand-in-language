import Base
import ./Core.bend as Co
import ./IC.bend as IC

# The net's rules as data: the one description the runtime's back ends are
# generated from (HANDOFF P8). A rule is what IC.bend's r.* do, in their
# order, as a list of steps: spend the interaction, delete agents, make new
# ones, wire ports. `act` is the table; `apply` runs it on IC.bend's net, and
# tests/rules.bend holds it to IC.bend's own rules word for word; dev/genic.bend
# prints it as bend/effs/ic.c's rules, and tests/native.bend holds those to
# IC.bend word for word. So IC.bend stays the meaning.
#
# Three things a rule does are not wiring, and each back end has them as its
# own primitives, which IC.bend defines: instantiating a template, reading a
# constant's parts from the store, and guided copying (`region`, which walks
# a whole region of the net in one rule).
#
# A pair is n (i: its contents) meeting m (j), n first, as IC.bend's apply.rule
# has it.

# A word a step needs.
type Wd is Data:
  WLit{+n: U32}
  WKind{+k: U32}
  WIa{}
  WJa{}
  WJb{}
  WJk{}
  WVar{+v: String}

# A port: slot s of an agent this rule made, the two agents' principal ports,
# or what the two agents' auxiliary ports are wired to.
type Pt is Data:
  PNew{+v: String, +s: U32}
  PMe{}
  PIt{}
  PI1{}
  PI2{}
  PJ1{}
  PJ2{}

type Op is Data:
  Spend{}
  DelN{}
  DelM{}
  Del2{}
  # A new agent, named v, of kind k with words a and b.
  New{+v: String, +k: Wd, +a: Wd, +b: Wd}
  # A new agent nothing uses (IC.bend's alloc4 makes four).
  Spare{+k: Wd}
  # A new label, named v.
  Fresh{+v: String}
  # Constant m's part at word `at` of its store entry, as a new agent named v.
  Part{+v: String, +at: U32}
  Wire{+p: Pt, +q: Pt}
  # Template j.a instantiated between i's ports (and, when j.b is an unbounded
  # recursion's step, one more unroll: a back end may leave those to Bend).
  Inst{}

# What a rule does.
type Act is Data:
  # Left to Bend: it makes a stuck value, whose message is a Bend String.
  Bendy{}
  Plain{+ops: List<&2, Op>}
  # Two Dups: `same` when their labels are equal, else `differ`.
  ByLabel{+first: List<&2, Op>, +same: List<&2, Op>, +differ: List<&2, Op>}
  # Copying a pair: `plain`, or by plan when its head's code has one.
  ByPlan{+plain: List<&2, Op>}

# The table
# ---------

def pn(+v: String, +s: U32) -> Pt:
  PNew{v, s}

def leaf(+v: String, +k: U32) -> Op:
  New{v, WKind{k}, WLit{0}, WLit{0}}

def act(r: IC.Rule) -> Act:
  match r:
    case IC.RNone{}:
      Bendy{}
    case IC.RSetEnvNonPair{}:
      Bendy{}
    case IC.RApplyNonFunction{}:
      Bendy{}
    case IC.RNonDataGate{}:
      Bendy{}
    case IC.RNonPair{}:
      Bendy{}
    case IC.RSplitNonPair{}:
      Bendy{}
    case IC.ROpen{}:
      Plain{[Spend{}, DelM{}, leaf("v", IC.pair()), Part{"cl", 0}, Part{"cr", 1},
             Wire{pn("v", 1), pn("cl", 0)}, Wire{pn("v", 2), pn("cr", 0)}, Wire{pn("v", 0), PMe{}}]}
    case IC.RSetEnvPair{}:
      Plain{Spend{} <> Del2{} <> [leaf("ap", IC.apply()),
             Wire{pn("ap", 0), PJ1{}}, Wire{pn("ap", 1), PJ2{}}, Wire{pn("ap", 2), PI1{}}]}
    case IC.RPass{}:
      Plain{[Spend{}, DelN{}, Wire{PIt{}, PI1{}}]}
    case IC.RApplyRef{}:
      Plain{Spend{} <> Del2{} <> [Inst{}]}
    case IC.RAwaitGate{}:
      Plain{Spend{} <> Del2{} <> [leaf("sc", IC.scrut()), Wire{pn("sc", 0), PI1{}}, Wire{pn("sc", 1), PI2{}}]}
    case IC.RPassApp{}:
      Plain{[Spend{}, DelN{}, leaf("e", IC.era()), Wire{pn("e", 0), PI1{}}, Wire{PIt{}, PI2{}}]}
    case IC.RSelectGate{}:
      Plain{Spend{} <> Del2{} <> [New{"sel", WKind{IC.ref()}, WLit{0}, WLit{Co.left.gate.ind()}}, Wire{pn("sel", 0), PI1{}}]}
    case IC.RScrutPair{}:
      Plain{Spend{} <> Del2{} <> [leaf("el", IC.era()), leaf("er", IC.era()),
             Wire{pn("el", 0), PJ1{}}, Wire{pn("er", 0), PJ2{}},
             New{"sel", WKind{IC.ref()}, WLit{1}, WLit{Co.right.gate.ind()}}, Wire{pn("sel", 0), PI1{}}]}
    case IC.RProjectLeft{}:
      Plain{Spend{} <> Del2{} <> [leaf("e", IC.era()), Wire{pn("e", 0), PJ2{}}, Wire{PJ1{}, PI1{}}]}
    case IC.RProjectRight{}:
      Plain{Spend{} <> Del2{} <> [leaf("e", IC.era()), Wire{pn("e", 0), PJ1{}}, Wire{PJ2{}, PI1{}}]}
    case IC.RSplitPair{}:
      Plain{Spend{} <> Del2{} <> [Wire{PJ1{}, PI1{}}, Wire{PJ2{}, PI2{}}]}
    case IC.RSplitZero{}:
      Plain{Spend{} <> Del2{} <> [leaf("c1", IC.zero()), leaf("c2", IC.zero()),
             Wire{pn("c1", 0), PI1{}}, Wire{pn("c2", 0), PI2{}}]}
    case IC.RSplitAborted{}:
      # both halves keep the origin
      Plain{Spend{} <> Del2{} <> [Fresh{"l"}, New{"dm", WKind{IC.dup()}, WVar{"l"}, WLit{0}}, Wire{pn("dm", 0), PJ1{}},
             New{"a1", WKind{IC.aborted()}, WJa{}, WLit{0}}, New{"a2", WKind{IC.aborted()}, WJa{}, WLit{0}},
             Wire{pn("a1", 1), pn("dm", 1)}, Wire{pn("a1", 0), PI1{}},
             Wire{pn("a2", 1), pn("dm", 2)}, Wire{pn("a2", 0), PI2{}}]}
    case IC.RSplitStuck{}:
      Plain{Spend{} <> Del2{} <> [New{"c1", WKind{IC.stuck()}, WJa{}, WLit{0}}, New{"c2", WKind{IC.stuck()}, WJa{}, WLit{0}},
             Wire{pn("c1", 0), PI1{}}, Wire{pn("c2", 0), PI2{}}]}
    case IC.REraPair{}:
      Plain{Spend{} <> Del2{} <> [leaf("el", IC.era()), leaf("er", IC.era()),
             Wire{pn("el", 0), PJ1{}}, Wire{pn("er", 0), PJ2{}}]}
    case IC.REraAborted{}:
      Plain{Spend{} <> Del2{} <> [leaf("e", IC.era()), Wire{pn("e", 0), PJ1{}}]}
    case IC.REraLeaf{}:
      Plain{[Spend{}, Del2{}]}
    case IC.RDupPlanned{}:
      ByPlan{Spend{} <> Del2{} <> [leaf("p1", IC.pair()), leaf("p2", IC.pair()),
             New{"dl", WKind{IC.dup()}, WIa{}, WLit{0}}, New{"dr", WKind{IC.dup()}, WIa{}, WLit{0}},
             Wire{pn("dl", 0), PJ1{}}, Wire{pn("dr", 0), PJ2{}},
             Wire{pn("p1", 1), pn("dl", 1)}, Wire{pn("p1", 2), pn("dr", 1)},
             Wire{pn("p2", 1), pn("dl", 2)}, Wire{pn("p2", 2), pn("dr", 2)},
             Wire{pn("p1", 0), PI1{}}, Wire{pn("p2", 0), PI2{}}]}
    case IC.RDupAborted{}:
      Plain{Spend{} <> Del2{} <> [New{"a1", WKind{IC.aborted()}, WJa{}, WLit{0}}, New{"a2", WKind{IC.aborted()}, WJa{}, WLit{0}},
             New{"dm", WKind{IC.dup()}, WIa{}, WLit{0}}, Spare{WKind{IC.zero()}},
             Wire{pn("dm", 0), PJ1{}}, Wire{pn("a1", 1), pn("dm", 1)}, Wire{pn("a2", 1), pn("dm", 2)},
             Wire{pn("a1", 0), PI1{}}, Wire{pn("a2", 0), PI2{}}]}
    case IC.RDupDup{}:
      ByLabel{[Spend{}, Del2{}],
        [Wire{PI1{}, PJ1{}}, Wire{PI2{}, PJ2{}}],
        [New{"m1", WKind{IC.dup()}, WJa{}, WLit{0}}, New{"m2", WKind{IC.dup()}, WJa{}, WLit{0}},
         New{"n1", WKind{IC.dup()}, WIa{}, WLit{0}}, New{"n2", WKind{IC.dup()}, WIa{}, WLit{0}},
         Wire{pn("m1", 0), PI1{}}, Wire{pn("m2", 0), PI2{}}, Wire{pn("n1", 0), PJ1{}}, Wire{pn("n2", 0), PJ2{}},
         Wire{pn("m1", 1), pn("n1", 1)}, Wire{pn("m1", 2), pn("n2", 1)},
         Wire{pn("m2", 1), pn("n1", 2)}, Wire{pn("m2", 2), pn("n2", 2)}]}
    case IC.RDupLeaf{}:
      Plain{Spend{} <> Del2{} <> [New{"c1", WJk{}, WJa{}, WJb{}}, New{"c2", WJk{}, WJa{}, WJb{}},
             Wire{pn("c1", 0), PI1{}}, Wire{pn("c2", 0), PI2{}}]}

# The table on IC.bend's net
# --------------------------

type Bind is Data:
  Bind{+v: String, +id: U32}

type Env is Data:
  Env{+n: U32, +i: IC.NI, +m: U32, +j: IC.NI, +binds: List<&2, Bind>}

def e.n(e: Env) -> U32:
  match e:
    case Env{n, i, m, j, binds}:
      n

def e.i(e: Env) -> IC.NI:
  match e:
    case Env{n, i, m, j, binds}:
      i

def e.m(e: Env) -> U32:
  match e:
    case Env{n, i, m, j, binds}:
      m

def e.j(e: Env) -> IC.NI:
  match e:
    case Env{n, i, m, j, binds}:
      j

# What a step leaves: the net, and what the rule has named so far.
type St is Type:
  St{net: IC.Net, env: Env}

def named(+v: String, bs: List<&2, Bind>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, rest}:
      match b:
        case Bind{+w, +id}:
          Bool.pick(U32, String.eq(v, w), id, named(v, rest))

def e.named(+v: String, e: Env) -> U32:
  match e:
    case Env{n, i, m, j, binds}:
      named(v, binds)

def wd(+e: Env, w: Wd) -> U32:
  match w:
    case WLit{+k}:
      k
    case WKind{+k}:
      k
    case WIa{}:
      IC.ni.a(e.i(e))
    case WJa{}:
      IC.ni.a(e.j(e))
    case WJb{}:
      IC.ni.b(e.j(e))
    case WJk{}:
      IC.ni.k(e.j(e))
    case WVar{+v}:
      e.named(v, e)

def pt(+e: Env, p: Pt) -> U32:
  match p:
    case PNew{+v, +s}:
      IC.port(e.named(v, e), s)
    case PMe{}:
      IC.port(e.n(e), 0)
    case PIt{}:
      IC.port(e.m(e), 0)
    case PI1{}:
      IC.ni.p1(e.i(e))
    case PI2{}:
      IC.ni.p2(e.i(e))
    case PJ1{}:
      IC.ni.p1(e.j(e))
    case PJ2{}:
      IC.ni.p2(e.j(e))

def e.bind(+v: String, +id: U32, e: Env) -> Env:
  match e:
    case Env{+n, +i, +m, +j, +binds}:
      Env{n, i, m, j, Con{Bind{v, id}, binds}}

def bound(+e: Env, +v: String, r: IC.Net & U32) -> St:
  (net, +id) = r
  St{net, e.bind(v, id, e)}

def spare.got(+e: Env, r: IC.Net & U32) -> St:
  (net, +id) = r
  St{net, e}

def part.got(+e: Env, +v: String, r: IC.Net & U32) -> St:
  (net, +w) = r
  bound(e, v, IC.const.node(U32.is_zero(w), net, w))

def step(+e: Env, net: IC.Net, op: Op) -> St:
  match op:
    case Spend{}:
      St{IC.spend(net), e}
    case DelN{}:
      St{IC.delete(net, e.n(e)), e}
    case DelM{}:
      St{IC.delete(net, e.m(e)), e}
    case Del2{}:
      St{IC.del2(net, e.n(e), e.m(e)), e}
    case New{+v, +k, +a, +b}:
      bound(e, v, IC.alloc(net, wd(e, k), wd(e, a), wd(e, b)))
    case Spare{+k}:
      spare.got(e, IC.alloc(net, wd(e, k), 0, 0))
    case Fresh{+v}:
      bound(e, v, IC.fresh.label(net))
    case Part{+v, +at}:
      part.got(e, v, IC.trd(net, (IC.ni.a(e.j(e)) + at : U32)))
    case Wire{+p, +q}:
      St{IC.connect(net, pt(e, p), pt(e, q)), e}
    case Inst{}:
      St{IC.instantiate(IC.unrolled(net, IC.ni.b(e.j(e))), IC.ni.a(e.j(e)), IC.ni.p1(e.i(e)), IC.ni.p2(e.i(e))), e}

def st.net(s: St) -> IC.Net:
  match s:
    case St{net, env}:
      net

def ops.run(ops: List<&2, Op>, s: St) -> St:
  match ops:
    case Nil{}:
      s
    case Con{op, rest}:
      match s:
        case St{net, +env}:
          ops.run(rest, step(env, net, op))

def by.label(same: Bool, +ys: List<&2, Op>, +ns: List<&2, Op>, s: St) -> St:
  match same:
    case True{}:
      ops.run(ys, s)
    case False{}:
      ops.run(ns, s)

def plan.pick(plain: Bool, +ops: List<&2, Op>, +env: Env, net: IC.Net, +p: U32) -> IC.Net:
  match plain:
    case True{}:
      st.net(ops.run(ops, St{net, env}))
    case False{}:
      IC.r.dup.closure(net, p, e.n(env), e.i(env), e.m(env))

def plan.got(+ops: List<&2, Op>, +env: Env, r: IC.Net & U32) -> IC.Net:
  (net, +p) = r
  plan.pick(U32.is_zero(p), ops, env, net, p)

def apply.act(a: Act, r: IC.Rule, net: IC.Net, +n: U32, +i: IC.NI, +m: U32, +j: IC.NI) -> IC.Net:
  match a:
    case Bendy{}:
      IC.apply.rule(r, net, n, i, m, j)
    case Plain{+ops}:
      st.net(ops.run(ops, St{net, Env{n, i, m, j, []}}))
    case ByLabel{+first, +same, +differ}:
      st.net(by.label(U32.is_eq(IC.ni.a(i), IC.ni.a(j)), same, differ, ops.run(first, St{net, Env{n, i, m, j, []}})))
    case ByPlan{+plain}:
      plan.got(plain, Env{n, i, m, j, []}, IC.plan.of(net, IC.ni.p1(j)))

# Rule r on n and m, by the table.
def apply(+r: IC.Rule, net: IC.Net, +n: U32, +i: IC.NI, +m: U32, +j: IC.NI) -> IC.Net:
  apply.act(act(r), r, net, n, i, m, j)

# IC.bend's fire and reduce, by the table
# ---------------------------------------

def fire.flip(r: IC.Rule, net: IC.Net, +a: U32, +ia: IC.NI, +b: U32, +ib: IC.NI) -> IC.Net:
  match r:
    case IC.RNone{}:
      IC.fire(net, a, b)
    case _:
      apply(r, net, b, ib, a, ia)

def fire.try(r: IC.Rule, net: IC.Net, +a: U32, +ia: IC.NI, +b: U32, +ib: IC.NI) -> IC.Net:
  match r:
    case IC.RNone{}:
      fire.flip(IC.rule.of(IC.ak.of(IC.ni.k(ib)), IC.ak.of(IC.ni.k(ia))), net, a, ia, b, ib)
    case _:
      apply(r, net, a, ia, b, ib)

def fire.b(+a: U32, +b: U32, +ia: IC.NI, r: IC.Net & IC.NI) -> IC.Net:
  (net, +ib) = r
  fire.try(IC.rule.of(IC.ak.of(IC.ni.k(ia)), IC.ak.of(IC.ni.k(ib))), net, a, ia, b, ib)

def fire.a(+a: U32, +b: U32, r: IC.Net & IC.NI) -> IC.Net:
  (net, +ia) = r
  fire.b(a, b, ia, IC.info(net, b))

def fire(net: IC.Net, +a: U32, +b: U32) -> IC.Net:
  fire.a(a, b, IC.info(net, a))

def reduce(fuel: Nat, st: IC.Popped) -> IC.Net:
  match fuel:
    case 0n:
      match st:
        case IC.PEmpty{net}:
          net
        case IC.PStale{net}:
          net
        case IC.PPair{net, a, b}:
          net
    case 1n+f:
      match st:
        case IC.PEmpty{net}:
          net
        case IC.PStale{net}:
          reduce(f, IC.pop(net))
        case IC.PPair{net, a, b}:
          reduce(f, IC.pop(fire(net, a, b)))

def finish(+bodies: IC.Read, r: IC.CS & U32) -> IC.Run:
  (cs, +root) = r
  IC.finish.root(bodies, root, IC.peer(reduce(U32.to_nat(4294967295), IC.pop(IC.cs.net(cs))), (root * 4 : U32)))

# IC.run, by the table: slower, and the same net word for word.
def run(p: IC.Prog, net: IC.Net, input: Co.D, +fuel: U32) -> IC.Run:
  match p:
    case IC.Prog{entry, +bodies, words, maxk, +os}:
      finish(IC.Read{bodies, os}, IC.start(entry, input)(IC.CS{IC.reset(net, fuel), Map.new(&2, List<&2, U32>)}))
