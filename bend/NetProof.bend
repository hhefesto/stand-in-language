import Base
import ./Core.bend as Co
import ./IC.bend as IC
import ./Rules.bend as Ru

# DRAFT, not approved claims (LAWS.bend is the human's): the rule table is
# IC.bend's rules, for every rule and any net, well-formed or not.
#
# A rule's steps that allocate read through a pair the net hides, so each
# allocation is a lemma that opens that pair: go(r, k, s) is rule r's steps
# from the k-th on, run from s, and each lemma says that, from the state its
# allocation leaves, the table does what IC.bend's continuation does.

def ops.of(a: Ru.Act) -> List<&2, Ru.Op>:
  match a:
    case Ru.Plain{ops}:
      ops
    case Ru.ByPlan{plain}:
      plain
    case Ru.ByLabel{first, same, differ}:
      differ
    case Ru.Bendy{}:
      []

def tail(r: IC.Rule, k: Nat) -> List<&2, Ru.Op>:
  List.drop(&2, Ru.Op, ops.of(Ru.act(r)), k)

def go(r: IC.Rule, k: Nat, s: Ru.St) -> IC.Net:
  Ru.st.net(Ru.ops.run(tail(r, k), s))

def E(+n: U32, +i: IC.NI, +m: U32, +j: IC.NI) -> Ru.Env:
  Ru.Env{n, i, m, j, []}

def B(+v: String, +x: U32, e: Ru.Env) -> Ru.Env:
  Ru.e.bind(v, x, e)

# One allocation
# --------------

law setenv_pair:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RSetEnvPair{}, 3n, Ru.bound(E(n, i, m, j), "ap", a)) == IC.r.apply.go(i, j, a) : IC.Net}

def setenv_pair(n, i, m, j, a):
  (net, +x) = a
  {==}

law await_gate:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RAwaitGate{}, 3n, Ru.bound(E(n, i, m, j), "sc", a)) == IC.r.await.go(i, a) : IC.Net}

def await_gate(n, i, m, j, a):
  (net, +x) = a
  {==}

law pass_app:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RPassApp{}, 3n, Ru.bound(E(n, i, m, j), "e", a)) == IC.r.pass.app.go(i, m, a) : IC.Net}

def pass_app(n, i, m, j, a):
  (net, +x) = a
  {==}

law select_gate:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RSelectGate{}, 3n, Ru.bound(E(n, i, m, j), "sel", a)) == IC.r.select.go(IC.ni.p1(i), a) : IC.Net}

def select_gate(n, i, m, j, a):
  (net, +x) = a
  {==}

law project_left:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RProjectLeft{}, 3n, Ru.bound(E(n, i, m, j), "e", a)) == IC.r.project.go(i, IC.ni.p1(j), IC.ni.p2(j), a) : IC.Net}

def project_left(n, i, m, j, a):
  (net, +x) = a
  {==}

law project_right:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RProjectRight{}, 3n, Ru.bound(E(n, i, m, j), "e", a)) == IC.r.project.go(i, IC.ni.p2(j), IC.ni.p1(j), a) : IC.Net}

def project_right(n, i, m, j, a):
  (net, +x) = a
  {==}

law era_aborted:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.REraAborted{}, 3n, Ru.bound(E(n, i, m, j), "e", a)) == IC.r.era.aborted.go(j, a) : IC.Net}

def era_aborted(n, i, m, j, a):
  (net, +x) = a
  {==}

# Two allocations
# ---------------

law scrut_3:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for +y: U32
  for a: IC.Net & U32
  {go(IC.RScrutPair{}, 7n, Ru.bound(B("er", y, B("el", x, E(n, i, m, j))), "sel", a)) == IC.r.select.go(IC.ni.p1(i), a) : IC.Net}

def scrut_3(n, i, m, j, x, y, a):
  (net, +s) = a
  {==}

law scrut_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RScrutPair{}, 4n, Ru.bound(B("el", x, E(n, i, m, j)), "er", a)) == IC.r.scrut.pair.go(i, j, IC.alloc2.two(x, a)) : IC.Net}

def scrut_2(n, i, m, j, x, a):
  (net, +y) = a
  scrut_3(n, i, m, j, x, y, IC.alloc(IC.connect(IC.connect(net, IC.port(x, 0), IC.ni.p1(j)), IC.port(y, 0), IC.ni.p2(j)), IC.ref(), 1, Co.right.gate.ind()))

law scrut_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RScrutPair{}, 3n, Ru.bound(E(n, i, m, j), "el", a)) == IC.r.scrut.pair.go(i, j, IC.alloc2.one(IC.era(), 0, 0, a)) : IC.Net}

def scrut_1(n, i, m, j, a):
  (net, +x) = a
  scrut_2(n, i, m, j, x, IC.alloc(net, IC.era(), 0, 0))

law split_zero_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RSplitZero{}, 4n, Ru.bound(B("c1", x, E(n, i, m, j)), "c2", a)) == IC.r.two.leaves(i, IC.alloc2.two(x, a)) : IC.Net}

def split_zero_2(n, i, m, j, x, a):
  (net, +y) = a
  {==}

law split_zero_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RSplitZero{}, 3n, Ru.bound(E(n, i, m, j), "c1", a)) == IC.r.two.leaves(i, IC.alloc2.one(IC.zero(), 0, 0, a)) : IC.Net}

def split_zero_1(n, i, m, j, a):
  (net, +x) = a
  split_zero_2(n, i, m, j, x, IC.alloc(net, IC.zero(), 0, 0))

law split_stuck_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RSplitStuck{}, 4n, Ru.bound(B("c1", x, E(n, i, m, j)), "c2", a)) == IC.r.two.leaves(i, IC.alloc2.two(x, a)) : IC.Net}

def split_stuck_2(n, i, m, j, x, a):
  (net, +y) = a
  {==}

law split_stuck_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RSplitStuck{}, 3n, Ru.bound(E(n, i, m, j), "c1", a)) == IC.r.two.leaves(i, IC.alloc2.one(IC.stuck(), IC.ni.a(j), 0, a)) : IC.Net}

def split_stuck_1(n, i, m, j, a):
  (net, +x) = a
  split_stuck_2(n, i, m, j, x, IC.alloc(net, IC.stuck(), IC.ni.a(j), 0))

law dup_leaf_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RDupLeaf{}, 4n, Ru.bound(B("c1", x, E(n, i, m, j)), "c2", a)) == IC.r.two.leaves(i, IC.alloc2.two(x, a)) : IC.Net}

def dup_leaf_2(n, i, m, j, x, a):
  (net, +y) = a
  {==}

law dup_leaf_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RDupLeaf{}, 3n, Ru.bound(E(n, i, m, j), "c1", a)) == IC.r.two.leaves(i, IC.alloc2.one(IC.ni.k(j), IC.ni.a(j), IC.ni.b(j), a)) : IC.Net}

def dup_leaf_1(n, i, m, j, a):
  (net, +x) = a
  dup_leaf_2(n, i, m, j, x, IC.alloc(net, IC.ni.k(j), IC.ni.a(j), IC.ni.b(j)))

law era_pair_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.REraPair{}, 4n, Ru.bound(B("el", x, E(n, i, m, j)), "er", a)) == IC.r.era.pair.go(j, IC.alloc2.two(x, a)) : IC.Net}

def era_pair_2(n, i, m, j, x, a):
  (net, +y) = a
  {==}

law era_pair_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.REraPair{}, 3n, Ru.bound(E(n, i, m, j), "el", a)) == IC.r.era.pair.go(j, IC.alloc2.one(IC.era(), 0, 0, a)) : IC.Net}

def era_pair_1(n, i, m, j, a):
  (net, +x) = a
  era_pair_2(n, i, m, j, x, IC.alloc(net, IC.era(), 0, 0))

# Split meets an aborted value
# ----------------------------

law split_aborted_4:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +l: U32
  for +dm: U32
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RSplitAborted{}, 7n, Ru.bound(B("a1", x, B("dm", dm, B("l", l, E(n, i, m, j)))), "a2", a)) == IC.r.split.aborted.two(i, dm, IC.alloc2.two(x, a)) : IC.Net}

def split_aborted_4(n, i, m, j, l, dm, x, a):
  (net, +y) = a
  {==}

law split_aborted_3:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +l: U32
  for +dm: U32
  for a: IC.Net & U32
  {go(IC.RSplitAborted{}, 6n, Ru.bound(B("dm", dm, B("l", l, E(n, i, m, j))), "a1", a)) == IC.r.split.aborted.two(i, dm, IC.alloc2.one(IC.aborted(), IC.ni.a(j), 0, a)) : IC.Net}

def split_aborted_3(n, i, m, j, l, dm, a):
  (net, +x) = a
  split_aborted_4(n, i, m, j, l, dm, x, IC.alloc(net, IC.aborted(), IC.ni.a(j), 0))

law split_aborted_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +l: U32
  for a: IC.Net & U32
  {go(IC.RSplitAborted{}, 4n, Ru.bound(B("l", l, E(n, i, m, j)), "dm", a)) == IC.r.split.aborted.one(i, j, a) : IC.Net}

def split_aborted_2(n, i, m, j, l, a):
  (net, +dm) = a
  split_aborted_3(n, i, m, j, l, dm, IC.alloc(IC.connect(net, IC.port(dm, 0), IC.ni.p1(j)), IC.aborted(), IC.ni.a(j), 0))

law split_aborted_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RSplitAborted{}, 3n, Ru.bound(E(n, i, m, j), "l", a)) == IC.r.split.aborted.label(i, j, a) : IC.Net}

def split_aborted_1(n, i, m, j, a):
  (net, +l) = a
  split_aborted_2(n, i, m, j, l, IC.alloc(net, IC.dup(), l, 0))

# Four allocations
# ----------------

law dup_aborted_4:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for +y: U32
  for +z: U32
  for a: IC.Net & U32
  {go(IC.RDupAborted{}, 6n, Ru.spare.got(B("dm", z, B("a2", y, B("a1", x, E(n, i, m, j)))), a)) == IC.r.dup.aborted.go(i, j, IC.alloc4.two(x, y, IC.alloc2.two(z, a))) : IC.Net}

def dup_aborted_4(n, i, m, j, x, y, z, a):
  (net, +w) = a
  {==}

law dup_aborted_3:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for +y: U32
  for a: IC.Net & U32
  {go(IC.RDupAborted{}, 5n, Ru.bound(B("a2", y, B("a1", x, E(n, i, m, j))), "dm", a)) == IC.r.dup.aborted.go(i, j, IC.alloc4.two(x, y, IC.alloc2.one(IC.zero(), 0, 0, a))) : IC.Net}

def dup_aborted_3(n, i, m, j, x, y, a):
  (net, +z) = a
  dup_aborted_4(n, i, m, j, x, y, z, IC.alloc(net, IC.zero(), 0, 0))

law dup_aborted_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RDupAborted{}, 4n, Ru.bound(B("a1", x, E(n, i, m, j)), "a2", a)) == IC.r.dup.aborted.go(i, j, IC.alloc4.one(IC.dup(), IC.ni.a(i), IC.zero(), 0, IC.alloc2.two(x, a))) : IC.Net}

def dup_aborted_2(n, i, m, j, x, a):
  (net, +y) = a
  dup_aborted_3(n, i, m, j, x, y, IC.alloc(net, IC.dup(), IC.ni.a(i), 0))

law dup_aborted_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RDupAborted{}, 3n, Ru.bound(E(n, i, m, j), "a1", a)) == IC.r.dup.aborted.go(i, j, IC.alloc4.one(IC.dup(), IC.ni.a(i), IC.zero(), 0, IC.alloc2.one(IC.aborted(), IC.ni.a(j), 0, a))) : IC.Net}

def dup_aborted_1(n, i, m, j, a):
  (net, +x) = a
  dup_aborted_2(n, i, m, j, x, IC.alloc(net, IC.aborted(), IC.ni.a(j), 0))

law dup_pair_4:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for +y: U32
  for +z: U32
  for a: IC.Net & U32
  {go(IC.RDupPlanned{}, 6n, Ru.bound(B("dl", z, B("p2", y, B("p1", x, E(n, i, m, j)))), "dr", a)) == IC.r.dup.pair.go(i, j, IC.alloc4.two(x, y, IC.alloc2.two(z, a))) : IC.Net}

def dup_pair_4(n, i, m, j, x, y, z, a):
  (net, +w) = a
  {==}

law dup_pair_3:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for +y: U32
  for a: IC.Net & U32
  {go(IC.RDupPlanned{}, 5n, Ru.bound(B("p2", y, B("p1", x, E(n, i, m, j))), "dl", a)) == IC.r.dup.pair.go(i, j, IC.alloc4.two(x, y, IC.alloc2.one(IC.dup(), IC.ni.a(i), 0, a))) : IC.Net}

def dup_pair_3(n, i, m, j, x, y, a):
  (net, +z) = a
  dup_pair_4(n, i, m, j, x, y, z, IC.alloc(net, IC.dup(), IC.ni.a(i), 0))

law dup_pair_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RDupPlanned{}, 4n, Ru.bound(B("p1", x, E(n, i, m, j)), "p2", a)) == IC.r.dup.pair.go(i, j, IC.alloc4.one(IC.dup(), IC.ni.a(i), IC.dup(), IC.ni.a(i), IC.alloc2.two(x, a))) : IC.Net}

def dup_pair_2(n, i, m, j, x, a):
  (net, +y) = a
  dup_pair_3(n, i, m, j, x, y, IC.alloc(net, IC.dup(), IC.ni.a(i), 0))

law dup_pair_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RDupPlanned{}, 3n, Ru.bound(E(n, i, m, j), "p1", a)) == IC.r.dup.pair.go(i, j, IC.alloc4.one(IC.dup(), IC.ni.a(i), IC.dup(), IC.ni.a(i), IC.alloc2.one(IC.pair(), 0, 0, a))) : IC.Net}

def dup_pair_1(n, i, m, j, a):
  (net, +x) = a
  dup_pair_2(n, i, m, j, x, IC.alloc(net, IC.pair(), 0, 0))

law dup_commute_4:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for +y: U32
  for +z: U32
  for a: IC.Net & U32
  {go(IC.RDupDup{}, 4n, Ru.bound(B("n1", z, B("m2", y, B("m1", x, E(n, i, m, j)))), "n2", a)) == IC.r.dup.commute.go(i, j, IC.alloc4.two(x, y, IC.alloc2.two(z, a))) : IC.Net}

def dup_commute_4(n, i, m, j, x, y, z, a):
  (net, +w) = a
  {==}

law dup_commute_3:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for +y: U32
  for a: IC.Net & U32
  {go(IC.RDupDup{}, 3n, Ru.bound(B("m2", y, B("m1", x, E(n, i, m, j))), "n1", a)) == IC.r.dup.commute.go(i, j, IC.alloc4.two(x, y, IC.alloc2.one(IC.dup(), IC.ni.a(i), 0, a))) : IC.Net}

def dup_commute_3(n, i, m, j, x, y, a):
  (net, +z) = a
  dup_commute_4(n, i, m, j, x, y, z, IC.alloc(net, IC.dup(), IC.ni.a(i), 0))

law dup_commute_2:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +x: U32
  for a: IC.Net & U32
  {go(IC.RDupDup{}, 2n, Ru.bound(B("m1", x, E(n, i, m, j)), "m2", a)) == IC.r.dup.commute.go(i, j, IC.alloc4.one(IC.dup(), IC.ni.a(i), IC.dup(), IC.ni.a(i), IC.alloc2.two(x, a))) : IC.Net}

def dup_commute_2(n, i, m, j, x, a):
  (net, +y) = a
  dup_commute_3(n, i, m, j, x, y, IC.alloc(net, IC.dup(), IC.ni.a(i), 0))

law dup_commute_1:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.RDupDup{}, 1n, Ru.bound(E(n, i, m, j), "m1", a)) == IC.r.dup.commute.go(i, j, IC.alloc4.one(IC.dup(), IC.ni.a(i), IC.dup(), IC.ni.a(i), IC.alloc2.one(IC.dup(), IC.ni.a(j), 0, a))) : IC.Net}

def dup_commute_1(n, i, m, j, a):
  (net, +x) = a
  dup_commute_2(n, i, m, j, x, IC.alloc(net, IC.dup(), IC.ni.a(j), 0))

# Rules that choose
# -----------------

law dup_dup:
  for same: Bool
  for net: IC.Net
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  {Ru.st.net(Ru.by.label(same, [Ru.Wire{Ru.PI1{}, Ru.PJ1{}}, Ru.Wire{Ru.PI2{}, Ru.PJ2{}}], ops.of(Ru.act(IC.RDupDup{})), Ru.St{IC.del2(IC.spend(net), n, m), E(n, i, m, j)})) == IC.r.dup.dup(net, n, i, m, j, same) : IC.Net}

def dup_dup(same, net, n, i, m, j):
  match same:
    case True{}:
      {==}
    case False{}:
      dup_commute_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.dup(), IC.ni.a(j), 0))

law plan_pick:
  for plain: Bool
  for net: IC.Net
  for +s: U32
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  {Ru.plan.pick(plain, ops.of(Ru.act(IC.RDupPlanned{})), n, i, m, j, net, s) == IC.r.dup.pick(plain, net, s, n, i, m, j) : IC.Net}

def plan_pick(plain, net, s, n, i, m, j):
  match plain:
    case True{}:
      dup_pair_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.pair(), 0, 0))
    case False{}:
      {==}

law plan_got:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {Ru.plan.got(ops.of(Ru.act(IC.RDupPlanned{})), n, i, m, j, a) == IC.r.dup.planned.got(n, i, m, j, a) : IC.Net}

def plan_got(n, i, m, j, a):
  (net, +s) = a
  plan_pick(U32.is_zero(s), net, s, n, i, m, j)

# A constant opens
# ----------------

law open_wire:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +v: U32
  for +cl: U32
  for a: IC.Net & U32
  {go(IC.ROpen{}, 4n, Ru.bound(B("cl", cl, B("v", v, E(n, i, m, j))), "cr", a)) == IC.open.wire(n, v, cl, a) : IC.Net}

def open_wire(n, i, m, j, v, cl, a):
  (net, +cr) = a
  {==}

law open_parts:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +v: U32
  for +wr: U32
  for a: IC.Net & U32
  {go(IC.ROpen{}, 4n, Ru.part("cr", wr, Ru.bound(B("v", v, E(n, i, m, j)), "cl", a))) == IC.open.parts(n, v, wr, a) : IC.Net}

def open_parts(n, i, m, j, v, wr, a):
  (net, +cl) = a
  open_wire(n, i, m, j, v, cl, IC.const.node(U32.is_zero(wr), net, wr))

law open_right:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +v: U32
  for +wl: U32
  for a: IC.Net & U32
  {go(IC.ROpen{}, 4n, Ru.parts.right(B("v", v, E(n, i, m, j)), "cl", "cr", wl, a)) == IC.open.right(n, v, wl, a) : IC.Net}

def open_right(n, i, m, j, v, wl, a):
  (net, +wr) = a
  open_parts(n, i, m, j, v, wr, IC.const.node(U32.is_zero(wl), net, wl))

law open_left:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for +v: U32
  for a: IC.Net & U32
  {go(IC.ROpen{}, 4n, Ru.parts.left(B("v", v, E(n, i, m, j)), "cl", "cr", a)) == IC.open.left(n, v, IC.ni.a(j), a) : IC.Net}

def open_left(n, i, m, j, v, a):
  (net, +wl) = a
  open_right(n, i, m, j, v, wl, IC.trd(net, (IC.ni.a(j) + 1 : U32)))

law open_pair:
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  for a: IC.Net & U32
  {go(IC.ROpen{}, 3n, Ru.bound(E(n, i, m, j), "v", a)) == IC.open.pair(n, IC.ni.a(j), a) : IC.Net}

def open_pair(n, i, m, j, a):
  (net, +v) = a
  open_left(n, i, m, j, v, IC.trd(net, IC.ni.a(j)))

# The table
# ---------

law table_is_rules:
  for r: IC.Rule
  for net: IC.Net
  for +n: U32
  for +i: IC.NI
  for +m: U32
  for +j: IC.NI
  {Ru.apply(r, net, n, i, m, j) == IC.apply.rule(r, net, n, i, m, j) : IC.Net}

def table_is_rules(r, net, n, i, m, j):
  match r:
    case IC.RNone{}:
      {==}
    case IC.RSetEnvNonPair{}:
      {==}
    case IC.RApplyNonFunction{}:
      {==}
    case IC.RNonDataGate{}:
      {==}
    case IC.RNonPair{}:
      {==}
    case IC.RSplitNonPair{}:
      {==}
    case IC.RPass{}:
      {==}
    case IC.RApplyRef{}:
      {==}
    case IC.RSplitPair{}:
      {==}
    case IC.REraLeaf{}:
      {==}
    case IC.RSetEnvPair{}:
      setenv_pair(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.apply(), 0, 0))
    case IC.RAwaitGate{}:
      await_gate(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.scrut(), 0, 0))
    case IC.RPassApp{}:
      pass_app(n, i, m, j, IC.alloc(IC.delete(IC.spend(net), n), IC.era(), 0, 0))
    case IC.RSelectGate{}:
      select_gate(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.ref(), 0, Co.left.gate.ind()))
    case IC.RScrutPair{}:
      scrut_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.era(), 0, 0))
    case IC.RProjectLeft{}:
      project_left(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.era(), 0, 0))
    case IC.RProjectRight{}:
      project_right(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.era(), 0, 0))
    case IC.RSplitZero{}:
      split_zero_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.zero(), 0, 0))
    case IC.RSplitAborted{}:
      split_aborted_1(n, i, m, j, IC.fresh.label(IC.del2(IC.spend(net), n, m)))
    case IC.RSplitStuck{}:
      split_stuck_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.stuck(), IC.ni.a(j), 0))
    case IC.REraPair{}:
      era_pair_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.era(), 0, 0))
    case IC.REraAborted{}:
      era_aborted(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.era(), 0, 0))
    case IC.RDupPlanned{}:
      plan_got(n, i, m, j, IC.plan.of(net, IC.ni.p1(j)))
    case IC.RDupAborted{}:
      dup_aborted_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.aborted(), IC.ni.a(j), 0))
    case IC.RDupDup{}:
      dup_dup(U32.is_eq(IC.ni.a(i), IC.ni.a(j)), net, n, i, m, j)
    case IC.RDupLeaf{}:
      dup_leaf_1(n, i, m, j, IC.alloc(IC.del2(IC.spend(net), n, m), IC.ni.k(j), IC.ni.a(j), IC.ni.b(j)))
    case IC.ROpen{}:
      open_pair(n, i, m, j, IC.alloc(IC.delete(IC.spend(net), m), IC.pair(), 0, 0))

# Wire directions
# ---------------
#
# Every port takes a value in or gives one out, and a wire should join an
# output to an input. Two Dups can then never meet: both their principal
# ports are inputs, so no directed wire joins them, and RDupDup never fires.
# The table's wires keep this: the law computes it for every pair of kinds
# that can meet on a directed wire. A wire to a neighbour (PI1 and so on) is
# the opposite way to the port it replaces.
#
# Not covered here: the stuck rules (Bendy, not in the table), instantiation
# (a template's wires) and guided copying (`region`).

type Dir is Data:
  DIn{}
  DOut{}
  DNo{}

def dir3(+s: U32, a0: Dir, a1: Dir, a2: Dir) -> Dir:
  Bool.pick(Dir, U32.is_eq(s, 0), a0, Bool.pick(Dir, U32.is_eq(s, 1), a1, Bool.pick(Dir, U32.is_eq(s, 2), a2, DNo{})))

def dir(k: IC.AK, +s: U32) -> Dir:
  match k:
    case IC.KNone{}:
      DNo{}
    case IC.KEra{}:
      dir3(s, DIn{}, DNo{}, DNo{})
    case IC.KZero{}:
      dir3(s, DOut{}, DNo{}, DNo{})
    case IC.KGate{}:
      dir3(s, DOut{}, DNo{}, DNo{})
    case IC.KConst{}:
      dir3(s, DOut{}, DNo{}, DNo{})
    case IC.KRef{}:
      dir3(s, DOut{}, DNo{}, DNo{})
    case IC.KStuck{}:
      dir3(s, DOut{}, DNo{}, DNo{})
    case IC.KPair{}:
      dir3(s, DOut{}, DIn{}, DIn{})
    case IC.KAborted{}:
      dir3(s, DOut{}, DIn{}, DNo{})
    case IC.KDup{}:
      dir3(s, DIn{}, DOut{}, DOut{})
    case IC.KSplit{}:
      dir3(s, DIn{}, DOut{}, DOut{})
    case IC.KSetEnv{}:
      dir3(s, DIn{}, DOut{}, DNo{})
    case IC.KLeft{}:
      dir3(s, DIn{}, DOut{}, DNo{})
    case IC.KRight{}:
      dir3(s, DIn{}, DOut{}, DNo{})
    case IC.KScrut{}:
      dir3(s, DIn{}, DOut{}, DNo{})
    case IC.KApply{}:
      dir3(s, DIn{}, DIn{}, DOut{})

def flip(d: Dir) -> Dir:
  match d:
    case DIn{}:
      DOut{}
    case DOut{}:
      DIn{}
    case DNo{}:
      DNo{}

def joined(a: Dir, b: Dir) -> Bool:
  match a:
    case DIn{}:
      match b:
        case DOut{}:
          True{}
        case _:
          False{}
    case DOut{}:
      match b:
        case DIn{}:
          True{}
        case _:
          False{}
    case DNo{}:
      False{}

type VK is Data:
  VK{+v: String, +k: IC.AK}

def kind.named(+v: String, vs: List<&2, VK>) -> IC.AK:
  match vs:
    case Nil{}:
      IC.KNone{}
    case Con{x, rest}:
      match x:
        case VK{+w, +k}:
          Bool.pick(IC.AK, String.eq(v, w), k, kind.named(v, rest))

def wd.kind(w: Ru.Wd, +kb: IC.AK) -> IC.AK:
  match w:
    case Ru.WKind{+k}:
      IC.ak.of(k)
    case Ru.WJk{}:
      kb
    case _:
      IC.KNone{}

def pt.dir(p: Ru.Pt, +ka: IC.AK, +kb: IC.AK, +vs: List<&2, VK>) -> Dir:
  match p:
    case Ru.PNew{+v, +s}:
      dir(kind.named(v, vs), s)
    case Ru.PMe{}:
      dir(ka, 0)
    case Ru.PIt{}:
      dir(kb, 0)
    case Ru.PI1{}:
      flip(dir(ka, 1))
    case Ru.PI2{}:
      flip(dir(ka, 2))
    case Ru.PJ1{}:
      flip(dir(kb, 1))
    case Ru.PJ2{}:
      flip(dir(kb, 2))

def ops.ok(ops: List<&2, Ru.Op>, +ka: IC.AK, +kb: IC.AK, +vs: List<&2, VK>) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case Con{op, rest}:
      match op:
        case Ru.Wire{+p, +q}:
          joined(pt.dir(p, ka, kb, vs), pt.dir(q, ka, kb, vs)) && ops.ok(rest, ka, kb, vs)
        case Ru.New{+v, +k, +a, +b}:
          ops.ok(rest, ka, kb, Con{VK{v, wd.kind(k, kb)}, vs})
        case Ru.Parts{+l, +r}:
          ops.ok(rest, ka, kb, Con{VK{r, IC.KConst{}}, Con{VK{l, IC.KConst{}}, vs}})
        case _:
          ops.ok(rest, ka, kb, vs)

def act.ok(a: Ru.Act, +ka: IC.AK, +kb: IC.AK) -> Bool:
  match a:
    case Ru.Bendy{}:
      True{}
    case Ru.Plain{+ops}:
      ops.ok(ops, ka, kb, [])
    case Ru.ByLabel{+first, +same, +differ}:
      ops.ok(first, ka, kb, []) && ops.ok(same, ka, kb, []) && ops.ok(differ, ka, kb, [])
    case Ru.ByPlan{+plain}:
      ops.ok(plain, ka, kb, [])

def is.dir(a: Dir, b: Dir) -> Bool:
  match a:
    case DIn{}:
      match b:
        case DIn{}:
          True{}
        case _:
          False{}
    case DOut{}:
      match b:
        case DOut{}:
          True{}
        case _:
          False{}
    case DNo{}:
      False{}

def is.none(r: IC.Rule) -> Bool:
  match r:
    case IC.RNone{}:
      True{}
    case _:
      False{}

def is.dupdup(r: IC.Rule) -> Bool:
  match r:
    case IC.RDupDup{}:
      True{}
    case _:
      False{}

# Whether ka and kb can meet on a directed wire, ka taking in and kb giving
# out.
def meets(+ka: IC.AK, +kb: IC.AK) -> Bool:
  is.dir(dir(ka, 0), DIn{}) && is.dir(dir(kb, 0), DOut{})

# A pair the rules fire is directed, unless it is two Dups; every directed
# pair's rule keeps the wires directed; and two Dups are not directed.
def pair.ok(+ka: IC.AK, +kb: IC.AK) -> Bool:
  Bool.pick(Bool, meets(ka, kb),
    act.ok(Ru.act(IC.rule.of(ka, kb)), ka, kb) && Bool.not(is.dupdup(IC.rule.of(ka, kb))),
    is.none(IC.rule.of(ka, kb)) || is.dupdup(IC.rule.of(ka, kb)))

def kinds() -> List<&2, IC.AK>:
  [IC.KNone{}, IC.KEra{}, IC.KZero{}, IC.KGate{}, IC.KConst{}, IC.KRef{}, IC.KPair{}, IC.KAborted{},
   IC.KDup{}, IC.KSplit{}, IC.KSetEnv{}, IC.KApply{}, IC.KScrut{}, IC.KLeft{}, IC.KRight{}, IC.KStuck{}]

def row.ok(+ka: IC.AK, kbs: List<&2, IC.AK>) -> Bool:
  match kbs:
    case Nil{}:
      True{}
    case Con{+kb, rest}:
      pair.ok(ka, kb) && row.ok(ka, rest)

def table.ok(kas: List<&2, IC.AK>) -> Bool:
  match kas:
    case Nil{}:
      True{}
    case Con{+ka, rest}:
      row.ok(ka, kinds()) && table.ok(rest)

law wires_directed:
  {table.ok(kinds()) == True{} : Bool}

def wires_directed():
  {==}

law dups_never_meet:
  {meets(IC.KDup{}, IC.KDup{}) == False{} : Bool}

def dups_never_meet():
  {==}
