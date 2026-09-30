import Base
import ./Show.bend as Sh
import ./Loc.bend as Lc
import ./Expr.bend as E
import ./Lift.bend as Lf

# Elementary Affine Logic certification (haskell-final's Telomare.EAL):
# box levels for a defer-lifted program, as linear constraints over the
# naturals. `certify` is the compile gate on the pre-sizing term;
# `layouts` gives the IC the capture shapes of the sized term's closures.
#
# The Haskell is followed step for step, because variable numbers, union
# roots and dispatch order decide tie-breaks and which error comes first:
# - A code body is derived afresh at each dispatch. The Haskell copies a
#   template of the first derivation instead, which it documents as the
#   same constraints; the one visible difference, its variable-budget test
#   before copying, is kept (`sizes`).
# - The unifier is one worklist, popped last in first, so its effects come
#   in the Haskell's depth-first order.
# - Tags are strings that sort as the Haskell's Ord Tag does: a code is
#   "0" and its hash; then "1" gate, "2" gate function, "3" abort, "4"
#   abort continuation.

# Types and constraints
# ---------------------

# A type skeleton: data, a variable, a pair (each side with its bang), a
# code class (a set of tags), or a capture selection of a closure package.

type Tau is Data:
  DataT{}
  VarT{+i: U32}
  PairT{+b1: U32, +t1: Tau, +b2: U32, +t2: Tau}
  CodeT{+i: U32}
  CapT{+i: U32}

# A bang variable in front of a type (Sigma).
type Sig is Data:
  Sig{+b: U32, +t: Tau}

type Blame is Data:
  Blame{+loc: Lc.Loc, +why: String}

type Class is Data:
  Unrestricted{}
  ForcedZero{+blame: Blame}
  ForcedLevel{+n: U32, +blame: Blame}

type Err is Data:
  TypeMismatch{+loc: Lc.Loc, +msg: String}
  BoxConflict{+need: Blame, +forbid: Blame}
  GaveUp{+msg: String}
  DependencyFailed{+h: String}
  Internal{+msg: String}

type SumEq is Data:
  SumEq{+lhs: List<&2, U32>, +rhs: U32, +blame: Blame}

# A tag of a code class, with the capture that rides with it in a package.
type TE is Data:
  TE{+tag: String, +cap: Maybe<&2, Sig>}

# An application, dispatched once its function position resolves to code
# (ApplySite); `done` are the tags already dispatched there.
type Site is Data:
  Site{+fn: Tau, +env: Sig, +res: Sig, +glob: List<&2, U32>, +depth: U32, +loc: Lc.Loc, +done: List<&2, String>}

# What a variable knows: its type binding, its bang class's union-find
# parent and constraint, and its tag class's parent and tags.
type V is Data:
  V{+bind: Maybe<&2, Tau>, +parent: U32, +cls: Class, +tparent: U32, +tags: List<&2, TE>}

# The state: the variables (a table that doubles), the apply sites, and
# the rest: the next variable and the tables' sizes, the sum equations
# newest first, leaf box paths, and per body its derivation count and the
# variables its first derivation minted.
type St is Type:
  St{vars: Array<V>, sites: Array<Site>, c: C}

type C is Data:
  C{+next: U32, +cap: U32, +nsites: U32, +scap: U32, +eqs: List<&2, SumEq>,
    +leaves: List<&2, List<&2, U32>>, +insts: Map<&2, U32>, +sizes: Map<&2, U32>}

type Mg is Data:
  MgOk{+c: Class, +changed: Bool}
  MgErr{+e: Err}

type SP is Data:
  SP{+a: Sig, +b: Sig}

type WK is Data:
  WkTau{+t: Tau}
  WkBound{+i: U32, +b: Maybe<&2, Tau>}

type OJ is Data:
  OTodo{+ts: List<&2, Tau>}
  OSeen{+t: Tau, +ts: List<&2, Tau>}

# A step of deepShowTau: a type to show at depth d (stop when d is 0), or
# its walk.
type DS is Data:
  DsTau{+t: Tau, +d: U32, +stop: Bool}
  DsWalked{+w: Tau, +d: U32}

# Work for the unifier, all at a visited set of capture classes and a
# dispatch mode (the dispatching tag, or "").
type W is Data:
  WSig{+vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, +a: Sig, +b: Sig}
  WTau{+vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, +a: Tau, +b: Tau}
  WColl{+vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, +s: Sig}

# Uses of one env path: how many, and where the first was.
type Use is Data:
  Use{+n: U32, +loc: Lc.Loc}

type Dup is Data:
  Dup{+path: String, +loc: Lc.Loc}

# A frame: its env domain bang and type, and its dispatch depth.
type Ctx is Data:
  Ctx{+bang: U32, +tau: Tau, +depth: U32}

# Box paths, innermost first: this frame's and the whole program's.
type Paths is Data:
  Paths{+here: List<&2, U32>, +glob: List<&2, U32>}

type FT is Data:
  FtClass{+vis: List<&2, U32>, +i: U32}
  FtCap{+vis: List<&2, U32>, +cap: Maybe<&2, Sig>}
  FtWalked{+vis: List<&2, U32>, +w: Tau}

# A derivation of a code body: its env domain bang and type, and its result.
type Der is Data:
  Der{+b: U32, +t: Tau, +s: Sig}

# The solver's class table (by root) and whether a round changed it; or
# the first failure.
type PR is Type:
  PGo{cls: Array<Class>, changed: Bool}
  PErr{e: Err}

# The assignment: each root's value, whether it is forced to zero, and how
# often it is a summand, with whether a round changed a value; or the
# failure.
type AR is Type:
  AGo{vals: Array<U32>, zf: Array<U32>, cnt: Array<U32>, changed: Bool}
  AErr{e: Err}

# The assignment's start: the classes, and the values and zero flags read
# off them.
type AI is Type:
  AI{cls: Array<Class>, vals: Array<U32>, zf: Array<U32>}

# The summand picked so far and how many equations it is in.
type Pk is Data:
  Pk{+best: U32, +bc: U32}

type SJ is Data:
  SjTau{+t: Tau}
  SjWalked{+w: Tau}

# Which bodies certify so far, and the first dependency found failing.
type DR is Data:
  DR{+memo: Map<&2, Bool>, +failed: Maybe<&2, String>}

# A step of withDeps over the body DAG: make sure a body is known, check a
# list of dependencies in order, and what came of each.
type DJ is Data:
  DjEnsure{+h: String, +known: Bool, +memo: Map<&2, Bool>}
  DjChecked{+h: String, +r: DR}
  DjCheck{+hs: List<&2, String>, +memo: Map<&2, Bool>}
  DjAfter{+h: String, +rest: List<&2, String>, +r: DR}
  DjNext{+ok: Bool, +h: String, +rest: List<&2, String>, +memo: Map<&2, Bool>}
  DjAll{+hs: List<&2, String>, +memo: Map<&2, Bool>}
  DjAllNext{+hs: List<&2, String>, +r: DR}

# A step of find on the table: a variable's record read, or its parent
# seen.
type RJ is Type:
  RjRead{i: U32, r: Array<V> & V}
  RjUp{i: U32, p: U32, top: Bool, a: Array<V>}
  RjFix{i: U32, x: V, p: U32, done: Bool, a: Array<V>}

type HB is Data:
  HB{+h: String, +ok: Bool}

def ds(t: Tau, +d: U32) -> DS:
  DsTau{t, d, U32.is_eq(d, 0)}

def none() -> U32:
  4294967295

def level.cap() -> U32:
  4096

def depth.cap() -> U32:
  1024

def var.budget() -> U32:
  2000000

def poly.cap() -> U32:
  16384

def v.empty() -> V:
  V{None{}, none(), Unrestricted{}, none(), []}

def site.empty() -> Site:
  Site{DataT{}, Sig{0, DataT{}}, Sig{0, DataT{}}, [], 0, Lc.Unknown{}, []}

def st.new() -> St:
  St{Array.new(V, 10n, v.empty()), Array.new(Site, 8n, site.empty()),
     C{0, 1024, 0, 256, [], [], Map.new(&2, U32), Map.new(&2, U32)}}

# Showing, for messages
# ---------------------

def blame.show(b: Blame) -> String:
  match b:
    case Blame{loc, why}:
      "Blame " ++ Lf.loc.show(loc, True{}) ++ " " ++ Sh.string(why)

def tag.show(t: String) -> String:
  match t:
    case SCon{Chr{48}, h}:
      "TCode " ++ h
    case SCon{Chr{49}, r}:
      "TGate"
    case SCon{Chr{50}, r}:
      "TGateFn"
    case SCon{Chr{51}, r}:
      "TAbort"
    case _:
      "TAbortCont"

def tags.show.go(ts: List<&2, String>) -> String:
  match ts:
    case Nil{}:
      "]"
    case Con{t, rest}:
      "," ++ tag.show(t) ++ tags.show.go(rest)

def tags.show(ts: List<&2, String>) -> String:
  match ts:
    case Nil{}:
      "[]"
    case Con{t, rest}:
      "[" ++ tag.show(t) ++ tags.show.go(rest)

def mode.show(m: String) -> String:
  match m:
    case SNil{}:
      "Nothing"
    case SCon{Chr{48}, h}:
      "Just (TCode " ++ h ++ ")"
    case other:
      "Just " ++ tag.show(other)

def describe(t: Tau) -> String:
  match t:
    case DataT{}:
      "data"
    case VarT{i}:
      "t" ++ U32.show(i)
    case PairT{b1, t1, b2, t2}:
      "pair"
    case CodeT{i}:
      "code"
    case CapT{i}:
      "capture"

def steps.show(p: String) -> String:
  match p:
    case SNil{}:
      "<whole env>"
    case other:
      other

def render.at(m: Maybe<&2, String>) -> String:
  match m:
    case Some{place}:
      " (at " ++ place ++ ")"
    case None{}:
      ""

def blame.render(b: Blame) -> String:
  match b:
    case Blame{loc, why}:
      why ++ render.at(Lc.render_compact(loc))

# The monad
# ---------

# renderEALError
def render(e: Err) -> String:
  match e:
    case TypeMismatch{loc, msg}:
      "certification failed: " ++ msg ++ render.at(Lc.render_compact(loc))
    case BoxConflict{need, forbid}:
      "certification failed: a duplicated value cannot be boxed:\n  boxing required: "
        ++ blame.render(need) ++ "\n  boxing forbidden: " ++ blame.render(forbid)
    case GaveUp{msg}:
      "certification gave up; this usually means unbounded self-application:\n  " ++ msg
    case DependencyFailed{h}:
      "a function body this program depends on failed certification: " ++ h
    case Internal{msg}:
      "certification internal error (analyzer bug): " ++ msg

def M(-A: Data) -> Type:
  St -> Result<&1, &1, Err, A & St>

def M.pure(-A: Data, x: A) -> M(A):
  s => Done{(x, s)}

def M.fail(-A: Data, e: Err) -> M(A):
  s => Fail{e}

def M.run(-A: Data, -B: Data, f: A -> M(B), r: Result<&1, &1, Err, A & St>) -> Result<&1, &1, Err, B & St>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{p}:
      (a, s) = p
      f(a)(s)

def M.bind(-A: Data, -B: Data, m: M(A), f: A -> M(B)) -> M(B):
  s => M.run(A, B, f, m(s))

# The counters and lists
# ----------------------

def c.next(c: C) -> U32:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      next

def c.nsites(c: C) -> U32:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      nsites

def c.eqs(c: C) -> List<&2, SumEq>:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      eqs

def c.leaves(c: C) -> List<&2, List<&2, U32>>:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      leaves

def c.inst(c: C, +h: String) -> U32:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      Pair.snd(Map<&2, U32>, U32, Map.get(U32, 0, insts, h))

def c.size(c: C, +h: String) -> U32:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      Pair.snd(Map<&2, U32>, U32, Map.get(U32, 0, sizes, h))

def c.with.eq(c: C, e: SumEq) -> C:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      C{next, cap, nsites, scap, e <> eqs, leaves, insts, sizes}

def c.with.leaf(c: C, p: List<&2, U32>) -> C:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      C{next, cap, nsites, scap, eqs, p <> leaves, insts, sizes}

def c.with.inst(c: C, +h: String, +n: U32) -> C:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      C{next, cap, nsites, scap, eqs, leaves, Map.set(&2, U32, insts, h, n), sizes}

def c.with.size(c: C, +h: String, +n: U32) -> C:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      C{next, cap, nsites, scap, eqs, leaves, insts, Map.set(&2, U32, sizes, h, n)}

def with.c.go(-A: Data, f: C -> A, s: St) -> Result<&1, &1, Err, A & St>:
  match s:
    case St{vars, sites, +c}:
      Done{(f(c), St{vars, sites, c})}

# A read of the rest.
def with.c(-A: Data, f: C -> A) -> M(A):
  s => with.c.go(A, f, s)

def on.c.go(f: C -> C, s: St) -> Result<&1, &1, Err, Unit & St>:
  match s:
    case St{vars, sites, c}:
      Done{(Unit{}, St{vars, sites, f(c)})}

# Variables
# ---------

# A change to the rest.
def on.c(f: C -> C) -> M(Unit):
  s => on.c.go(f, s)

def grow.vars(+cap: U32, vars: Array<V>) -> Array<V>:
  ANode{vars, Array.new(V, U32.log2(cap), v.empty())}

def fresh.room(room: Bool, vars: Array<V>, sites: Array<Site>, c: C) -> Result<&1, &1, Err, U32 & St>:
  match room:
    case True{}:
      match c:
        case C{+next, cap, nsites, scap, eqs, leaves, insts, sizes}:
          Done{(next, St{vars, sites, C{(next + 1 : U32), cap, nsites, scap, eqs, leaves, insts, sizes}})}
    case False{}:
      match c:
        case C{+next, +cap, nsites, scap, eqs, leaves, insts, sizes}:
          Done{(next, St{grow.vars(cap, vars), sites, C{(next + 1 : U32), (cap * 2 : U32), nsites, scap, eqs, leaves, insts, sizes}})}

def c.room(c: C) -> Bool:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      U32.is_lt(next, cap)

def fresh.at(over: Bool, s: St) -> Result<&1, &1, Err, U32 & St>:
  match over:
    case True{}:
      Fail{GaveUp{"constraint variable budget (2000000) exceeded; the dispatch structure is likely exploding"}}
    case False{}:
      match s:
        case St{vars, sites, +c}:
          fresh.room(c.room(c), vars, sites, c)

def fresh.go(s: St) -> Result<&1, &1, Err, U32 & St>:
  match s:
    case St{vars, sites, +c}:
      fresh.at(U32.is_ge(c.next(c), var.budget()), St{vars, sites, c})

# freshInt
def fresh() -> M(U32):
  s => fresh.go(s)

def fresh.tau() -> M(Tau):
  do M<Tau>:
    i : U32 <- fresh()
    return VarT{i}

def fresh.sig() -> M(Sig):
  do M<Sig>:
    b : U32 <- fresh()
    t : Tau <- fresh.tau()
    return Sig{b, t}

def v.got(r: Array<V> & V, sites: Array<Site>, c: C) -> Result<&1, &1, Err, V & St>:
  (vars, x) = r
  Done{(x, St{vars, sites, c})}

def v.get.go(+i: U32, s: St) -> Result<&1, &1, Err, V & St>:
  match s:
    case St{vars, sites, c}:
      v.got(Array.get(V, vars, i), sites, c)

def v.get(+i: U32) -> M(V):
  s => v.get.go(i, s)

def v.put.go(+i: U32, x: V, s: St) -> Result<&1, &1, Err, Unit & St>:
  match s:
    case St{vars, sites, c}:
      Done{(Unit{}, St{Array.set(V, vars, i, x), sites, c})}

def v.put(+i: U32, x: V) -> M(Unit):
  s => v.put.go(i, x, s)

def v.bind(x: V) -> Maybe<&2, Tau>:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      bind

def v.parent(x: V) -> U32:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      parent

def v.cls(x: V) -> Class:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      cls

def v.tparent(x: V) -> U32:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      tparent

def v.tags(x: V) -> List<&2, TE>:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      tags

def v.with.bind(x: V, b: Maybe<&2, Tau>) -> V:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      V{b, parent, cls, tparent, tags}

def v.with.parent(x: V, +p: U32) -> V:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      V{bind, p, cls, tparent, tags}

def v.with.cls(x: V, c: Class) -> V:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      V{bind, parent, c, tparent, tags}

def v.with.tparent(x: V, +p: U32) -> V:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      V{bind, parent, cls, p, tags}

def v.with.tags(x: V, ts: List<&2, TE>) -> V:
  match x:
    case V{bind, parent, cls, tparent, tags}:
      V{bind, parent, cls, tparent, ts}

# Equations, leaves, sites, counters
# ----------------------------------

def eq.add(e: SumEq) -> M(Unit):
  on.c(c => c.with.eq(c, e))

# recordLeaf
def leaf.add(p: List<&2, U32>) -> M(Unit):
  on.c(c => c.with.leaf(c, p))

def eqs.get() -> M(List<&2, SumEq>):
  with.c(List<&2, SumEq>, c => c.eqs(c))

def leaves.get() -> M(List<&2, List<&2, U32>>):
  with.c(List<&2, List<&2, U32>>, c => c.leaves(c))

def next.get() -> M(U32):
  with.c(U32, c => c.next(c))

def nsites.get() -> M(U32):
  with.c(U32, c => c.nsites(c))

def insts.get(+h: String) -> M(U32):
  with.c(U32, c => c.inst(c, h))

def insts.put(+h: String, +n: U32) -> M(Unit):
  on.c(c => c.with.inst(c, h, n))

# The variables a body's first derivation minted (0 before it has one).
def sizes.get(+h: String) -> M(U32):
  with.c(U32, c => c.size(c, h))

def sizes.put(+h: String, +n: U32) -> M(Unit):
  on.c(c => c.with.size(c, h, n))

def grow.sites(+cap: U32, a: Array<Site>) -> Array<Site>:
  ANode{a, Array.new(Site, U32.log2(cap), site.empty())}

def site.add.room(room: Bool, x: Site, vars: Array<V>, sites: Array<Site>, c: C) -> Result<&1, &1, Err, Unit & St>:
  match room:
    case True{}:
      match c:
        case C{next, cap, +nsites, scap, eqs, leaves, insts, sizes}:
          Done{(Unit{}, St{vars, Array.set(Site, sites, nsites, x), C{next, cap, (nsites + 1 : U32), scap, eqs, leaves, insts, sizes}})}
    case False{}:
      match c:
        case C{next, cap, +nsites, +scap, eqs, leaves, insts, sizes}:
          Done{(Unit{}, St{vars, Array.set(Site, grow.sites(scap, sites), nsites, x), C{next, cap, (nsites + 1 : U32), (scap * 2 : U32), eqs, leaves, insts, sizes}})}

def site.add.at(x: Site, vars: Array<V>, sites: Array<Site>, c: C) -> Result<&1, &1, Err, Unit & St>:
  match c:
    case C{next, cap, +nsites, +scap, eqs, leaves, insts, sizes}:
      site.add.room(U32.is_lt(nsites, scap), x, vars, sites, C{next, cap, nsites, scap, eqs, leaves, insts, sizes})

def site.add.go(x: Site, s: St) -> Result<&1, &1, Err, Unit & St>:
  match s:
    case St{vars, sites, c}:
      site.add.at(x, vars, sites, c)

# registerApply
def site.add(x: Site) -> M(Unit):
  s => site.add.go(x, s)

def site.got(r: Array<Site> & Site, vars: Array<V>, c: C) -> Result<&1, &1, Err, Site & St>:
  (sites, x) = r
  Done{(x, St{vars, sites, c})}

def site.get.go(+k: U32, s: St) -> Result<&1, &1, Err, Site & St>:
  match s:
    case St{vars, sites, c}:
      site.got(Array.get(Site, sites, k), vars, c)

def site.get(+k: U32) -> M(Site):
  s => site.get.go(k, s)

def site.put.go(+k: U32, x: Site, s: St) -> Result<&1, &1, Err, Unit & St>:
  match s:
    case St{vars, sites, c}:
      Done{(Unit{}, St{vars, Array.set(Site, sites, k, x), c})}

def site.put(+k: U32, x: Site) -> M(Unit):
  s => site.put.go(k, x, s)

# Union-find
# ----------

def parent.of(tag: Bool, x: V) -> U32:
  match tag:
    case True{}:
      v.tparent(x)
    case False{}:
      v.parent(x)

def merge.lv(ge: Bool, a: Class, b: Class) -> Mg:
  match ge:
    case True{}:
      MgOk{a, False{}}
    case False{}:
      MgOk{b, True{}}

# mergeClasses, and whether the class changed: it keeps the first class
# unless the second is stricter.
def merge(a: Class, b: Class) -> Mg:
  match a:
    case Unrestricted{}:
      match b:
        case Unrestricted{}:
          MgOk{Unrestricted{}, False{}}
        case other:
          MgOk{other, True{}}
    case ForcedZero{z}:
      match b:
        case Unrestricted{}:
          MgOk{ForcedZero{z}, False{}}
        case ForcedZero{y}:
          MgOk{ForcedZero{z}, False{}}
        case ForcedLevel{n, l}:
          MgErr{BoxConflict{l, z}}
    case ForcedLevel{+la, l}:
      match b:
        case Unrestricted{}:
          MgOk{ForcedLevel{la, l}, False{}}
        case ForcedZero{z}:
          MgErr{BoxConflict{l, z}}
        case ForcedLevel{+lb, m}:
          merge.lv(U32.is_ge(la, lb), ForcedLevel{la, l}, ForcedLevel{lb, m})

def over.cap(c: Class) -> Bool:
  match c:
    case ForcedLevel{n, blame}:
      U32.is_gt(n, level.cap())
    case _:
      False{}

def sum.eq(+loc: Lc.Loc, +what: String, lhs: List<&2, U32>, +rhs: U32) -> M(Unit):
  eq.add(SumEq{lhs, rhs, Blame{loc, what}})

# Tag classes
# -----------

def te.tag(e: TE) -> String:
  match e:
    case TE{tag, cap}:
      tag

def keys(ts: List<&2, TE>) -> List<&2, String>:
  match ts:
    case Nil{}:
      []
    case Con{e, rest}:
      te.tag(e) <> keys(rest)

def with.cap(ts: List<&2, String>, +cap: Maybe<&2, Sig>) -> List<&2, TE>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      TE{t, cap} <> with.cap(rest, cap)

def keep(x: Maybe<&2, Sig>, y: Maybe<&2, Sig>) -> Maybe<&2, Sig>:
  match x:
    case Some{s}:
      Some{s}
    case None{}:
      y

def te.cap(e: TE) -> Maybe<&2, Sig>:
  match e:
    case TE{tag, cap}:
      cap

# How the heads of two tag lists compare (a missing head is greatest).
def heads(xs: List<&2, TE>, ys: List<&2, TE>) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      match ys:
        case Nil{}:
          LT{}
        case Con{y, yr}:
          String.order(te.tag(x), te.tag(y))

def join.eq(x: TE, y: TE) -> TE:
  match x y:
    case TE{t, cx} TE{u, cy}:
      TE{t, keep(cx, cy)}

# The two classes' tags, joined: a tag on both sides keeps a capture, the
# first side's when both have one (Map.unionWith keep).
def tags.join.go(fuel: Nat, +xs: List<&2, TE>, +ys: List<&2, TE>, c: Cmp) -> List<&2, TE>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match xs:
        case Nil{}:
          ys
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              Con{x, xr}
            case Con{+y, +yr}:
              match c:
                case LT{}:
                  x <> tags.join.go(f, xr, Con{y, yr}, heads(xr, Con{y, yr}))
                case GT{}:
                  y <> tags.join.go(f, Con{x, xr}, yr, heads(Con{x, xr}, yr))
                case EQ{}:
                  join.eq(x, y) <> tags.join.go(f, xr, yr, heads(xr, yr))

def tags.join(+xs: List<&2, TE>, +ys: List<&2, TE>) -> List<&2, TE>:
  tags.join.go((List.length(&2, TE, xs) + List.length(&2, TE, ys) + 1n : Nat), xs, ys, heads(xs, ys))

def pending.one(cx: Maybe<&2, Sig>, cy: Maybe<&2, Sig>, rest: List<&2, SP>) -> List<&2, SP>:
  match cx:
    case Some{a}:
      match cy:
        case Some{b}:
          SP{a, b} <> rest
        case None{}:
          rest
    case None{}:
      rest

# The captures both classes hold for one tag, in tag order: they must
# unify.
def pending.go(fuel: Nat, +xs: List<&2, TE>, +ys: List<&2, TE>, c: Cmp) -> List<&2, SP>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match xs:
        case Nil{}:
          []
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              []
            case Con{+y, +yr}:
              match c:
                case LT{}:
                  pending.go(f, xr, Con{y, yr}, heads(xr, Con{y, yr}))
                case GT{}:
                  pending.go(f, Con{x, xr}, yr, heads(Con{x, xr}, yr))
                case EQ{}:
                  pending.one(te.cap(x), te.cap(y), pending.go(f, xr, yr, heads(xr, yr)))

def pending(+xs: List<&2, TE>, +ys: List<&2, TE>) -> List<&2, SP>:
  pending.go((List.length(&2, TE, xs) + List.length(&2, TE, ys) + 1n : Nat), xs, ys, heads(xs, ys))

def head.cmp(ts: List<&2, TE>, +t: String) -> Cmp:
  match ts:
    case Nil{}:
      GT{}
    case Con{e, rest}:
      String.order(te.tag(e), t)

# The capture a class holds for one tag, if the tag is there with one.
def lookup.go(fuel: Nat, +ts: List<&2, TE>, +t: String, c: Cmp) -> Maybe<&2, Sig>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match ts:
        case Nil{}:
          None{}
        case Con{+e, +rest}:
          match c:
            case LT{}:
              lookup.go(f, rest, t, head.cmp(rest, t))
            case EQ{}:
              te.cap(e)
            case GT{}:
              None{}

def lookup(+ts: List<&2, TE>, +t: String) -> Maybe<&2, Sig>:
  lookup.go((List.length(&2, TE, ts) + 1n : Nat), ts, t, head.cmp(ts, t))

def occurs.var(hit: Bool, f: Nat, +i: U32, ts: List<&2, Tau>) -> M(Bool):
  match hit:
    case True{}:
      M.pure(Bool, True{})
    case False{}:
      M.pure(Bool, False{})

def sigs(ps: List<&2, SP>, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  match ps:
    case Nil{}:
      rest
    case Con{p, pr}:
      match p:
        case SP{a, b}:
          WSig{[], "", loc, a, b} <> sigs(pr, loc, rest)

def cap.all(cs: List<&2, TE>, +vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, +t: Tau, rest: List<&2, W>) -> List<&2, W>:
  match cs:
    case Nil{}:
      rest
    case Con{e, er}:
      match e:
        case TE{tag, cap}:
          match cap:
            case Some{s}:
              match s:
                case Sig{b, ct}:
                  WTau{vis, mode, loc, ct, t} <> cap.all(er, vis, mode, loc, t, rest)
            case None{}:
              cap.all(er, vis, mode, loc, t, rest)

def cap.mode(m: Maybe<&2, Sig>, +cs: List<&2, TE>, +vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, +t: Tau, rest: List<&2, W>) -> List<&2, W>:
  match m:
    case Some{s}:
      match s:
        case Sig{b, ct}:
          WTau{vis, mode, loc, ct, t} <> rest
    case None{}:
      cap.all(cs, vis, mode, loc, t, rest)

def cap.for(+mode: String, +cs: List<&2, TE>) -> Maybe<&2, Sig>:
  match mode:
    case SNil{}:
      None{}
    case other:
      lookup(cs, other)

def member(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      U32.is_eq(x, y) || member(rest, x)

def use.add.got(+path: String, +loc: Lc.Loc, r: Map<&2, Use> & Use) -> Map<&2, Use>:
  (acc, u) = r
  match u:
    case Use{n, first}:
      Map.set(&2, Use, acc, path, Use{(n + 1 : U32), first})

def use.add(+path: String, +loc: Lc.Loc, acc: Map<&2, Use>) -> Map<&2, Use>:
  use.add.got(path, loc, Map.get(Use, Use{0, loc}, acc, path))

# Env occurrences by the projection path applied to them, innermost step
# first ("RL" is Left (Right Env)); a pair or SetEnv starts its children's
# paths afresh, and references are closed.
def usage(l: Lf.L, +path: String, acc: Map<&2, Use>) -> Map<&2, Use>:
  match l:
    case Lf.LEnv{loc}:
      use.add(path, loc, acc)
    case Lf.LUnsized{loc, tok}:
      use.add(path, loc, acc)
    case Lf.LLeft{loc, x}:
      usage(x, "L" ++ path, acc)
    case Lf.LRight{loc, x}:
      usage(x, "R" ++ path, acc)
    case Lf.LCheck{loc, cloc, tc, c}:
      usage(c, path, acc)
    case Lf.LPair{loc, a, b}:
      usage(b, "", usage(a, "", acc))
    case Lf.LSetEnv{loc, x}:
      usage(x, "", acc)
    case _:
      acc

def extends(ks: List<&2, String>, +p: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{+k, rest}:
      (String.starts_with(k, p) && Bool.not(String.eq(k, p))) || extends(rest, p)

def dup.at(dup: Bool, +path: String, +loc: Lc.Loc, later: Maybe<&2, Dup>) -> Maybe<&2, Dup>:
  match dup:
    case True{}:
      Some{Dup{path, loc}}
    case False{}:
      later

def dup.find(us: List<&2, Sigma<&2, &2, String, _ => Use>>, +ks: List<&2, String>) -> Maybe<&2, Dup>:
  match us:
    case Nil{}:
      None{}
    case Con{kv, rest}:
      match kv:
        case (+path, u):
          match u:
            case Use{+n, loc}:
              dup.at(U32.is_ge(n, 2) || (U32.is_ge(n, 1) && extends(ks, path)), path, loc, dup.find(rest, ks))

# contraction: the first path, in path order, used twice, or used along
# with a longer path it starts.
def contraction(+us: Map<&2, Use>) -> Maybe<&2, Dup>:
  dup.find(Map.to_list(&2, Use, us), Map.keys(&2, Use, us))

# Constraint generation (viewNode, intrinsic)
# -------------------------------------------

def sig.b(s: Sig) -> U32:
  match s:
    case Sig{b, t}:
      b

def sig.t(s: Sig) -> Tau:
  match s:
    case Sig{b, t}:
      t

def l.loc(l: Lf.L) -> Lc.Loc:
  match l:
    case Lf.LZero{loc}:
      loc
    case Lf.LPair{loc, a, b}:
      loc
    case Lf.LEnv{loc}:
      loc
    case Lf.LSetEnv{loc, x}:
      loc
    case Lf.LGate{loc}:
      loc
    case Lf.LLeft{loc, x}:
      loc
    case Lf.LRight{loc, x}:
      loc
    case Lf.LAbort{loc}:
      loc
    case Lf.LUnsized{loc, tok}:
      loc
    case Lf.LCheck{loc, cloc, tc, c}:
      loc
    case Lf.LRef{loc, h}:
      loc

def paths.in(+w: U32, p: Paths) -> Paths:
  match p:
    case Paths{here, glob}:
      Paths{w <> here, w <> glob}

def paths.glob(p: Paths) -> List<&2, U32>:
  match p:
    case Paths{here, glob}:
      glob

def ctx.depth(c: Ctx) -> U32:
  match c:
    case Ctx{bang, tau, depth}:
      depth

def str.heads(xs: List<&2, String>, ys: List<&2, String>) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      match ys:
        case Nil{}:
          LT{}
        case Con{y, yr}:
          String.order(x, y)

# xs less ys.
def diff.go(fuel: Nat, +xs: List<&2, String>, +ys: List<&2, String>, c: Cmp) -> List<&2, String>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match xs:
        case Nil{}:
          []
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              Con{x, xr}
            case Con{+y, +yr}:
              match c:
                case LT{}:
                  x <> diff.go(f, xr, Con{y, yr}, str.heads(xr, Con{y, yr}))
                case GT{}:
                  diff.go(f, Con{x, xr}, yr, str.heads(Con{x, xr}, yr))
                case EQ{}:
                  diff.go(f, xr, yr, str.heads(xr, yr))

def diff(+xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  diff.go((List.length(&2, String, xs) + List.length(&2, String, ys) + 1n : Nat), xs, ys, str.heads(xs, ys))

def both.go(fuel: Nat, +xs: List<&2, String>, +ys: List<&2, String>, c: Cmp) -> List<&2, String>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match xs:
        case Nil{}:
          ys
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              Con{x, xr}
            case Con{+y, +yr}:
              match c:
                case LT{}:
                  x <> both.go(f, xr, Con{y, yr}, str.heads(xr, Con{y, yr}))
                case GT{}:
                  y <> both.go(f, Con{x, xr}, yr, str.heads(Con{x, xr}, yr))
                case EQ{}:
                  x <> both.go(f, xr, yr, str.heads(xr, yr))

# The union of two sorted lists.
def both(+xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  both.go((List.length(&2, String, xs) + List.length(&2, String, ys) + 1n : Nat), xs, ys, str.heads(xs, ys))

# Dispatch
# --------

def ft.caps(cs: List<&2, TE>, +vis: List<&2, U32>, rest: List<&2, FT>) -> List<&2, FT>:
  match cs:
    case Nil{}:
      rest
    case Con{e, er}:
      FtCap{vis, te.cap(e)} <> ft.caps(er, vis, rest)

def body.fi(b: Lf.Body) -> U32:
  match b:
    case Lf.Body{fi, body}:
      fi

def body.l(b: Lf.Body) -> Lf.L:
  match b:
    case Lf.Body{fi, body}:
      body

def site.done(s: Site) -> List<&2, String>:
  match s:
    case Site{fn, env, res, glob, depth, loc, done}:
      done

def site.with.done(s: Site, d: List<&2, String>) -> Site:
  match s:
    case Site{fn, env, res, glob, depth, loc, done}:
      Site{fn, env, res, glob, depth, loc, d}

def site.fn(s: Site) -> Tau:
  match s:
    case Site{fn, env, res, glob, depth, loc, done}:
      fn

def site.loc(s: Site) -> Lc.Loc:
  match s:
    case Site{fn, env, res, glob, depth, loc, done}:
      loc

def derived(+what: String, b: Blame) -> Blame:
  match b:
    case Blame{loc, why}:
      Blame{loc, what ++ ": " ++ why}

def is.fz(c: Class) -> Bool:
  match c:
    case ForcedZero{b}:
      True{}
    case _:
      False{}

def lower(c: Class) -> U32:
  match c:
    case ForcedLevel{n, b}:
      n
    case _:
      0

def all.fz(cs: List<&2, Class>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      is.fz(c) && all.fz(rest)

def sum.lower(cs: List<&2, Class>) -> U32:
  match cs:
    case Nil{}:
      0
    case Con{c, rest}:
      (lower(c) + sum.lower(rest) : U32)

def boxable.at(fz: Bool, l: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match fz:
    case True{}:
      rest
    case False{}:
      l <> rest

# The summands whose classes may be boxed.
def boxable(ls: List<&2, U32>, cs: List<&2, Class>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      []
    case Con{l, lr}:
      match cs:
        case Nil{}:
          []
        case Con{c, cr}:
          boxable.at(is.fz(c), l, boxable(lr, cr))

def eq.roots(es: List<&2, SumEq>, acc: List<&2, U32>) -> List<&2, U32>:
  match es:
    case Nil{}:
      acc
    case Con{e, rest}:
      match e:
        case SumEq{lhs, rhs, blame}:
          eq.roots(rest, rhs <> List.append(&2, U32, lhs, acc))

def c.cap(c: C) -> U32:
  match c:
    case C{next, cap, nsites, scap, eqs, leaves, insts, sizes}:
      cap

def register(fn: Tau, env: Sig) -> M(Unit):
  do M<Unit>:
    so : Sig <- fresh.sig()
    site.add(Site{fn, env, so, [], 0, Lc.Gen{"virtual application of main to input"}, []})

def appliable(t: Tau) -> Bool:
  match t:
    case CodeT{i}:
      True{}
    case CapT{i}:
      True{}
    case _:
      False{}

def virtual.pair(ok: Bool, wc: Tau, +b2: U32, +t2: Tau) -> M(Unit):
  match ok:
    case True{}:
      do M<Unit>:
        ib : U32 <- fresh()
        eb : U32 <- fresh()
        register(wc, Sig{eb, PairT{ib, DataT{}, b2, t2}})
    case False{}:
      M.pure(Unit, Unit{})

def virtual.top(ok: Bool, w: Tau) -> M(Unit):
  match ok:
    case True{}:
      do M<Unit>:
        ib : U32 <- fresh()
        register(w, Sig{ib, DataT{}})
    case False{}:
      M.pure(Unit, Unit{})

# allDataShape
def all.data(s: Lf.Shape) -> Bool:
  match s:
    case Lf.CapData{}:
      True{}
    case Lf.CapPair{a, b}:
      all.data(a) && all.data(b)
    case _:
      False{}

def meet.flat(data: Bool) -> Lf.Shape:
  match data:
    case True{}:
      Lf.CapData{}
    case False{}:
      Lf.CapOther{}

# meetShape: what two construction sites' capture shapes agree on (equal
# shapes meet to themselves: pairs by their parts, code to code).
def meet(a: Lf.Shape, b: Lf.Shape) -> Lf.Shape:
  match a b:
    case Lf.CapPair{a1, a2} Lf.CapPair{b1, b2}:
      Lf.CapPair{meet(a1, b1), meet(a2, b2)}
    case Lf.CapCode{} Lf.CapCode{}:
      Lf.CapCode{}
    case +x +y:
      meet.flat(all.data(x) && all.data(y))

def shape.meet(+h: String, +s: Lf.Shape, r: Map<&2, Lf.Shape> & Lf.Shape) -> Map<&2, Lf.Shape>:
  (m, +old) = r
  Map.set(&2, Lf.Shape, m, h, meet(s, old))

def shape.add(+h: String, +s: Lf.Shape, r: Map<&2, Lf.Shape> & Bool) -> Map<&2, Lf.Shape>:
  (m, known) = r
  match known:
    case True{}:
      shape.meet(h, s, Map.get(Lf.Shape, Lf.CapOther{}, m, h))
    case False{}:
      Map.set(&2, Lf.Shape, m, h, s)

# The bodies a term references directly, in hash order (refsOf).
def refs(l: Lf.L, +acc: List<&2, String>) -> List<&2, String>:
  match l:
    case Lf.LRef{loc, h}:
      both(acc, [h])
    case Lf.LPair{loc, a, b}:
      refs(b, refs(a, acc))
    case Lf.LSetEnv{loc, x}:
      refs(x, acc)
    case Lf.LLeft{loc, x}:
      refs(x, acc)
    case Lf.LRight{loc, x}:
      refs(x, acc)
    case Lf.LCheck{loc, cloc, tc, c}:
      refs(c, refs(tc, acc))
    case _:
      acc

def ran(r: Result<&1, &1, Err, Sig & St>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{p}:
      True{}

def failure(r: Result<&1, &1, Err, Sig & St>) -> Maybe<&2, Err>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{p}:
      None{}

def ensure.at(+h: String, r: Map<&2, Bool> & Bool) -> DJ:
  (m, known) = r
  DjEnsure{h, known, m}

def ensure(+h: String, m: Map<&2, Bool>) -> DJ:
  ensure.at(h, Map.has(&2, Bool, m, h))

def memo.ok.at(r: Map<&2, Bool> & Bool) -> Bool & Map<&2, Bool>:
  (m, ok) = r
  (ok, m)

def memo.ok(+h: String, m: Map<&2, Bool>) -> Bool & Map<&2, Bool>:
  memo.ok.at(Map.get(Bool, False{}, m, h))

def next.of(+h: String, rest: List<&2, String>, p: Bool & Map<&2, Bool>) -> DJ:
  (ok, m) = p
  DjNext{ok, h, rest, m}

def body.of(+bodies: Map<&2, Lf.Body>, +h: String) -> Lf.Body:
  Pair.snd(Map<&2, Lf.Body>, Lf.Body, Map.get(Lf.Body, Lf.Body{0, Lf.LZero{Lc.Unknown{}}}, bodies, h))

def data.main(data: Bool) -> Maybe<&2, Err>:
  match data:
    case True{}:
      Some{TypeMismatch{Lc.Gen{"EAL certification"}, "main is data through and through; a program must be a function of its input"}}
    case False{}:
      None{}

# The program's main shape, or why it does not certify.
def main.of(r: Result<&1, &1, Err, Lf.Shape & St>) -> Result<&2, &2, Err, Lf.Shape>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{p}:
      (s, st) = p
      Done{s}

# certifyMain beyond ealLiftedMain: main must be a function of its input.
def certified(r: Result<&2, &2, Err, Lf.Shape>) -> Maybe<&2, Err>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{s}:
      data.main(all.data(s))

def dr.memo(r: DR) -> Map<&2, Bool>:
  match r:
    case DR{memo, failed}:
      memo

def layouts.keep(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Shape>>, +memo: Map<&2, Bool>, +acc: Map<&2, Lf.Shape>) -> Map<&2, Lf.Shape>:
  match kvs:
    case Nil{}:
      acc
    case Con{kv, rest}:
      match kv:
        case (+h, s):
          layouts.keep(rest, memo, Bool.pick(Map<&2, Lf.Shape>, Pair.snd(Map<&2, Bool>, Bool, Map.get(Bool, False{}, memo, h)),
            Map.set(&2, Lf.Shape, acc, h, s), acc))

# A variable's record changed in one step.
def v.mod.at(+i: U32, f: V -> V, r: Array<V> & V, sites: Array<Site>, c: C) -> Result<&1, &1, Err, Unit & St>:
  (vars, x) = r
  Done{(Unit{}, St{Array.set(V, vars, i, f(x)), sites, c})}

def v.mod.go(+i: U32, f: V -> V, s: St) -> Result<&1, &1, Err, Unit & St>:
  match s:
    case St{vars, sites, c}:
      v.mod.at(i, f, Array.get(V, vars, i), sites, c)

def v.mod(+i: U32, f: V -> V) -> M(Unit):
  s => v.mod.go(i, f, s)

# Something of a variable's record, read in one step.
def v.read.at(-A: Data, f: V -> A, r: Array<V> & V, sites: Array<Site>, c: C) -> Result<&1, &1, Err, A & St>:
  (vars, x) = r
  Done{(f(x), St{vars, sites, c})}

def v.read.go(-A: Data, +i: U32, f: V -> A, s: St) -> Result<&1, &1, Err, A & St>:
  match s:
    case St{vars, sites, c}:
      v.read.at(A, f, Array.get(V, vars, i), sites, c)

def v.read(-A: Data, +i: U32, f: V -> A) -> M(A):
  s => v.read.go(A, i, f, s)

def set.bind(+i: U32, t: Tau) -> M(Unit):
  v.mod(i, x => v.with.bind(x, Some{t}))

def bind.at(cyclic: Bool, +loc: Lc.Loc, +i: U32, +t: Tau, rest: List<&2, W>) -> M(List<&2, W>):
  match cyclic:
    case True{}:
      do M<List<&2, W>>:
        u : Unit <- set.bind(i, DataT{})
        return WTau{[], "", loc, t, DataT{}} <> rest
    case False{}:
      do M<List<&2, W>>:
        u : Unit <- set.bind(i, t)
        return rest

def set.parent(+i: U32, +p: U32) -> M(Unit):
  v.mod(i, x => v.with.parent(x, p))

def set.cls(+i: U32, c: Class) -> M(Unit):
  v.mod(i, x => v.with.cls(x, c))

def constrain.merged(+r: U32, m: Mg) -> M(Bool):
  match m:
    case MgErr{e}:
      M.fail(Bool, e)
    case MgOk{c, changed}:
      match changed:
        case True{}:
          do M<Bool>:
            u : Unit <- set.cls(r, c)
            return True{}
        case False{}:
          M.pure(Bool, False{})

def union.merged(+ra: U32, +rb: U32, m: Mg) -> M(Unit):
  match m:
    case MgErr{e}:
      M.fail(Unit, e)
    case MgOk{c, changed}:
      do M<Unit>:
        u : Unit <- set.parent(ra, rb)
        u2 : Unit <- set.cls(rb, c)
        set.cls(ra, Unrestricted{})

def set.tparent(+i: U32, +p: U32) -> M(Unit):
  v.mod(i, x => v.with.tparent(x, p))

def set.tags(+i: U32, ts: List<&2, TE>) -> M(Unit):
  v.mod(i, x => v.with.tags(x, ts))

# A fresh code class holding exactly these tags (freshCode).
def fresh.code(ts: List<&2, String>) -> M(Tau):
  do M<Tau>:
    +i : U32 <- fresh()
    u : Unit <- set.tags(i, with.cap(ts, None{}))
    return CodeT{i}

def union.tags.roots(same: Bool, +ra: U32, +rb: U32) -> M(List<&2, SP>):
  match same:
    case True{}:
      M.pure(List<&2, SP>, [])
    case False{}:
      do M<List<&2, SP>>:
        xa : V <- v.get(ra)
        xb : V <- v.get(rb)
        +ma : List<&2, TE> = v.tags(xa)
        +mb : List<&2, TE> = v.tags(xb)
        u : Unit <- set.tparent(ra, rb)
        u2 : Unit <- set.tags(rb, tags.join(ma, mb))
        u3 : Unit <- set.tags(ra, [])
        return pending(ma, mb)

def get.bind(+i: U32) -> M(Maybe<&2, Tau>):
  v.read(Maybe<&2, Tau>, i, x => v.bind(x))

def walk.go(fuel: Nat, j: WK) -> M(Tau):
  match fuel:
    case 0n:
      M.fail(Tau, Internal{"a type binding cycle"})
    case 1n+f:
      match j:
        case WkTau{t}:
          match t:
            case VarT{+i}:
              do M<Tau>:
                b : Maybe<&2, Tau> <- get.bind(i)
                walk.go(f, WkBound{i, b})
            case other:
              M.pure(Tau, other)
        case WkBound{i, b}:
          match b:
            case Some{t}:
              walk.go(f, WkTau{t})
            case None{}:
              M.pure(Tau, VarT{i})

# walkTau
def walk(t: Tau) -> M(Tau):
  walk.go(U32.to_nat(4294967295), WkTau{t})

def occurs.go(fuel: Nat, +i: U32, j: OJ) -> M(Bool):
  match fuel:
    case 0n:
      M.pure(Bool, False{})
    case 1n+f:
      match j:
        case OTodo{ts}:
          match ts:
            case Nil{}:
              M.pure(Bool, False{})
            case Con{t, rest}:
              do M<Bool>:
                w : Tau <- walk(t)
                occurs.go(f, i, OSeen{w, rest})
        case OSeen{t, ts}:
          match t:
            case VarT{j2}:
              occurs.var(U32.is_eq(i, j2), f, i, ts)
            case PairT{b1, t1, b2, t2}:
              occurs.go(f, i, OTodo{t1 <> t2 <> ts})
            case _:
              occurs.go(f, i, OTodo{ts})

def occurs(+i: U32, t: Tau) -> M(Bool):
  occurs.go(U32.to_nat(4294967295), i, OTodo{[t]})

# Unification
# -----------

# bindTVar: a cyclic binding collapses to data.
def bind.var(+loc: Lc.Loc, +i: U32, +t: Tau, rest: List<&2, W>) -> M(List<&2, W>):
  do M<List<&2, W>>:
    cyclic : Bool <- occurs(i, t)
    bind.at(cyclic, loc, i, t, rest)

def same.var(same: Bool, +loc: Lc.Loc, +i: U32, +j: U32, rest: List<&2, W>) -> M(List<&2, W>):
  match same:
    case True{}:
      M.pure(List<&2, W>, rest)
    case False{}:
      bind.var(loc, i, VarT{j}, rest)

def virtual.at(+w: Tau) -> M(Unit):
  match w:
    case PairT{b1, t1, +b2, +t2}:
      do M<Unit>:
        +wc : Tau <- walk(t1)
        virtual.pair(appliable(wc), wc, b2, t2)
    case other:
      virtual.top(appliable(other), other)

# virtualMainApply: the run applies the program to its input, so that
# application is certified too: a closure package applies its code to
# (input, captures), bare code to the input alone.
def virtual(s: Sig) -> M(Unit):
  do M<Unit>:
    +w : Tau <- walk(sig.t(s))
    virtual.at(w)

# shapeOfSigma
def shape.go(+fuel: Nat, j: SJ) -> M(Lf.Shape):
  match fuel:
    case 0n:
      M.pure(Lf.Shape, Lf.CapOther{})
    case 1n+f:
      match j:
        case SjTau{t}:
          do M<Lf.Shape>:
            w : Tau <- walk(t)
            shape.go(f, SjWalked{w})
        case SjWalked{w}:
          match w:
            case DataT{}:
              M.pure(Lf.Shape, Lf.CapData{})
            case PairT{b1, t1, b2, t2}:
              do M<Lf.Shape>:
                a : Lf.Shape <- shape.go(f, SjTau{t1})
                b : Lf.Shape <- shape.go(f, SjTau{t2})
                return Lf.CapPair{a, b}
            case CodeT{i}:
              M.pure(Lf.Shape, Lf.CapCode{})
            case _:
              M.pure(Lf.Shape, Lf.CapOther{})

def shape(s: Sig) -> M(Lf.Shape):
  shape.go(U32.to_nat(4294967295), SjTau{sig.t(s)})

def shapes.caps(ts: List<&2, TE>, +acc: Map<&2, Lf.Shape>) -> M(Map<&2, Lf.Shape>):
  match ts:
    case Nil{}:
      M.pure(Map<&2, Lf.Shape>, acc)
    case Con{e, rest}:
      match e:
        case TE{tag, cap}:
          match tag:
            case SCon{Chr{48}, +h}:
              match cap:
                case Some{sig}:
                  do M<Map<&2, Lf.Shape>>:
                    +s : Lf.Shape <- shape(sig)
                    shapes.caps(rest, shape.add(h, s, Map.has(&2, Lf.Shape, acc, h)))
                case None{}:
                  shapes.caps(rest, acc)
            case _:
              shapes.caps(rest, acc)

def shapes.go(fuel: Nat, +i: U32, more: Bool, +acc: Map<&2, Lf.Shape>) -> M(Map<&2, Lf.Shape>):
  match fuel:
    case 0n:
      M.pure(Map<&2, Lf.Shape>, acc)
    case 1n+f:
      match more:
        case False{}:
          M.pure(Map<&2, Lf.Shape>, acc)
        case True{}:
          do M<Map<&2, Lf.Shape>>:
            x : V <- v.get(i)
            n : U32 <- next.get()
            acc2 : Map<&2, Lf.Shape> <- shapes.caps(v.tags(x), acc)
            shapes.go(f, (i + 1 : U32), U32.is_lt((i + 1 : U32), n), acc2)

# groundCaptureShapes: every closure package's capture shape, met per hash
# over the sites it is built at.
def shapes() -> M(Map<&2, Lf.Shape>):
  do M<Map<&2, Lf.Shape>>:
    +n : U32 <- next.get()
    shapes.go(U32.to_nat(n), 0, U32.is_lt(0, n), Map.new(&2, Lf.Shape))

# Bodies standalone, and their dependencies
# -----------------------------------------

def get.cls(+i: U32) -> M(Class):
  v.read(Class, i, x => v.cls(x))

def union.roots(same: Bool, +ra: U32, +rb: U32) -> M(Unit):
  match same:
    case True{}:
      M.pure(Unit, Unit{})
    case False{}:
      do M<Unit>:
        ia : Class <- get.cls(ra)
        ib : Class <- get.cls(rb)
        union.merged(ra, rb, merge(ia, ib))

def get.tags(+i: U32) -> M(List<&2, TE>):
  v.read(List<&2, TE>, i, x => v.tags(x))

def root.go(fuel: Nat, +tag: Bool, j: RJ) -> Array<V> & U32:
  match fuel:
    case 0n:
      match j:
        case RjRead{i, r}:
          (a, x) = r
          (a, i)
        case RjUp{i, p, top, a}:
          (a, i)
        case RjFix{i, x, p, done, a}:
          (a, i)
    case 1n+f:
      match j:
        case RjRead{+i, r}:
          (a, x) = r
          +p = parent.of(tag, x)
          root.go(f, tag, RjUp{i, p, U32.is_eq(p, none()), a})
        case RjUp{i, +p, top, a}:
          match top:
            case True{}:
              (a, i)
            case False{}:
              root.go(f, tag, RjRead{p, Array.get(V, a, p)})
        case RjFix{i, x, p, done, a}:
          (a, i)

def with.parent.of(tag: Bool, x: V, +p: U32) -> V:
  match tag:
    case True{}:
      v.with.tparent(x, p)
    case False{}:
      v.with.parent(x, p)

# Every variable on the path from i points at the root r afterwards.
def compress.go(fuel: Nat, +tag: Bool, +r: U32, j: RJ) -> Array<V>:
  match fuel:
    case 0n:
      match j:
        case RjRead{i, rd}:
          (a, x) = rd
          a
        case RjUp{i, p, top, a}:
          a
        case RjFix{i, x, p, done, a}:
          a
    case 1n+f:
      match j:
        case RjRead{+i, rd}:
          (a, +x) = rd
          +p = parent.of(tag, x)
          compress.go(f, tag, r, RjFix{i, x, p, U32.is_eq(p, none()) || U32.is_eq(p, r), a})
        case RjUp{i, p, top, a}:
          a
        case RjFix{+i, x, +p, done, a}:
          match done:
            case True{}:
              a
            case False{}:
              compress.go(f, tag, r, RjRead{p, Array.get(V, Array.set(V, a, i, with.parent.of(tag, x, r)), p)})

def find.fin(+tag: Bool, +i: U32, r: Array<V> & U32, sites: Array<Site>, c: C) -> Result<&1, &1, Err, U32 & St>:
  (a, +root) = r
  Done{(root, St{compress.go(U32.to_nat(4294967295), tag, root, RjRead{i, Array.get(V, a, i)}), sites, c})}

def find.go(+tag: Bool, +i: U32, s: St) -> Result<&1, &1, Err, U32 & St>:
  match s:
    case St{vars, sites, c}:
      find.fin(tag, i, root.go(U32.to_nat(4294967295), tag, RjRead{i, Array.get(V, vars, i)}), sites, c)

# find with path compression, on either union-find.
def find(+tag: Bool, +i: U32) -> M(U32):
  s => find.go(tag, i, s)

# findB
def find.b(+i: U32) -> M(U32):
  find(False{}, i)

# findTag
def find.t(+i: U32) -> M(U32):
  find(True{}, i)

# Bang classes
# ------------

# constrainB on a class root.
def constrain.go(+r: U32, nc: Class) -> M(Bool):
  do M<Bool>:
    ci : Class <- get.cls(r)
    constrain.merged(r, merge(ci, nc))

def constrain.at(over: Bool, +r: U32, nc: Class) -> M(Bool):
  match over:
    case True{}:
      match nc:
        case ForcedLevel{n, blame}:
          M.fail(Bool, GaveUp{"bang level exceeded cap of 4096: " ++ blame.show(blame)})
        case _:
          M.fail(Bool, Internal{"level cap"})
    case False{}:
      constrain.go(r, nc)

# constrainB: whether the class changed.
def constrain(+b: U32, +nc: Class) -> M(Bool):
  do M<Bool>:
    +r : U32 <- find.b(b)
    constrain.at(over.cap(nc), r, nc)

# constrainB on a variable known to be a root.
def constrain.root(+r: U32, +nc: Class) -> M(Bool):
  constrain.at(over.cap(nc), r, nc)

# unionB
def union.b(+a: U32, +b: U32) -> M(Unit):
  do M<Unit>:
    +ra : U32 <- find.b(a)
    +rb : U32 <- find.b(b)
    union.roots(U32.is_eq(ra, rb), ra, rb)

def forced.zero(+blame: Blame) -> M(U32):
  do M<U32>:
    +b : U32 <- fresh()
    changed : Bool <- constrain(b, ForcedZero{blame})
    return b

# plainSigma: a value constructor's own type, locally unboxed.
def plain(+loc: Lc.Loc, +what: String, t: Tau) -> M(Sig):
  do M<Sig>:
    b : U32 <- forced.zero(Blame{loc, what})
    return Sig{b, t}

# The captures of a tag class (capturesOf).
def caps(+i: U32) -> M(List<&2, TE>):
  do M<List<&2, TE>>:
    +r : U32 <- find.t(i)
    x : V <- v.get(r)
    return v.tags(x)

# tagSetOf
def tag.set(+i: U32) -> M(List<&2, String>):
  do M<List<&2, String>>:
    ts : List<&2, TE> <- caps(i)
    return keys(ts)

# A closure package: the tags of code class i, each carrying this capture
# (packageClass).
def package(+i: U32, +cap: Sig) -> M(U32):
  do M<U32>:
    ts : List<&2, String> <- tag.set(i)
    +p : U32 <- fresh()
    u : Unit <- set.tags(p, with.cap(ts, Some{cap}))
    return p

# unionTags, less the unifications of the captures both held, which it
# returns for the caller to run.
def union.tags(+a: U32, +b: U32) -> M(List<&2, SP>):
  do M<List<&2, SP>>:
    +ra : U32 <- find.t(a)
    +rb : U32 <- find.t(b)
    union.tags.roots(U32.is_eq(ra, rb), ra, rb)

# Types
# -----

# deepShowTau, for mismatch reports.
def deep.show(+fuel: Nat, j: DS) -> M(String):
  match fuel:
    case 0n:
      M.pure(String, "...")
    case 1n+f:
      match j:
        case DsTau{t, +d, stop}:
          match stop:
            case True{}:
              M.pure(String, "...")
            case False{}:
              do M<String>:
                w : Tau <- walk(t)
                deep.show(f, DsWalked{w, d})
        case DsWalked{w, +d}:
          match w:
            case DataT{}:
              M.pure(String, "D")
            case VarT{i}:
              M.pure(String, "t" ++ U32.show(i))
            case CodeT{+i}:
              do M<String>:
                r : U32 <- find.t(i)
                ts : List<&2, String> <- tag.set(i)
                return "Code#" ++ U32.show(r) ++ tags.show(ts)
            case CapT{+i}:
              do M<String>:
                r : U32 <- find.t(i)
                return "Cap#" ++ U32.show(r)
            case PairT{b1, t1, b2, t2}:
              do M<String>:
                sa : String <- deep.show(f, ds(t1, (d - 1 : U32)))
                sb : String <- deep.show(f, ds(t2, (d - 1 : U32)))
                return "(" ++ sa ++ ", " ++ sb ++ ")"

def mismatch(+loc: Lc.Loc, +mode: String, +a: Tau, +b: Tau) -> M(List<&2, W>):
  do M<List<&2, W>>:
    da : String <- deep.show(64n, ds(a, 5))
    db : String <- deep.show(64n, ds(b, 5))
    M.fail(List<&2, W>, TypeMismatch{loc, describe(a) ++ " vs " ++ describe(b) ++ " [mode "
      ++ mode.show(mode) ++ "; " ++ da ++ " ||| " ++ db ++ "]"})

def join.tags(+loc: Lc.Loc, +i: U32, +j: U32, rest: List<&2, W>) -> M(List<&2, W>):
  do M<List<&2, W>>:
    ps : List<&2, SP> <- union.tags(i, j)
    return sigs(ps, loc, rest)

def cap.seen(seen: Bool, +r: U32, +vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, +t: Tau, rest: List<&2, W>) -> M(List<&2, W>):
  match seen:
    case True{}:
      M.pure(List<&2, W>, rest)
    case False{}:
      do M<List<&2, W>>:
        +cs : List<&2, TE> <- caps(r)
        return cap.mode(cap.for(mode, cs), cs, r <> vis, mode, loc, t, rest)

# resolveCapT: under a dispatch mode the package holds, that tag's capture
# is meant; otherwise every capture the package holds must fit.
def cap.resolve(+vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, +i: U32, +t: Tau, rest: List<&2, W>) -> M(List<&2, W>):
  do M<List<&2, W>>:
    +r : U32 <- find.t(i)
    cap.seen(member(vis, r), r, vis, mode, loc, t, rest)

# unifyTauAt, on walked types: its immediate effect, then the work left.
def walked(+vis: List<&2, U32>, +mode: String, +loc: Lc.Loc, a: Tau, b: Tau, rest: List<&2, W>) -> M(List<&2, W>):
  match a:
    case VarT{+i}:
      match b:
        case VarT{+j}:
          same.var(U32.is_eq(i, j), loc, i, j, rest)
        case other:
          bind.var(loc, i, other, rest)
    case DataT{}:
      match b:
        case VarT{+j}:
          bind.var(loc, j, DataT{}, rest)
        case DataT{}:
          M.pure(List<&2, W>, rest)
        case CapT{+j}:
          cap.resolve(vis, mode, loc, j, DataT{}, rest)
        case PairT{b1, t1, b2, t2}:
          M.pure(List<&2, W>, WColl{vis, mode, loc, Sig{b1, t1}} <> WColl{vis, mode, loc, Sig{b2, t2}} <> rest)
        case other:
          mismatch(loc, mode, DataT{}, other)
    case CodeT{+i}:
      match b:
        case VarT{+j}:
          bind.var(loc, j, CodeT{i}, rest)
        case CodeT{+j}:
          join.tags(loc, i, j, rest)
        case CapT{+j}:
          cap.resolve(vis, mode, loc, j, CodeT{i}, rest)
        case other:
          mismatch(loc, mode, CodeT{i}, other)
    case CapT{+i}:
      match b:
        case VarT{+j}:
          bind.var(loc, j, CapT{i}, rest)
        case CapT{+j}:
          join.tags(loc, i, j, rest)
        case other:
          cap.resolve(vis, mode, loc, i, other, rest)
    case PairT{+a1, +s1, +a2, +s2}:
      match b:
        case VarT{+j}:
          bind.var(loc, j, PairT{a1, s1, a2, s2}, rest)
        case CapT{+j}:
          cap.resolve(vis, mode, loc, j, PairT{a1, s1, a2, s2}, rest)
        case PairT{b1, t1, b2, t2}:
          M.pure(List<&2, W>, WSig{vis, mode, loc, Sig{a1, s1}, Sig{b1, t1}} <> WSig{vis, mode, loc, Sig{a2, s2}, Sig{b2, t2}} <> rest)
        case DataT{}:
          M.pure(List<&2, W>, WColl{vis, mode, loc, Sig{a1, s1}} <> WColl{vis, mode, loc, Sig{a2, s2}} <> rest)
        case other:
          mismatch(loc, mode, PairT{a1, s1, a2, s2}, other)

def unify.step(w: W, rest: List<&2, W>) -> M(List<&2, W>):
  match w:
    case WSig{vis, mode, loc, a, b}:
      match a b:
        case Sig{+ba, ta} Sig{+bb, tb}:
          do M<List<&2, W>>:
            u : Unit <- union.b(ba, bb)
            return WTau{vis, mode, loc, ta, tb} <> rest
    case WTau{+vis, +mode, +loc, a, b}:
      do M<List<&2, W>>:
        wa : Tau <- walk(a)
        wb : Tau <- walk(b)
        walked(vis, mode, loc, wa, wb, rest)
    case WColl{vis, mode, +loc, s}:
      match s:
        case Sig{+b, t}:
          do M<List<&2, W>>:
            changed : Bool <- constrain(b, ForcedZero{Blame{loc, "component of a data pair is unboxed data"}})
            return WTau{vis, mode, loc, t, DataT{}} <> rest

def unify.go(fuel: Nat, ws: List<&2, W>) -> M(Unit):
  match fuel:
    case 0n:
      M.fail(Unit, Internal{"unification ran out of steps"})
    case 1n+f:
      match ws:
        case Nil{}:
          M.pure(Unit, Unit{})
        case Con{w, rest}:
          do M<Unit>:
            next : List<&2, W> <- unify.step(w, rest)
            unify.go(f, next)

# unifySigmaAt with an empty visited set.
def unify.at(+mode: String, +loc: Lc.Loc, a: Sig, b: Sig) -> M(Unit):
  unify.go(U32.to_nat(4294967295), [WSig{[], mode, loc, a, b}])

# unifySigma
def unify(+loc: Lc.Loc, a: Sig, b: Sig) -> M(Unit):
  unify.at("", loc, a, b)

# Env usage (envUsageL, contraction)
# ----------------------------------

def pair.of(+loc: Lc.Loc, +sa: Sig, +sb: Sig, w: Tau) -> M(Sig):
  match w:
    case CodeT{+i}:
      do M<Sig>:
        p : U32 <- package(i, sb)
        plain(loc, "pair constructor is locally unboxed", PairT{sig.b(sa), sig.t(sa), sig.b(sb), CapT{p}})
    case _:
      plain(loc, "pair constructor is locally unboxed", PairT{sig.b(sa), sig.t(sa), sig.b(sb), sig.t(sb)})

# envOccurrence
def occurrence(+ctx: Ctx, +paths: Paths, +loc: Lc.Loc) -> M(Sig):
  match ctx paths:
    case Ctx{+bang, +tau, depth} Paths{here, glob}:
      do M<Sig>:
        u : Unit <- leaf.add(glob)
        +d : U32 <- fresh()
        slack : U32 <- fresh()
        u2 : Unit <- sum.eq(loc, "env occurrence depth = domain bang + slack", [bang, slack], d)
        u3 : Unit <- sum.eq(loc, "env occurrence depth matches its path boxes", here, d)
        b : U32 <- forced.zero(Blame{loc, "variable occurrence is locally unboxed"})
        return Sig{b, tau}

def leaf.code(+paths: Paths, +loc: Lc.Loc, +tag: String, +what: String) -> M(Sig):
  match paths:
    case Paths{here, glob}:
      do M<Sig>:
        u : Unit <- leaf.add(glob)
        ct : Tau <- fresh.code([tag])
        plain(loc, what, ct)

# viewNode (node) and intrinsic, as one.
def gen(+fuel: Nat, node: Bool, +ctx: Ctx, +paths: Paths, +t: Lf.L) -> M(Sig):
  match fuel:
    case 0n:
      M.fail(Sig, Internal{"term too deep"})
    case 1n+f:
      match node:
        case True{}:
          do M<Sig>:
            +w : U32 <- fresh()
            +si : Sig <- gen(f, False{}, ctx, paths.in(w, paths), t)
            +v : U32 <- fresh()
            u : Unit <- sum.eq(l.loc(t), "view bangs = edge boxes + intrinsic bangs", [w, sig.b(si)], v)
            return Sig{v, sig.t(si)}
        case False{}:
          match t:
            case Lf.LZero{+loc}:
              do M<Sig>:
                u : Unit <- leaf.add(paths.glob(paths))
                plain(loc, "Zero is an unboxed value", DataT{})
            case Lf.LPair{+loc, a, b}:
              do M<Sig>:
                +sa : Sig <- gen(f, True{}, ctx, paths, a)
                +sb : Sig <- gen(f, True{}, ctx, paths, b)
                w : Tau <- walk(sig.t(sa))
                pair.of(loc, sa, sb, w)
            case Lf.LEnv{+loc}:
              occurrence(ctx, paths, loc)
            case Lf.LUnsized{+loc, tok}:
              occurrence(ctx, paths, loc)
            case Lf.LRef{+loc, h}:
              leaf.code(paths, loc, "0" ++ h, "code constant is an unboxed value")
            case Lf.LSetEnv{+loc, x}:
              do M<Sig>:
                sx : Sig <- gen(f, True{}, ctx, paths, x)
                +si : Sig <- fresh.sig()
                +so : Sig <- fresh.sig()
                +fnT : Tau <- fresh.tau()
                fnB : U32 <- forced.zero(Blame{loc, "applied function must be unboxed"})
                pairB : U32 <- fresh()
                u : Unit <- unify(loc, sx, Sig{pairB, PairT{fnB, fnT, sig.b(si), sig.t(si)}})
                u2 : Unit <- site.add(Site{fnT, si, so, paths.glob(paths), ctx.depth(ctx), loc, []})
                return so
            case Lf.LGate{+loc}:
              leaf.code(paths, loc, "1", "gate is an unboxed value")
            case Lf.LLeft{+loc, x}:
              do M<Sig>:
                sx : Sig <- gen(f, True{}, ctx, paths, x)
                +sl : Sig <- fresh.sig()
                +sr : Sig <- fresh.sig()
                pb : U32 <- fresh()
                u : Unit <- unify(loc, sx, Sig{pb, PairT{sig.b(sl), sig.t(sl), sig.b(sr), sig.t(sr)}})
                return sl
            case Lf.LRight{+loc, x}:
              do M<Sig>:
                sx : Sig <- gen(f, True{}, ctx, paths, x)
                +sl : Sig <- fresh.sig()
                +sr : Sig <- fresh.sig()
                pb : U32 <- fresh()
                u : Unit <- unify(loc, sx, Sig{pb, PairT{sig.b(sl), sig.t(sl), sig.b(sr), sig.t(sr)}})
                return sr
            case Lf.LAbort{+loc}:
              leaf.code(paths, loc, "3", "abort is an unboxed value")
            case Lf.LCheck{loc, cloc, tc, c}:
              gen(f, False{}, ctx, paths, c)

# viewNode
def view(+ctx: Ctx, +paths: Paths, +t: Lf.L) -> M(Sig):
  gen(U32.to_nat(4294967295), True{}, ctx, paths, t)

# Sorted tag lists
# ----------------

def ft.class(seen: Bool, +r: U32, +vis: List<&2, U32>, rest: List<&2, FT>) -> M(List<&2, FT>):
  match seen:
    case True{}:
      M.pure(List<&2, FT>, rest)
    case False{}:
      do M<List<&2, FT>>:
        cs : List<&2, TE> <- caps(r)
        return ft.caps(cs, r <> vis, rest)

# fnTagsOfCaptures: the code a capture position can hold, when it is
# applied.
def fn.tags.go(fuel: Nat, js: List<&2, FT>, +acc: List<&2, String>) -> M(List<&2, String>):
  match fuel:
    case 0n:
      M.pure(List<&2, String>, acc)
    case 1n+f:
      match js:
        case Nil{}:
          M.pure(List<&2, String>, acc)
        case Con{j, rest}:
          match j:
            case FtClass{+vis, +i}:
              do M<List<&2, String>>:
                +r : U32 <- find.t(i)
                next : List<&2, FT> <- ft.class(member(vis, r), r, vis, rest)
                fn.tags.go(f, next, acc)
            case FtCap{vis, cap}:
              match cap:
                case Some{s}:
                  do M<List<&2, String>>:
                    w : Tau <- walk(sig.t(s))
                    fn.tags.go(f, FtWalked{vis, w} <> rest, acc)
                case None{}:
                  fn.tags.go(f, rest, acc)
            case FtWalked{vis, w}:
              match w:
                case CodeT{+k}:
                  do M<List<&2, String>>:
                    ts : List<&2, String> <- tag.set(k)
                    fn.tags.go(f, rest, both(acc, ts))
                case CapT{+k}:
                  fn.tags.go(f, FtClass{vis, k} <> rest, acc)
                case _:
                  fn.tags.go(f, rest, acc)

def fn.tags(+i: U32) -> M(List<&2, String>):
  fn.tags.go(U32.to_nat(4294967295), [FtClass{[], i}], [])

def dup.constrain(d: Maybe<&2, Dup>, +b: U32, +pre: String, +post: String) -> M(Unit):
  match d:
    case Some{x}:
      match x:
        case Dup{path, loc}:
          do M<Unit>:
            changed : Bool <- constrain(b, ForcedLevel{1, Blame{loc, pre ++ steps.show(path) ++ post}})
            return Unit{}
    case None{}:
      M.pure(Unit, Unit{})

# A body walked at a dispatch site (captureTemplate's walk).
def derive(+glob: List<&2, U32>, +depth: U32, +fi: U32, +body: Lf.L) -> M(Der):
  do M<Der>:
    +b : U32 <- fresh()
    +t : Tau <- fresh.tau()
    u : Unit <- dup.constrain(contraction(usage(body, "", Map.new(&2, Use))), b, "env path ", " duplicated in " ++ E.fi.show(fi))
    s : Sig <- view(Ctx{b, t, (depth + 1 : U32)}, Paths{[], glob}, body)
    return Der{b, t, s}

# The first derivation of a body records how many variables it minted; a
# later one is refused when that many would reach the budget, as copying
# the Haskell's template is.
def derive.first(+h: String, +glob: List<&2, U32>, +depth: U32, +fi: U32, +body: Lf.L) -> M(Der):
  do M<Der>:
    +v0 : U32 <- next.get()
    +d : Der <- derive(glob, depth, fi, body)
    v1 : U32 <- next.get()
    u : Unit <- sizes.put(h, (v1 - v0 : U32))
    return d

def derive.again.at(over: Bool, +glob: List<&2, U32>, +depth: U32, +fi: U32, +body: Lf.L) -> M(Der):
  match over:
    case True{}:
      M.fail(Der, GaveUp{"constraint variable budget (2000000) exceeded; the dispatch structure is likely exploding"})
    case False{}:
      derive(glob, depth, fi, body)

def derive.again(+h: String, +glob: List<&2, U32>, +depth: U32, +fi: U32, +body: Lf.L) -> M(Der):
  do M<Der>:
    size : U32 <- sizes.get(h)
    base : U32 <- next.get()
    derive.again.at(U32.is_ge((base + size : U32), var.budget()), glob, depth, fi, body)

def derive.pick(first: Bool, +h: String, +glob: List<&2, U32>, +depth: U32, +fi: U32, +body: Lf.L) -> M(Der):
  match first:
    case True{}:
      derive.first(h, glob, depth, fi, body)
    case False{}:
      derive.again(h, glob, depth, fi, body)

def dispatch.derived(+tag: String, +env: Sig, +res: Sig, +loc: Lc.Loc, d: Der) -> M(Unit):
  match d:
    case Der{b, t, s}:
      do M<Unit>:
        u : Unit <- unify.at(tag, loc, env, Sig{b, t})
        unify(loc, res, s)

def dispatch.counted(over: Bool, +count: U32, +h: String, +tag: String, +site: Site, +b: Lf.Body) -> M(Unit):
  match over:
    case True{}:
      M.fail(Unit, GaveUp{"polyvariance budget: body " ++ E.fi.show(body.fi(b)) ++ " needed more than 16384 derivations (dispatch structure likely exploding)"})
    case False{}:
      match site:
        case Site{fn, +env, +res, +glob, +depth, +loc, done}:
          do M<Unit>:
            u : Unit <- insts.put(h, (count + 1 : U32))
            d : Der <- derive.pick(U32.is_eq(count, 0), h, glob, depth, body.fi(b), body.l(b))
            dispatch.derived(tag, env, res, loc, d)

def dispatch.found(r: Map<&2, Lf.Body> & Bool, +h: String, +tag: String, +site: Site) -> M(Unit):
  (bodies, found) = r
  match found:
    case True{}:
      do M<Unit>:
        +count : U32 <- insts.get(h)
        +b : Lf.Body = Pair.snd(Map<&2, Lf.Body>, Lf.Body, Map.get(Lf.Body, Lf.Body{0, Lf.LZero{Lc.Unknown{}}}, bodies, h))
        dispatch.counted(U32.is_ge(count, poly.cap()), count, h, tag, site, b)
    case False{}:
      M.fail(Unit, Internal{"dispatched code not in the DeferMap " ++ h})

def dispatch.code(deep: Bool, +bodies: Map<&2, Lf.Body>, +h: String, +tag: String, +site: Site, +loc: Lc.Loc) -> M(Unit):
  match deep:
    case True{}:
      M.fail(Unit, GaveUp{"code dispatch depth exceeded 1024 (unbounded self-application?): " ++ Lf.loc.show(loc, False{})})
    case False{}:
      dispatch.found(Map.has(&2, Lf.Body, bodies, h), h, tag, site)

# dispatchTag: the constraints of applying one tag at one site.
def dispatch(+bodies: Map<&2, Lf.Body>, +site: Site, +tag: String) -> M(Unit):
  match site:
    case Site{fn, +env, +res, glob, +depth, +loc, done}:
      match tag:
        case SCon{Chr{48}, +h}:
          dispatch.code(U32.is_ge(depth, depth.cap()), bodies, h, tag, site, loc)
        case SCon{Chr{49}, r}:
          do M<Unit>:
            scr : U32 <- forced.zero(Blame{loc, "gate scrutinee must be unboxed data"})
            u : Unit <- unify(loc, env, Sig{scr, DataT{}})
            ct : Tau <- fresh.code(["2"])
            gfn : Sig <- plain(loc, "gate switch function is locally unboxed", ct)
            unify(loc, res, gfn)
        case SCon{Chr{50}, r}:
          do M<Unit>:
            +se : Sig <- fresh.sig()
            +st : Sig <- fresh.sig()
            bb : U32 <- fresh()
            u : Unit <- unify(loc, env, Sig{bb, PairT{sig.b(se), sig.t(se), sig.b(st), sig.t(st)}})
            u2 : Unit <- unify(loc, res, se)
            unify(loc, res, st)
        case SCon{Chr{51}, r}:
          do M<Unit>:
            ct : Tau <- fresh.code(["4"])
            cont : Sig <- plain(loc, "abort continuation is locally unboxed", ct)
            unify(loc, res, cont)
        case _:
          unify(loc, env, res)

def dispatch.all(+bodies: Map<&2, Lf.Body>, +site: Site, ts: List<&2, String>) -> M(Unit):
  match ts:
    case Nil{}:
      M.pure(Unit, Unit{})
    case Con{t, rest}:
      do M<Unit>:
        u : Unit <- dispatch(bodies, site, t)
        dispatch.all(bodies, site, rest)

def dispatch.new.at(none: Bool, +bodies: Map<&2, Lf.Body>, +k: U32, +site: Site, +tags: List<&2, String>, new: List<&2, String>) -> M(Bool):
  match none:
    case True{}:
      M.pure(Bool, False{})
    case False{}:
      do M<Bool>:
        u : Unit <- site.put(k, site.with.done(site, both(site.done(site), tags)))
        u2 : Unit <- dispatch.all(bodies, site, new)
        return True{}

# dispatchNew: the tags this site has not dispatched yet; marked first.
def dispatch.new(+bodies: Map<&2, Lf.Body>, +k: U32, +site: Site, +tags: List<&2, String>) -> M(Bool):
  +new = diff(tags, site.done(site))
  dispatch.new.at(List.is_empty(&2, String, new), bodies, k, site, tags, new)

def site.walked(+bodies: Map<&2, Lf.Body>, +k: U32, +site: Site, w: Tau) -> M(Bool):
  match w:
    case CodeT{+i}:
      do M<Bool>:
        +ts : List<&2, String> <- tag.set(i)
        dispatch.new(bodies, k, site, ts)
    case CapT{+i}:
      do M<Bool>:
        +ts : List<&2, String> <- fn.tags(i)
        dispatch.new(bodies, k, site, ts)
    case PairT{b1, t1, b2, t2}:
      M.fail(Bool, TypeMismatch{site.loc(site), "applied value is pair, not code"})
    case _:
      M.pure(Bool, False{})

def site.resolve(+bodies: Map<&2, Lf.Body>, +k: U32) -> M(Bool):
  do M<Bool>:
    +site : Site <- site.get(k)
    w : Tau <- walk(site.fn(site))
    site.walked(bodies, k, site, w)

# One round over the sites there were when it began.
def round(fuel: Nat, +bodies: Map<&2, Lf.Body>, +k: U32, +n: U32, more: Bool, +changed: Bool) -> M(Bool):
  match fuel:
    case 0n:
      M.pure(Bool, changed)
    case 1n+f:
      match more:
        case False{}:
          M.pure(Bool, changed)
        case True{}:
          do M<Bool>:
            c : Bool <- site.resolve(bodies, k)
            round(f, bodies, (k + 1 : U32), n, U32.is_lt((k + 1 : U32), n), changed || c)

def applies.go(fuel: Nat, +bodies: Map<&2, Lf.Body>, +r: U32, more: Bool, over: Bool) -> M(Unit):
  match fuel:
    case 0n:
      M.pure(Unit, Unit{})
    case 1n+f:
      match more:
        case False{}:
          M.pure(Unit, Unit{})
        case True{}:
          match over:
            case True{}:
              M.fail(Unit, GaveUp{"application dispatch did not converge"})
            case False{}:
              do M<Unit>:
                +n : U32 <- nsites.get()
                changed : Bool <- round(U32.to_nat(n), bodies, 0, n, U32.is_lt(0, n), False{})
                applies.go(f, bodies, (r + 1 : U32), changed, U32.is_gt((r + 1 : U32), 10000))

# resolveApplies: dispatch every tag every site's function position holds,
# to a fixpoint.
def applies(+bodies: Map<&2, Lf.Body>) -> M(Unit):
  applies.go(10002n, bodies, 0, True{}, False{})

# Solving
# -------

def roots(ls: List<&2, U32>) -> M(List<&2, U32>):
  match ls:
    case Nil{}:
      M.pure(List<&2, U32>, [])
    case Con{+l, rest}:
      do M<List<&2, U32>>:
        r : U32 <- find.b(l)
        rs : List<&2, U32> <- roots(rest)
        return r <> rs

# resolveEqs: the equations over class roots.
def resolve.eqs(es: List<&2, SumEq>) -> M(List<&2, SumEq>):
  match es:
    case Nil{}:
      M.pure(List<&2, SumEq>, [])
    case Con{e, rest}:
      match e:
        case SumEq{lhs, +rhs, blame}:
          do M<List<&2, SumEq>>:
            ls : List<&2, U32> <- roots(lhs)
            r : U32 <- find.b(rhs)
            more : List<&2, SumEq> <- resolve.eqs(rest)
            return SumEq{ls, r, blame} <> more

# Nothing merges classes while the solver runs, so the equations' roots
# are found once and their classes copied to a table of their own; both
# passes then work on tables, not in the analysis' monad. A derived blame
# is built only when a class keeps it or a conflict names it.

def pr.or(+ch: Bool, r: PR) -> PR:
  match r:
    case PGo{cls, c}:
      PGo{cls, ch || c}
    case PErr{e}:
      PErr{e}

def zero.at(+r: U32, +what: String, +blame: Blame, p: Array<Class> & Class) -> PR:
  (cls, old) = p
  match old:
    case Unrestricted{}:
      PGo{Array.set(Class, cls, r, ForcedZero{derived(what, blame)}), True{}}
    case ForcedZero{z}:
      PGo{cls, False{}}
    case ForcedLevel{n, l}:
      PErr{BoxConflict{l, derived(what, blame)}}

# constrainB to ForcedZero, on a root.
def zero(cls: Array<Class>, +r: U32, +what: String, +blame: Blame) -> PR:
  zero.at(r, what, blame, Array.get(Class, cls, r))

def level.keep(keep: Bool, cls: Array<Class>, +r: U32, +n: U32, +what: String, +blame: Blame) -> PR:
  match keep:
    case True{}:
      PGo{cls, False{}}
    case False{}:
      PGo{Array.set(Class, cls, r, ForcedLevel{n, derived(what, blame)}), True{}}

def level.at(+r: U32, +n: U32, +what: String, +blame: Blame, p: Array<Class> & Class) -> PR:
  (cls, old) = p
  match old:
    case Unrestricted{}:
      PGo{Array.set(Class, cls, r, ForcedLevel{n, derived(what, blame)}), True{}}
    case ForcedZero{z}:
      PErr{BoxConflict{derived(what, blame), z}}
    case ForcedLevel{+la, l}:
      level.keep(U32.is_ge(la, n), cls, r, n, what, blame)

# constrainB to ForcedLevel n, on a root; past the level cap, it gives up.
def level(over: Bool, cls: Array<Class>, +r: U32, +n: U32, +what: String, +blame: Blame) -> PR:
  match over:
    case True{}:
      PErr{GaveUp{"bang level exceeded cap of 4096: " ++ blame.show(derived(what, blame))}}
    case False{}:
      level.at(r, n, what, blame, Array.get(Class, cls, r))

def zero.then(+l: U32, +blame: Blame, r: PR) -> PR:
  match r:
    case PGo{cls, ch}:
      pr.or(ch, zero(cls, l, "summand of an unboxed total", blame))
    case PErr{e}:
      PErr{e}

def zeros(ls: List<&2, U32>, +blame: Blame, r: PR) -> PR:
  match ls:
    case Nil{}:
      r
    case Con{+l, rest}:
      zeros(rest, blame, zero.then(l, blame, r))

def classes.push(cs: List<&2, Class>, q: Array<Class> & Class) -> Array<Class> & List<&2, Class>:
  (cls, c) = q
  (cls, c <> cs)

# The classes of these roots.
def classes(ls: List<&2, U32>, p: Array<Class> & List<&2, Class>) -> Array<Class> & List<&2, Class>:
  match ls:
    case Nil{}:
      (cls, cs) = p
      (cls, List.reverse(&2, Class, cs))
    case Con{l, rest}:
      (cls, cs) = p
      classes(rest, classes.push(cs, Array.get(Class, cls, l)))

# An unboxed total unboxes every summand.
def prop.c1(fz: Bool, +lhs: List<&2, U32>, +blame: Blame, cls: Array<Class>) -> PR:
  match fz:
    case True{}:
      zeros(lhs, blame, PGo{cls, False{}})
    case False{}:
      PGo{cls, False{}}

# Summands all unboxed unbox the total.
def prop.c2(all: Bool, cls: Array<Class>, +rhs: U32, +blame: Blame) -> PR:
  match all:
    case True{}:
      zero(cls, rhs, "all summands unboxed", blame)
    case False{}:
      PGo{cls, False{}}

# The summands' lower bounds bound the total.
def prop.c3(some: Bool, cls: Array<Class>, +rhs: U32, +n: U32, +blame: Blame) -> PR:
  match some:
    case True{}:
      level(U32.is_gt(n, level.cap()), cls, rhs, n, "sum of summand lower bounds", blame)
    case False{}:
      PGo{cls, False{}}

# A boxed total's only boxable summand takes its level.
def prop.c4(frees: List<&2, U32>, ri: Class, cls: Array<Class>, +blame: Blame) -> PR:
  match frees:
    case Con{+lone, rest}:
      match rest:
        case Nil{}:
          match ri:
            case ForcedLevel{+n, b}:
              level(U32.is_gt(n, level.cap()), cls, lone, n, "only boxable summand", blame)
            case _:
              PGo{cls, False{}}
        case _:
          PGo{cls, False{}}
    case Nil{}:
      PGo{cls, False{}}

def step.ri2(frees: List<&2, U32>, +blame: Blame, p: Array<Class> & Class) -> PR:
  (cls, ri) = p
  prop.c4(frees, ri, cls, blame)

def step.c4(+lhs: List<&2, U32>, +rhs: U32, +blame: Blame, +cs: List<&2, Class>, r: PR) -> PR:
  match r:
    case PGo{cls, ch}:
      pr.or(ch, step.ri2(boxable(lhs, cs), blame, Array.get(Class, cls, rhs)))
    case PErr{e}:
      PErr{e}

def step.c3(+lhs: List<&2, U32>, +rhs: U32, +blame: Blame, +cs: List<&2, Class>, r: PR) -> PR:
  match r:
    case PGo{cls, ch}:
      +n = sum.lower(cs)
      step.c4(lhs, rhs, blame, cs, pr.or(ch, prop.c3(U32.is_gt(n, 0), cls, rhs, n, blame)))
    case PErr{e}:
      PErr{e}

def step.cs(+lhs: List<&2, U32>, +rhs: U32, +blame: Blame, +c1: Bool, p: Array<Class> & List<&2, Class>) -> PR:
  (cls, +cs) = p
  step.c3(lhs, rhs, blame, cs, pr.or(c1, prop.c2(all.fz(cs), cls, rhs, blame)))

def step.c1(+lhs: List<&2, U32>, +rhs: U32, +blame: Blame, r: PR) -> PR:
  match r:
    case PGo{cls, c1}:
      step.cs(lhs, rhs, blame, c1, classes(lhs, (cls, [])))
    case PErr{e}:
      PErr{e}

def step.ri(+lhs: List<&2, U32>, +rhs: U32, +blame: Blame, p: Array<Class> & Class) -> PR:
  (cls, ri) = p
  step.c1(lhs, rhs, blame, prop.c1(is.fz(ri), lhs, blame, cls))

# One equation's propagation step: whether any class changed.
def step(e: SumEq, cls: Array<Class>) -> PR:
  match e:
    case SumEq{+lhs, +rhs, +blame}:
      step.ri(lhs, rhs, blame, Array.get(Class, cls, rhs))

def prop.round(es: List<&2, SumEq>, r: PR) -> PR:
  match es:
    case Nil{}:
      r
    case Con{e, rest}:
      match r:
        case PGo{cls, ch}:
          prop.round(rest, pr.or(ch, step(e, cls)))
        case PErr{x}:
          PErr{x}

# propagate: zero-forcings and lower bounds through the sums, round after
# round to a fixpoint, within fuel rounds.
def rounds(fuel: Nat, +es: List<&2, SumEq>, r: PR) -> PR:
  match fuel:
    case 0n:
      match r:
        case PGo{cls, changed}:
          match changed:
            case True{}:
              PErr{GaveUp{"constraint propagation did not converge"}}
            case False{}:
              PGo{cls, False{}}
        case PErr{e}:
          PErr{e}
    case 1n+f:
      match r:
        case PGo{cls, changed}:
          match changed:
            case True{}:
              rounds(f, es, prop.round(es, PGo{cls, False{}}))
            case False{}:
              PGo{cls, False{}}
        case PErr{e}:
          PErr{e}

# Assignment (assignValues)
# -------------------------

def give.up(+what: String, b: Blame) -> Err:
  GaveUp{what ++ ": " ++ blame.show(b)}

def a.plus(+acc: U32, q: Array<U32> & U32) -> Array<U32> & U32:
  (vals, v) = q
  (vals, (acc + v : U32))

# The sum of these roots' values.
def a.sum(ls: List<&2, U32>, p: Array<U32> & U32) -> Array<U32> & U32:
  match ls:
    case Nil{}:
      p
    case Con{l, rest}:
      (vals, acc) = p
      a.sum(rest, a.plus(acc, vals[l]))

def a.free(+fs: List<&2, U32>, +l: U32, q: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  (zf, z) = q
  (zf, Bool.pick(List<&2, U32>, U32.is_eq(z, 0), l <> fs, fs))

# The summands that may be boxed (in no particular order: the pick is a
# minimum).
def a.frees(ls: List<&2, U32>, p: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match ls:
    case Nil{}:
      p
    case Con{+l, rest}:
      (zf, fs) = p
      a.frees(rest, a.free(fs, l, zf[l]))

def a.cmp(+l: U32, q: Array<U32> & U32, k: Pk) -> Array<U32> & Pk:
  (cnt, +c) = q
  match k:
    case Pk{+best, +bc}:
      +better = U32.is_lt(c, bc) || (U32.is_eq(c, bc) && U32.is_lt(l, best))
      (cnt, Pk{Bool.pick(U32, better, l, best), Bool.pick(U32, better, c, bc)})

# minimumBy on (count, root): the summand in the fewest equations, then the
# lowest.
def a.pick(ls: List<&2, U32>, p: Array<U32> & Pk) -> Array<U32> & Pk:
  match ls:
    case Nil{}:
      p
    case Con{+l, rest}:
      (cnt, k) = p
      a.pick(rest, a.cmp(l, cnt[l], k))

def adjust.set(over: Bool, +p: U32, +v: U32, +blame: Blame, vals: Array<U32>, zf: Array<U32>, cnt: Array<U32>) -> AR:
  match over:
    case True{}:
      AErr{give.up("assignment exceeded level cap", blame)}
    case False{}:
      AGo{vals[p] <- v, zf, cnt, True{}}

def adjust.raise(+blame: Blame, +short: U32, +p: U32, zf: Array<U32>, cnt: Array<U32>, q: Array<U32> & U32) -> AR:
  (vals, v) = q
  +v2 = (v + short : U32)
  adjust.set(U32.is_gt(v2, level.cap()), p, v2, blame, vals, zf, cnt)

def adjust.pick(+blame: Blame, +short: U32, vals: Array<U32>, zf: Array<U32>, p: Array<U32> & Pk) -> AR:
  (cnt, k) = p
  match k:
    case Pk{+best, bc}:
      adjust.raise(blame, short, best, zf, cnt, vals[best])

def adjust.first(+f: U32, q: Array<U32> & U32) -> Array<U32> & Pk:
  (cnt, c) = q
  (cnt, Pk{f, c})

# The sum falls short: raise one free summand by the difference.
def adjust.lt(+blame: Blame, +short: U32, vals: Array<U32>, cnt: Array<U32>, p: Array<U32> & List<&2, U32>) -> AR:
  (zf, fs) = p
  match fs:
    case Nil{}:
      AErr{give.up("no boxable position to absorb required boxes", blame)}
    case Con{+f, rest}:
      adjust.pick(blame, short, vals, zf, a.pick(rest, adjust.first(f, cnt[f])))

def adjust.over(zero: Bool, over: Bool, +rhs: U32, +sum: U32, +blame: Blame, vals: Array<U32>, zf: Array<U32>, cnt: Array<U32>) -> AR:
  match zero:
    case True{}:
      AErr{give.up("sum exceeds an unboxed total", blame)}
    case False{}:
      match over:
        case True{}:
          AErr{give.up("assignment exceeded level cap", blame)}
        case False{}:
          AGo{vals[rhs] <- sum, zf, cnt, True{}}

# The sum exceeds the total: raise the total.
def adjust.gt(+rhs: U32, +blame: Blame, +sum: U32, vals: Array<U32>, cnt: Array<U32>, p: Array<U32> & U32) -> AR:
  (zf, z) = p
  adjust.over(U32.is_ne(z, 0), U32.is_gt(sum, level.cap()), rhs, sum, blame, vals, zf, cnt)

def adjust.cmp(c: Cmp, +lhs: List<&2, U32>, +rhs: U32, +blame: Blame, +sum: U32, +t: U32, vals: Array<U32>, zf: Array<U32>, cnt: Array<U32>) -> AR:
  match c:
    case EQ{}:
      AGo{vals, zf, cnt, False{}}
    case GT{}:
      adjust.gt(rhs, blame, sum, vals, cnt, zf[rhs])
    case LT{}:
      adjust.lt(blame, (t - sum : U32), vals, cnt, a.frees(lhs, (zf, [])))

def adjust.t(+lhs: List<&2, U32>, +rhs: U32, +blame: Blame, +sum: U32, zf: Array<U32>, cnt: Array<U32>, p: Array<U32> & U32) -> AR:
  (vals, +t) = p
  adjust.cmp(U32.cmp(sum, t), lhs, rhs, blame, sum, t, vals, zf, cnt)

def adjust.sum(+lhs: List<&2, U32>, +rhs: U32, +blame: Blame, zf: Array<U32>, cnt: Array<U32>, p: Array<U32> & U32) -> AR:
  (vals, +sum) = p
  adjust.t(lhs, rhs, blame, sum, zf, cnt, vals[rhs])

# adjust: raise the total, or one summand, so that one equation holds.
def adjust(e: SumEq, vals: Array<U32>, zf: Array<U32>, cnt: Array<U32>) -> AR:
  match e:
    case SumEq{+lhs, +rhs, +blame}:
      adjust.sum(lhs, rhs, blame, zf, cnt, a.sum(lhs, (vals, 0)))

def ar.or(+ch: Bool, r: AR) -> AR:
  match r:
    case AGo{vals, zf, cnt, c}:
      AGo{vals, zf, cnt, ch || c}
    case AErr{e}:
      AErr{e}

def a.round(es: List<&2, SumEq>, r: AR) -> AR:
  match es:
    case Nil{}:
      r
    case Con{e, rest}:
      match r:
        case AGo{vals, zf, cnt, ch}:
          a.round(rest, ar.or(ch, adjust(e, vals, zf, cnt)))
        case AErr{x}:
          AErr{x}

def a.loop(fuel: Nat, +es: List<&2, SumEq>, r: AR) -> AR:
  match fuel:
    case 0n:
      match r:
        case AGo{vals, zf, cnt, changed}:
          match changed:
            case True{}:
              AErr{GaveUp{"assignment did not converge"}}
            case False{}:
              AGo{vals, zf, cnt, False{}}
        case AErr{e}:
          AErr{e}
    case 1n+f:
      match r:
        case AGo{vals, zf, cnt, changed}:
          match changed:
            case True{}:
              a.loop(f, es, a.round(es, AGo{vals, zf, cnt, False{}}))
            case False{}:
              AGo{vals, zf, cnt, False{}}
        case AErr{e}:
          AErr{e}

def verify.one(ok: Bool, b: Blame) -> Maybe<&2, Err>:
  match ok:
    case True{}:
      None{}
    case False{}:
      Some{GaveUp{"assignment verification failed: " ++ blame.show(b)}}

def holds.at(+blame: Blame, +sum: U32, p: Array<U32> & U32) -> Array<U32> & Maybe<&2, Err>:
  (vals, t) = p
  (vals, verify.one(U32.is_eq(sum, t), blame))

def holds.sum(+rhs: U32, +blame: Blame, p: Array<U32> & U32) -> Array<U32> & Maybe<&2, Err>:
  (vals, +sum) = p
  holds.at(blame, sum, vals[rhs])

def holds(e: SumEq, vals: Array<U32>) -> Array<U32> & Maybe<&2, Err>:
  match e:
    case SumEq{lhs, +rhs, +blame}:
      holds.sum(rhs, blame, a.sum(lhs, (vals, 0)))

# Every equation holds exactly.
def verify(es: List<&2, SumEq>, p: Array<U32> & Maybe<&2, Err>) -> Maybe<&2, Err>:
  match es:
    case Nil{}:
      (vals, m) = p
      m
    case Con{e, rest}:
      (vals, m) = p
      match m:
        case Some{x}:
          Some{x}
        case None{}:
          verify(rest, holds(e, vals))

def a.done(+es: List<&2, SumEq>, r: AR) -> Maybe<&2, Err>:
  match r:
    case AGo{vals, zf, cnt, changed}:
      verify(es, (vals, None{}))
    case AErr{e}:
      Some{e}

def a.inc(+l: U32, p: Array<U32> & U32) -> Array<U32>:
  (cnt, c) = p
  cnt[l] <- (c + 1 : U32)

def a.count.one(ls: List<&2, U32>, cnt: Array<U32>) -> Array<U32>:
  match ls:
    case Nil{}:
      cnt
    case Con{+l, rest}:
      a.count.one(rest, a.inc(l, cnt[l]))

# How often each root is a summand.
def a.count(es: List<&2, SumEq>, cnt: Array<U32>) -> Array<U32>:
  match es:
    case Nil{}:
      cnt
    case Con{e, rest}:
      match e:
        case SumEq{lhs, rhs, blame}:
          a.count(rest, a.count.one(lhs, cnt))

def a.init.got(+r: U32, vals: Array<U32>, zf: Array<U32>, p: Array<Class> & Class) -> AI:
  (cls, +c) = p
  AI{cls, vals[r] <- lower(c), zf[r] <- Bool.to_u32(is.fz(c))}

# Each root's value starts at its lower bound.
def a.init(rs: List<&2, U32>, ai: AI) -> AI:
  match rs:
    case Nil{}:
      ai
    case Con{+r, rest}:
      match ai:
        case AI{cls, vals, zf}:
          a.init(rest, a.init.got(r, vals, zf, Array.get(Class, cls, r)))

def assign.with(+es: List<&2, SumEq>, +d: Nat, ai: AI) -> Maybe<&2, Err>:
  match ai:
    case AI{cls, vals, zf}:
      a.done(es, a.loop(U32.to_nat((U32.from_nat(List.length(&2, SumEq, es)) * 4 + 16 : U32)), es,
        AGo{vals, zf, a.count(es, Array.new(U32, d, 0)), True{}}))

# assignValues: concrete bangs for every equation, from the lower bounds,
# greedily raising free summands. Only whether it succeeds matters here.
def assign(+es: List<&2, SumEq>, +d: Nat, r: PR) -> Maybe<&2, Err>:
  match r:
    case PGo{cls, changed}:
      assign.with(es, d, a.init(eq.roots(es, []), AI{cls, Array.new(U32, d, 0), Array.new(U32, d, 0)}))
    case PErr{e}:
      Some{e}

# The solver
# ----------

def cls.copy(+r: U32, t: Array<Class>, q: Array<V> & V) -> Array<V> & Array<Class>:
  (vars, x) = q
  (vars, Array.set(Class, t, r, v.cls(x)))

# The roots' classes, in a table of their own.
def table(rs: List<&2, U32>, p: Array<V> & Array<Class>) -> Array<V> & Array<Class>:
  match rs:
    case Nil{}:
      p
    case Con{+r, rest}:
      (vars, t) = p
      table(rest, cls.copy(r, t, Array.get(V, vars, r)))

def solve.done(s: St, m: Maybe<&2, Err>) -> Result<&1, &1, Err, Unit & St>:
  match m:
    case None{}:
      Done{(Unit{}, s)}
    case Some{e}:
      Fail{e}

def solve.with(+rs: List<&2, SumEq>, +d: Nat, sites: Array<Site>, c: C, p: Array<V> & Array<Class>) -> Result<&1, &1, Err, Unit & St>:
  (vars, cls) = p
  solve.done(St{vars, sites, c},
    assign(rs, d, rounds(U32.to_nat((U32.from_nat(List.length(&2, SumEq, rs)) * 4 + 64 : U32)), rs, PGo{cls, True{}})))

def solve.go(+rs: List<&2, SumEq>, s: St) -> Result<&1, &1, Err, Unit & St>:
  match s:
    case St{vars, sites, +c}:
      +d = U32.log2(c.cap(c))
      solve.with(rs, d, sites, c, table(eq.roots(rs, []), (vars, Array.new(Class, d, Unrestricted{}))))

# propagate, then assignValues, over the equations' roots.
def solve() -> M(Unit):
  do M<Unit>:
    es : List<&2, SumEq> <- eqs.get()
    +rs : List<&2, SumEq> <- resolve.eqs(es)
    s => solve.go(rs, s)

# The whole analysis
# ------------------

def main.apply(apply: Bool, +bodies: Map<&2, Lf.Body>, s: Sig) -> M(Unit):
  match apply:
    case True{}:
      do M<Unit>:
        u : Unit <- virtual(s)
        applies(bodies)
    case False{}:
      M.pure(Unit, Unit{})

# The walk of a top-level term over its own env.
def walk.top(+what: String, +term: Lf.L) -> M(Sig):
  do M<Sig>:
    +b : U32 <- fresh()
    +t : Tau <- fresh.tau()
    u : Unit <- dup.constrain(contraction(usage(term, "", Map.new(&2, Use))), b, what ++ " path ", " duplicated")
    view(Ctx{b, t, 0}, Paths{[], []}, term)

# Every dispatch, then the program applied to its input and its dispatches.
def main.apply.all(+bodies: Map<&2, Lf.Body>, apply: Bool, +s: Sig) -> M(Unit):
  do M<Unit>:
    u : Unit <- applies(bodies)
    main.apply(apply, bodies, s)

# analyzeTopWith: a top-level term (the program, or a body standalone) over
# its own env; the program also applied to its input.
def analyze(+bodies: Map<&2, Lf.Body>, apply: Bool, +what: String, +term: Lf.L) -> M(Sig):
  do M<Sig>:
    +s : Sig <- walk.top(what, term)
    u : Unit <- main.apply.all(bodies, apply, s)
    u2 : Unit <- solve()
    return s

# Capture shapes
# --------------

# summarizeBody: whether a body certifies standalone.
def standalone(+bodies: Map<&2, Lf.Body>, b: Lf.Body) -> Bool:
  match b:
    case Lf.Body{fi, body}:
      ran(analyze(bodies, False{}, "env of lifted body " ++ E.fi.show(fi), body)(st.new()))

# summarizeBody's failure: why a body does not certify standalone, if it
# does not.
def summary(+bodies: Map<&2, Lf.Body>, b: Lf.Body) -> Maybe<&2, Err>:
  match b:
    case Lf.Body{fi, body}:
      failure(analyze(bodies, False{}, "env of lifted body " ++ E.fi.show(fi), body)(st.new()))

def deps(+fuel: Nat, +bodies: Map<&2, Lf.Body>, +pre: Map<&2, Bool>, j: DJ) -> DR:
  match fuel:
    case 0n:
      DR{Map.new(&2, Bool), Some{"(too deep)"}}
    case 1n+f:
      match j:
        case DjEnsure{+h, known, memo}:
          match known:
            case True{}:
              DR{memo, None{}}
            case False{}:
              deps(f, bodies, pre, DjChecked{h, deps(f, bodies, pre, DjCheck{refs(body.l(body.of(bodies, h)), []), memo})})
        case DjChecked{+h, r}:
          match r:
            case DR{memo, failed}:
              match failed:
                case Some{d}:
                  DR{Map.set(&2, Bool, memo, h, False{}), None{}}
                case None{}:
                  DR{Map.set(&2, Bool, memo, h, Pair.snd(Map<&2, Bool>, Bool, Map.get(Bool, False{}, pre, h))), None{}}
        case DjCheck{hs, memo}:
          match hs:
            case Nil{}:
              DR{memo, None{}}
            case Con{+h, rest}:
              deps(f, bodies, pre, DjAfter{h, rest, deps(f, bodies, pre, ensure(h, memo))})
        case DjAfter{+h, rest, r}:
          match r:
            case DR{memo, failed}:
              deps(f, bodies, pre, next.of(h, rest, memo.ok(h, memo)))
        case DjNext{ok, h, rest, memo}:
          match ok:
            case True{}:
              deps(f, bodies, pre, DjCheck{rest, memo})
            case False{}:
              DR{memo, Some{h}}
        case DjAll{hs, memo}:
          match hs:
            case Nil{}:
              DR{memo, None{}}
            case Con{+h, rest}:
              deps(f, bodies, pre, DjAllNext{rest, deps(f, bodies, pre, ensure(h, memo))})
        case DjAllNext{hs, r}:
          match r:
            case DR{memo, failed}:
              deps(f, bodies, pre, DjAll{hs, memo})

# withDeps: the first of these dependencies that does not certify, given
# every body's standalone verdict.
def check.deps(+bodies: Map<&2, Lf.Body>, +pre: Map<&2, Bool>, hs: List<&2, String>, memo: Map<&2, Bool>) -> DR:
  deps(U32.to_nat(4294967295), bodies, pre, DjCheck{hs, memo})

def verdicts.go(+fuel: Nat, +bodies: Map<&2, Lf.Body>, +n: U32, one: Bool, +hs: List<&2, String>) -> List<&2, HB>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match one:
        case True{}:
          match hs:
            case Nil{}:
              []
            case Con{+h, rest}:
              [HB{h, standalone(bodies, body.of(bodies, h))}]
        case False{}:
          +k = U32.shr(n)
          +m = (n - k : U32)
          a b = verdicts.go(f, bodies, k, U32.is_le(k, 1), List.take(&2, String, hs, U32.to_nat(k))) verdicts.go(f, bodies, m, U32.is_le(m, 1), List.drop(&2, String, hs, U32.to_nat(k)))
          List.append(&2, HB, a, b)

def verdicts.map(xs: List<&2, HB>, acc: Map<&2, Bool>) -> Map<&2, Bool>:
  match xs:
    case Nil{}:
      acc
    case Con{x, rest}:
      match x:
        case HB{h, ok}:
          verdicts.map(rest, Map.set(&2, Bool, acc, h, ok))

# Every body's standalone verdict (summarizeBody), computed in parallel: a
# balanced fork-join over the bodies in hash order.
def verdicts(+bodies: Map<&2, Lf.Body>) -> Map<&2, Bool>:
  +hs = Map.keys(&2, Lf.Body, bodies)
  +n = U32.from_nat(List.length(&2, String, hs))
  verdicts.map(verdicts.go(U32.to_nat((U32.from_nat(U32.log2(n)) + 3 : U32)), bodies, n, U32.is_le(n, 1), hs), Map.new(&2, Bool))

# The entry points
# ----------------

def main.shape(+bodies: Map<&2, Lf.Body>, +main: Lf.L) -> M(Lf.Shape):
  do M<Lf.Shape>:
    s : Sig <- analyze(bodies, True{}, "program input", main)
    shape(s)

def inferred.at(r: DR, main: Result<&1, &1, Err, Lf.Shape & St>) -> Result<&2, &2, Err, Lf.Shape>:
  match r:
    case DR{memo, failed}:
      match failed:
        case Some{d}:
          Fail{DependencyFailed{d}}
        case None{}:
          main.of(main)

def inferred.with(+bodies: Map<&2, Lf.Body>, +main: Lf.L, +pre: Map<&2, Bool>, r: Result<&1, &1, Err, Lf.Shape & St>) -> Result<&2, &2, Err, Lf.Shape>:
  inferred.at(check.deps(bodies, pre, refs(main, []), Map.new(&2, Bool)), r)

# ealLiftedMain: the program's main shape, or why it does not certify, its
# dependencies first. The bodies' standalone verdicts and the whole
# program's analysis run in parallel.
def inferred(t: Lf.Lifted) -> Result<&2, &2, Err, Lf.Shape>:
  match t:
    case Lf.Lifted{+bodies, +main}:
      pre r = verdicts(bodies) main.shape(bodies, main)(st.new())
      inferred.with(bodies, main, pre, r)

# certifyMain: why the program is not certified, if it is not.
def certify(t: Lf.Lifted) -> Maybe<&2, Err>:
  certified(inferred(t))

# ealGuidance's verdicts: whether each body certifies, its dependencies
# first.
def gated(+bodies: Map<&2, Lf.Body>) -> Map<&2, Bool>:
  dr.memo(deps(U32.to_nat(4294967295), bodies, verdicts(bodies),
    DjAll{Map.keys(&2, Lf.Body, bodies), Map.new(&2, Bool)}))

def main.shapes(+bodies: Map<&2, Lf.Body>, +main: Lf.L) -> M(Map<&2, Lf.Shape>):
  do M<Map<&2, Lf.Shape>>:
    s : Sig <- analyze(bodies, True{}, "program input", main)
    shapes()

def layouts.at(+bodies: Map<&2, Lf.Body>, +pre: Map<&2, Bool>, +m: Map<&2, Lf.Shape>, r: DR) -> Map<&2, Lf.Shape>:
  match r:
    case DR{memo, failed}:
      match failed:
        case Some{d}:
          Map.new(&2, Lf.Shape)
        case None{}:
          layouts.keep(Map.to_list(&2, Lf.Shape, m),
            dr.memo(deps(U32.to_nat(4294967295), bodies, pre, DjAll{Map.keys(&2, Lf.Shape, m), memo})), Map.new(&2, Lf.Shape))

def layouts.with(+bodies: Map<&2, Lf.Body>, +main: Lf.L, +pre: Map<&2, Bool>, +m: Map<&2, Lf.Shape>) -> Map<&2, Lf.Shape>:
  layouts.at(bodies, pre, m, check.deps(bodies, pre, refs(main, []), Map.new(&2, Bool)))

def layouts.ran(+bodies: Map<&2, Lf.Body>, +main: Lf.L, r: Result<&1, &1, Err, Map<&2, Lf.Shape> & St>) -> Map<&2, Lf.Shape>:
  match r:
    case Fail{e}:
      Map.new(&2, Lf.Shape)
    case Done{p}:
      (+m, st) = p
      layouts.with(bodies, main, verdicts(bodies), m)

# ealCaptureLayouts: the capture shape of each closure code the whole
# program builds, for the codes that certify standalone; none when the
# program does not certify. The bodies' verdicts matter only when the
# whole program's analysis succeeds, so only then are they computed.
def layouts(t: Lf.Lifted) -> Map<&2, Lf.Shape>:
  match t:
    case Lf.Lifted{+bodies, +main}:
      layouts.ran(bodies, main, main.shapes(bodies, main)(st.new()))

def st.next(s: St) -> U32:
  match s:
    case St{vars, sites, c}:
      c.next(c)

def ran.u(r: Result<&1, &1, Err, Unit & St>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{p}:
      True{}

def resolved() -> M(List<&2, SumEq>):
  do M<List<&2, SumEq>>:
    es : List<&2, SumEq> <- eqs.get()
    resolve.eqs(es)
