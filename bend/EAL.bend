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
#   before copying, is kept.
# - The unifier is one worklist, popped last in first, so its effects come
#   in the Haskell's depth-first order.
#
# The state is laid out as the IC's net is, in arrays read and written in
# place by direct-style defs; recursion that threads it runs on a stack of
# jobs:
# - A type is one word: its kind in the low three bits (1 a variable, 2 a
#   code class, 3 a capture selection, 4 a pair, 5 data) and above them a
#   variable, or a pair's number in the pairs' table.
# - A tag is one word: a body's rank among the bodies' hashes (the Haskell
#   orders code tags by hash), or, above every rank, the built-ins in the
#   Haskell's Ord Tag order: gate, gate function, abort, abort
#   continuation.
# - A variable has eight words: its type binding (0 when unbound), its
#   bang class's parent plus one (0 at a root), the class (its level times
#   four, plus 0 unrestricted, 1 forced zero, 2 forced level), the class's
#   blame (a number in the blames' table) and its tag class's parent plus
#   one. Before the variables, the table keeps its counters.
# - A failure is kept in the state, the first one only, and every loop
#   stops at it.
# - Branches go on small enumerations (a type's kind, a class merge's
#   outcome) or on Bools, never on a U32's literal values: a U32 case
#   compiles to a test per bit, each with its own copy of the default.

# Types
# -----

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

# Uses of one env path: how many, and where the first was.
type Use is Data:
  Use{+n: U32, +loc: Lc.Loc}

type Dup is Data:
  Dup{+path: String, +loc: Lc.Loc}

# The term the analysis walks: Term3Lifting with every reference by its
# body's rank, and without what the walk ignores (a recursion hole is an
# env occurrence; a checking wrapper keeps only what it wraps).
type A is Data:
  AZero{+loc: Lc.Loc}
  APair{+loc: Lc.Loc, +a: A, +b: A}
  AEnv{+loc: Lc.Loc}
  ASetEnv{+loc: Lc.Loc, +x: A}
  AGate{+loc: Lc.Loc}
  ALeft{+loc: Lc.Loc, +x: A}
  ARight{+loc: Lc.Loc, +x: A}
  AAbort{+loc: Lc.Loc}
  ACheck{+loc: Lc.Loc, +c: A}
  ARef{+loc: Lc.Loc, +r: U32}

# A body: its hash, the index it was first seen with, the env path its
# walk duplicates (if any) and its term.
type Bd is Data:
  Bd{+h: String, +fi: U32, +dup: Maybe<&2, Dup>, +t: A}

# The bodies by rank, a complete binary tree.
type BT is Data:
  BTip{}
  BOne{+b: Bd}
  BTwo{+l: BT, +r: BT}

# The program's bodies: how many, the tree's size (a power of two), the
# tree.
type P is Data:
  P{+n: U32, +size: U32, +bt: BT}

# A type's kind.
type K is Data:
  KVar{}
  KCode{}
  KCap{}
  KPair{}
  KData{}

# The next link of a chain (a binding, a union-find parent): none, or one.
type Nx is Data:
  NEnd{}
  NAt{+i: U32}

# What constraining a class does (mergeClasses, the old class first):
# nothing, the new class replaces the old, or a conflict where the new or
# the old class is the one that must be boxed.
type Dc is Data:
  DcKeep{}
  DcSet{}
  DcNeedNew{}
  DcNeedOld{}

# Which class a union of two classes keeps: a's, b's, or a conflict where
# b's or a's is the one that must be boxed.
type Mg is Data:
  MgA{}
  MgB{}
  MgNeedB{}
  MgNeedA{}

# How one apply site went in a round: nothing new, dispatched, or stop
# (past the last site, or a failure).
type SS is Data:
  SsNone{}
  SsNew{}
  SsStop{}

# The built-in tags.
type Bi is Data:
  BiGate{}
  BiGateFn{}
  BiAbort{}
  BiCont{}

# A bang and a type (Sigma).
type Sig is Data:
  Sig{+b: U32, +t: U32}

# A pair type: each side's bang and type.
type Pr is Data:
  Pr{+b1: U32, +t1: U32, +b2: U32, +t2: U32}

# A tag of a code class, with the capture that rides with it in a package
# (its bang cb is none() when there is none).
type TE is Data:
  TE{+tag: U32, +cb: U32, +ct: U32}

# An application, dispatched once its function position resolves to code
# (ApplySite); `done` are the tags already dispatched there.
type Site is Data:
  Site{+fn: U32, +env: Sig, +res: Sig, +depth: U32, +loc: Lc.Loc, +done: List<&2, U32>}

# What is not the variables: the apply sites, the blames, two counters per
# body (derivations so far, and the variables the first one minted), the
# sum equations newest first, the first failure (a list, which keeps it
# boxed), and the program.
type X is Type:
  X{sites: Array<Site>, bl: Array<Blame>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P}

# The state: the variables and counters, the pairs, the tags of each tag
# class root, and the rest.
type St is Type:
  St{m: Array<U32>, ps: Array<Pr>, tg: Array<List<&2, TE>>, x: X}

# Work for the unifier, all at a visited set of capture classes and a
# dispatch mode (the dispatching tag, or none()).
type W is Data:
  WSig{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: Sig, +b: Sig}
  WTau{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32}
  WColl{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +s: Sig}

# A frame: its env domain bang and type, and its dispatch depth.
type Ctx is Data:
  Ctx{+bang: U32, +tau: U32, +depth: U32}

# What waits for a result: a view's sum, a pair's second side, a pair, an
# application, a projection (left or right).
type GK is Data:
  KView{+w: U32, +loc: Lc.Loc}
  KPairA{+ctx: Ctx, +here: List<&2, U32>, +loc: Lc.Loc, +b: A}
  KPairB{+loc: Lc.Loc, +sa: Sig}
  KSetEnv{+ctx: Ctx, +here: List<&2, U32>, +loc: Lc.Loc}
  KProj{+loc: Lc.Loc, +left: Bool}

# The constraint walk's jobs (viewNode and intrinsic): a node to view or
# to walk, or a result to hand to the frame on top.
type GJ is Data:
  GView{+ctx: Ctx, +here: List<&2, U32>, +t: A, +ks: List<&2, GK>}
  GIntr{+ctx: Ctx, +here: List<&2, U32>, +t: A, +ks: List<&2, GK>}
  GRet{+s: Sig, +ks: List<&2, GK>}

# fnTagsOfCaptures' work: a tag class to open, a capture's type, or its
# walk.
type FT is Data:
  FtClass{+vis: List<&2, U32>, +i: U32}
  FtCap{+vis: List<&2, U32>, +t: U32}
  FtWalked{+vis: List<&2, U32>, +w: U32}

# fnTagsOfCaptures' work left, and the tags found so far.
type FQ is Data:
  FQ{+js: List<&2, FT>, +acc: List<&2, U32>}

# deepShowTau's work: a type to show at a depth, a walked one, or two shown
# sides to join.
type DS is Data:
  DsTau{+t: U32, +d: U32}
  DsWalked{+k: K, +w: U32, +d: U32}
  DsJoin{}

# deepShowTau's jobs left and the texts shown so far.
type DQ is Data:
  DQ{+js: List<&2, DS>, +vs: List<&2, String>}

# The shapes' work (shapeOfSigma): a type, a walked one, or two shapes to
# pair.
type SJ is Data:
  SjTau{+t: U32}
  SjWalked{+k: K, +w: U32}
  SjPair{}

# The shapes' jobs left and the shapes found so far.
type SQ is Data:
  SQ{+js: List<&2, SJ>, +vs: List<&2, Lf.Shape>}

# A class root's class, read for the solver.
type RC is Data:
  RC{+root: U32, +c: Class}

# A derivation of a code body: its env domain bang and type, and its result.
type Der is Data:
  Der{+b: U32, +t: U32, +s: Sig}

# A step of occurs: whether it hit, and the types left.
type OS is Data:
  OS{+hit: Bool, +ts: List<&2, U32>}

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

type HB is Data:
  HB{+h: String, +ok: Bool}

# Constants
# ---------

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

def big() -> Nat:
  U32.to_nat(4294967295)

# The built-in tags, after every rank; a reference to no body gets
# missing().
def t.gate() -> U32:
  4294967290

def t.gatefn() -> U32:
  4294967291

def t.abort() -> U32:
  4294967292

def t.cont() -> U32:
  4294967293

def missing() -> U32:
  4294967289

def data() -> U32:
  5

def kind.at(+k: U32) -> K:
  Bool.pick(K, U32.is_eq(k, 1), KVar{}, Bool.pick(K, U32.is_eq(k, 2), KCode{},
    Bool.pick(K, U32.is_eq(k, 3), KCap{}, Bool.pick(K, U32.is_eq(k, 4), KPair{}, KData{}))))

def kind(+t: U32) -> K:
  kind.at((t .&. 7 : U32))

def is.var(+t: U32) -> Bool:
  U32.is_eq((t .&. 7 : U32), 1)

def is.code(+t: U32) -> Bool:
  U32.is_eq((t .&. 7 : U32), 2)

def is.pair(+t: U32) -> Bool:
  U32.is_eq((t .&. 7 : U32), 4)

# Code or a capture selection: something an application can dispatch.
def appliable(+t: U32) -> Bool:
  U32.is_eq((t .&. 6 : U32), 2)

def ix(+t: U32) -> U32:
  (t >> 3n : U32)

def var.t(+i: U32) -> U32:
  (i * 8 + 1 : U32)

def code.t(+i: U32) -> U32:
  (i * 8 + 2 : U32)

def cap.t(+i: U32) -> U32:
  (i * 8 + 3 : U32)

def blame.none() -> Blame:
  Blame{Lc.Unknown{}, ""}

def site.none() -> Site:
  Site{0, Sig{0, 0}, Sig{0, 0}, 0, Lc.Unknown{}, []}

def pr.none() -> Pr:
  Pr{0, 0, 0, 0}

def te.none() -> List<&2, TE>:
  []

def sig.b(s: Sig) -> U32:
  match s:
    case Sig{b, t}:
      b

def sig.t(s: Sig) -> U32:
  match s:
    case Sig{b, t}:
      t

def ctx.depth(c: Ctx) -> U32:
  match c:
    case Ctx{bang, tau, depth}:
      depth


# Env usage (envUsageL, contraction)
# ----------------------------------

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

def dup.of(+l: Lf.L) -> Maybe<&2, Dup>:
  contraction(usage(l, "", Map.new(&2, Use)))

# The program
# -----------

# A lifted term as the analysis walks it.
def to.a(l: Lf.L, +ranks: Map<&2, U32>) -> A:
  match l:
    case Lf.LZero{loc}:
      AZero{loc}
    case Lf.LPair{loc, a, b}:
      APair{loc, to.a(a, ranks), to.a(b, ranks)}
    case Lf.LEnv{loc}:
      AEnv{loc}
    case Lf.LUnsized{loc, tok}:
      AEnv{loc}
    case Lf.LSetEnv{loc, x}:
      ASetEnv{loc, to.a(x, ranks)}
    case Lf.LGate{loc}:
      AGate{loc}
    case Lf.LLeft{loc, x}:
      ALeft{loc, to.a(x, ranks)}
    case Lf.LRight{loc, x}:
      ARight{loc, to.a(x, ranks)}
    case Lf.LAbort{loc}:
      AAbort{loc}
    case Lf.LCheck{loc, cloc, tc, c}:
      ACheck{loc, to.a(c, ranks)}
    case Lf.LRef{loc, h}:
      ARef{loc, Pair.snd(Map<&2, U32>, U32, Map.get(U32, missing(), ranks, h))}

def ranks.go(ks: List<&2, String>, +i: U32, acc: Map<&2, U32>) -> Map<&2, U32>:
  match ks:
    case Nil{}:
      acc
    case Con{k, rest}:
      ranks.go(rest, (i + 1 : U32), Map.set(&2, U32, acc, k, i))

# Each body's rank: its place in hash order.
def ranks(+bodies: Map<&2, Lf.Body>) -> Map<&2, U32>:
  ranks.go(Map.keys(&2, Lf.Body, bodies), 0, Map.new(&2, U32))

def bds(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>, +ranks: Map<&2, U32>) -> List<&2, Bd>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (h, b):
          match b:
            case Lf.Body{fi, +body}:
              Bd{h, fi, dup.of(body), to.a(body, ranks)} <> bds(rest, ranks)

def bt.build(+d: Nat, +xs: List<&2, Bd>) -> BT:
  match d:
    case 0n:
      match xs:
        case Nil{}:
          BTip{}
        case Con{x, rest}:
          BOne{x}
    case 1n+e:
      +k = U32.to_nat(U32.shln(1, e))
      BTwo{bt.build(e, List.take(&2, Bd, xs, k)), bt.build(e, List.drop(&2, Bd, xs, k))}

# The body of a rank below the subtree's half size when lo.
def bt.get(t: BT, lo: Bool, +r: U32, +half: U32) -> Maybe<&2, Bd>:
  match t:
    case BTip{}:
      None{}
    case BOne{b}:
      Some{b}
    case BTwo{l, u}:
      match lo:
        case True{}:
          bt.get(l, U32.is_lt(r, U32.shr(half)), r, U32.shr(half))
        case False{}:
          bt.get(u, U32.is_lt((r - half : U32), U32.shr(half)), (r - half : U32), U32.shr(half))

def body.in(ok: Bool, bt: BT, +r: U32, +size: U32) -> Maybe<&2, Bd>:
  match ok:
    case True{}:
      bt.get(bt, U32.is_lt(r, U32.shr(size)), r, U32.shr(size))
    case False{}:
      None{}

# The body of a rank.
def body.at(p: P, +r: U32) -> Maybe<&2, Bd>:
  match p:
    case P{+n, +size, bt}:
      body.in(U32.is_lt(r, n), bt, r, size)

def depth.at(one: Bool, +n: U32) -> Nat:
  match one:
    case True{}:
      0n
    case False{}:
      (U32.log2((n - 1 : U32)) + 1n : Nat)

def depth.of(+n: U32) -> Nat:
  depth.at(U32.is_le(n, 1), n)

def program.of(+n: U32, +d: Nat, xs: List<&2, Bd>) -> P:
  P{n, U32.shln(1, d), bt.build(d, xs)}

# The bodies as the analysis sees them.
def program(+bodies: Map<&2, Lf.Body>, +ranks: Map<&2, U32>) -> P:
  +n = U32.from_nat(Map.size(&2, Lf.Body, bodies))
  program.of(n, depth.of(n), bds(Map.to_list(&2, Lf.Body, bodies), ranks))

# Showing, for messages
# ---------------------

def blame.show(b: Blame) -> String:
  match b:
    case Blame{loc, why}:
      "Blame " ++ Lf.loc.show(loc, True{}) ++ " " ++ Sh.string(why)

def bd.hash(m: Maybe<&2, Bd>) -> String:
  match m:
    case Some{b}:
      match b:
        case Bd{h, fi, dup, t}:
          h
    case None{}:
      "(unknown)"

def builtin(+t: U32) -> Bi:
  Bool.pick(Bi, U32.is_eq(t, t.gate()), BiGate{}, Bool.pick(Bi, U32.is_eq(t, t.gatefn()), BiGateFn{},
    Bool.pick(Bi, U32.is_eq(t, t.abort()), BiAbort{}, BiCont{})))

def bi.show(b: Bi) -> String:
  match b:
    case BiGate{}:
      "TGate"
    case BiGateFn{}:
      "TGateFn"
    case BiAbort{}:
      "TAbort"
    case BiCont{}:
      "TAbortCont"

def tag.builtin(+t: U32) -> String:
  bi.show(builtin(t))

def tag.show.at(code: Bool, +p: P, +t: U32) -> String:
  match code:
    case True{}:
      "TCode " ++ bd.hash(body.at(p, t))
    case False{}:
      tag.builtin(t)

def tag.show(+p: P, +t: U32) -> String:
  tag.show.at(U32.is_lt(t, t.gate()), p, t)

def tags.show.go(+p: P, ts: List<&2, U32>) -> String:
  match ts:
    case Nil{}:
      "]"
    case Con{t, rest}:
      "," ++ tag.show(p, t) ++ tags.show.go(p, rest)

def tags.show(+p: P, ts: List<&2, U32>) -> String:
  match ts:
    case Nil{}:
      "[]"
    case Con{t, rest}:
      "[" ++ tag.show(p, t) ++ tags.show.go(p, rest)

def mode.code(code: Bool, +p: P, +m: U32) -> String:
  match code:
    case True{}:
      "Just (" ++ tag.show(p, m) ++ ")"
    case False{}:
      "Just " ++ tag.show(p, m)

def mode.at(no: Bool, +p: P, +m: U32) -> String:
  match no:
    case True{}:
      "Nothing"
    case False{}:
      mode.code(U32.is_lt(m, t.gate()), p, m)

def mode.show(+p: P, +m: U32) -> String:
  mode.at(U32.is_eq(m, none()), p, m)

def describe.k(k: K, +t: U32) -> String:
  match k:
    case KVar{}:
      "t" ++ U32.show(ix(t))
    case KCode{}:
      "code"
    case KCap{}:
      "capture"
    case KPair{}:
      "pair"
    case KData{}:
      "data"

def describe(+t: U32) -> String:
  describe.k(kind(t), t)

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



# The state
# ---------

# The counters, before the variables: 0 the next variable, 1 the table's
# size in words, 2 and 3 the pairs and their table's size, 4 whether it
# failed, 5 and 6 the apply sites and their table's size, 7 and 8 the
# blames and theirs. Variable i's words start at i * 8 + 16.

def m.new() -> Array<U32>:
  Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, Array.new(U32, 11n, 0), 1, 2048), 3, 64), 6, 64), 8, 64)

def st.new(+p: P) -> St:
  match p:
    case P{+n, size, bt}:
      St{m.new(), Array.new(Pr, 6n, pr.none()), Array.new(List<&2, TE>, 8n, te.none()),
         X{Array.new(Site, 6n, site.none()), Array.new(Blame, 6n, blame.none()),
           Array.new(U32, (U32.log2((n * 2 + 1 : U32)) + 1n : Nat), 0), [], [], p}}

def st.m(ps: Array<Pr>, tg: Array<List<&2, TE>>, x: X, r: Array<U32> & U32) -> St & U32:
  (m, v) = r
  (St{m, ps, tg, x}, v)

# Word i of the table.
def rd(s: St, +i: U32) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      st.m(ps, tg, x, Array.get(U32, m, i))

def wr(s: St, +i: U32, +v: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      St{Array.set(U32, m, i, v), ps, tg, x}

def x.failed(x: X, e: Err) -> X:
  match x:
    case X{sites, bl, ct, eqs, err, p}:
      X{sites, bl, ct, eqs, [e], p}

def fail.set(s: St, e: Err) -> St:
  match s:
    case St{m, ps, tg, x}:
      St{Array.set(U32, m, 4, 1), ps, tg, x.failed(x, e)}

def zero.of(r: St & U32) -> St & Bool:
  (s, +v) = r
  (s, U32.is_zero(v))

# Whether nothing has failed yet.
def ok.of(s: St) -> St & Bool:
  zero.of(rd(s, 4))

def fail.at(e: Err, r: St & Bool) -> St:
  (s, ok) = r
  match ok:
    case True{}:
      fail.set(s, e)
    case False{}:
      s

# A failure, unless there is one already.
def fail(s: St, e: Err) -> St:
  fail.at(e, ok.of(s))

def budget.err() -> Err:
  GaveUp{"constraint variable budget (2000000) exceeded; the dispatch structure is likely exploding"}

# The table and the tags double.
def grow.m(s: St, +size: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      St{Array.set(U32, ANode{m, Array.new(U32, U32.log2(size), 0)}, 1, (size * 2 : U32)), ps,
         ANode{tg, Array.new(List<&2, TE>, U32.log2((size >> 3n : U32)), te.none())}, x}

def fresh.at(over: Bool, full: Bool, s: St, +n: U32, +size: U32) -> St & U32:
  match over:
    case True{}:
      (fail(s, budget.err()), 0)
    case False{}:
      match full:
        case True{}:
          (wr(grow.m(s, size), 0, (n + 1 : U32)), n)
        case False{}:
          (wr(s, 0, (n + 1 : U32)), n)

def fresh.size(+n: U32, r: St & U32) -> St & U32:
  (s, +size) = r
  fresh.at(U32.is_ge(n, var.budget()), U32.is_gt((n * 8 + 24 : U32), size), s, n, size)

def fresh.next(r: St & U32) -> St & U32:
  (s, +n) = r
  fresh.size(n, rd(s, 1))

# freshInt
def fresh(s: St) -> St & U32:
  fresh.next(rd(s, 0))

def as.var(r: St & U32) -> St & U32:
  (s, +i) = r
  (s, var.t(i))

def fresh.tau(s: St) -> St & U32:
  as.var(fresh(s))

def fresh.sig.t(+b: U32, r: St & U32) -> St & Sig:
  (s, +i) = r
  (s, Sig{b, var.t(i)})

def fresh.sig.b(r: St & U32) -> St & Sig:
  (s, +b) = r
  fresh.sig.t(b, fresh(s))

def fresh.sig(s: St) -> St & Sig:
  fresh.sig.b(fresh(s))

# Pairs
# -----

def pair.set(s: St, +n: U32, pr: Pr) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      (St{Array.set(U32, m, 2, (n + 1 : U32)), Array.set(Pr, ps, n, pr), tg, x}, (n * 8 + 4 : U32))

def pair.grow(s: St, +cap: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      St{Array.set(U32, m, 3, (cap * 2 : U32)), ANode{ps, Array.new(Pr, U32.log2(cap), pr.none())}, tg, x}

def pair.room(full: Bool, s: St, +n: U32, +cap: U32, pr: Pr) -> St & U32:
  match full:
    case True{}:
      pair.set(pair.grow(s, cap), n, pr)
    case False{}:
      pair.set(s, n, pr)

def pair.cap(+n: U32, pr: Pr, r: St & U32) -> St & U32:
  (s, +cap) = r
  pair.room(U32.is_ge(n, cap), s, n, cap, pr)

def pair.n(pr: Pr, r: St & U32) -> St & U32:
  (s, +n) = r
  pair.cap(n, pr, rd(s, 3))

# A pair type.
def pair.new(s: St, pr: Pr) -> St & U32:
  pair.n(pr, rd(s, 2))

def pair.got(m: Array<U32>, tg: Array<List<&2, TE>>, x: X, r: Array<Pr> & Pr) -> St & Pr:
  (ps, pr) = r
  (St{m, ps, tg, x}, pr)

# A pair type's sides.
def pair.get(s: St, +t: U32) -> St & Pr:
  match s:
    case St{m, ps, tg, x}:
      pair.got(m, tg, x, Array.get(Pr, ps, ix(t)))

# Tag sets
# --------

def tg.got(m: Array<U32>, ps: Array<Pr>, x: X, r: Array<List<&2, TE>> & List<&2, TE>) -> St & List<&2, TE>:
  (tg, ts) = r
  (St{m, ps, tg, x}, ts)

# The tags held at a variable (a tag class's root).
def tg.get(s: St, +i: U32) -> St & List<&2, TE>:
  match s:
    case St{m, ps, tg, x}:
      tg.got(m, ps, x, Array.get(List<&2, TE>, tg, i))

def tg.set(s: St, +i: U32, ts: List<&2, TE>) -> St:
  match s:
    case St{m, ps, tg, x}:
      St{m, ps, Array.set(List<&2, TE>, tg, i, ts), x}

# Blames, sites, equations, counters
# ----------------------------------

def bl.set(s: St, +n: U32, b: Blame) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          (St{Array.set(U32, m, 7, (n + 1 : U32)), ps, tg, X{sites, Array.set(Blame, bl, n, b), ct, eqs, err, p}}, n)

def bl.grow(s: St, +cap: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          St{Array.set(U32, m, 8, (cap * 2 : U32)), ps, tg,
             X{sites, ANode{bl, Array.new(Blame, U32.log2(cap), blame.none())}, ct, eqs, err, p}}

def bl.room(full: Bool, s: St, +n: U32, +cap: U32, b: Blame) -> St & U32:
  match full:
    case True{}:
      bl.set(bl.grow(s, cap), n, b)
    case False{}:
      bl.set(s, n, b)

def bl.cap(+n: U32, b: Blame, r: St & U32) -> St & U32:
  (s, +cap) = r
  bl.room(U32.is_ge(n, cap), s, n, cap, b)

def bl.n(b: Blame, r: St & U32) -> St & U32:
  (s, +n) = r
  bl.cap(n, b, rd(s, 8))

# A blame kept, by its number.
def blame.add(s: St, b: Blame) -> St & U32:
  bl.n(b, rd(s, 7))

def bl.got(m: Array<U32>, ps: Array<Pr>, tg: Array<List<&2, TE>>, sites: Array<Site>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P, r: Array<Blame> & Blame) -> St & Blame:
  (bl, b) = r
  (St{m, ps, tg, X{sites, bl, ct, eqs, err, p}}, b)

def blame.get(s: St, +n: U32) -> St & Blame:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          bl.got(m, ps, tg, sites, ct, eqs, err, p, Array.get(Blame, bl, n))

def site.set(s: St, +n: U32, site: Site) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          St{m, ps, tg, X{Array.set(Site, sites, n, site), bl, ct, eqs, err, p}}

def site.grow(s: St, +cap: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          St{Array.set(U32, m, 6, (cap * 2 : U32)), ps, tg,
             X{ANode{sites, Array.new(Site, U32.log2(cap), site.none())}, bl, ct, eqs, err, p}}

def site.room(full: Bool, s: St, +n: U32, +cap: U32, site: Site) -> St:
  match full:
    case True{}:
      wr(site.set(site.grow(s, cap), n, site), 5, (n + 1 : U32))
    case False{}:
      wr(site.set(s, n, site), 5, (n + 1 : U32))

def site.cap(+n: U32, site: Site, r: St & U32) -> St:
  (s, +cap) = r
  site.room(U32.is_ge(n, cap), s, n, cap, site)

def site.n(site: Site, r: St & U32) -> St:
  (s, +n) = r
  site.cap(n, site, rd(s, 6))

# registerApply
def site.add(s: St, site: Site) -> St:
  site.n(site, rd(s, 5))

def site.got(m: Array<U32>, ps: Array<Pr>, tg: Array<List<&2, TE>>, bl: Array<Blame>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P, r: Array<Site> & Site) -> St & Site:
  (sites, site) = r
  (St{m, ps, tg, X{sites, bl, ct, eqs, err, p}}, site)

def site.get(s: St, +n: U32) -> St & Site:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          site.got(m, ps, tg, bl, ct, eqs, err, p, Array.get(Site, sites, n))

def eq.add(s: St, e: SumEq) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          St{m, ps, tg, X{sites, bl, ct, e <> eqs, err, p}}

def sum.eq(s: St, +loc: Lc.Loc, +what: String, lhs: List<&2, U32>, +rhs: U32) -> St:
  eq.add(s, SumEq{lhs, rhs, Blame{loc, what}})

def ct.got(m: Array<U32>, ps: Array<Pr>, tg: Array<List<&2, TE>>, sites: Array<Site>, bl: Array<Blame>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P, r: Array<U32> & U32) -> St & U32:
  (ct, v) = r
  (St{m, ps, tg, X{sites, bl, ct, eqs, err, p}}, v)

# A body's counter: its derivations so far (2r), or the variables its
# first one minted (2r + 1).
def ct.get(s: St, +i: U32) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          ct.got(m, ps, tg, sites, bl, eqs, err, p, Array.get(U32, ct, i))

def ct.set(s: St, +i: U32, +v: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          St{m, ps, tg, X{sites, bl, Array.set(U32, ct, i, v), eqs, err, p}}

def p.got(m: Array<U32>, ps: Array<Pr>, tg: Array<List<&2, TE>>, sites: Array<Site>, bl: Array<Blame>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, +p: P) -> St & P:
  (St{m, ps, tg, X{sites, bl, ct, eqs, err, p}}, p)

# The program.
def prog(s: St) -> St & P:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, +p}:
          p.got(m, ps, tg, sites, bl, ct, eqs, err, p)


# Union-find
# ----------

def nx.of(end: Bool, +i: U32) -> Nx:
  match end:
    case True{}:
      NEnd{}
    case False{}:
      NAt{i}

def up.of(r: Array<U32> & U32) -> Array<U32> & Nx:
  (m, +p) = r
  (m, nx.of(U32.is_zero(p), (p - 1 : U32)))

# i's parent on the union-find whose parent is word f of a variable (1
# bangs, 4 tags).
def up(m: Array<U32>, +f: U32, +i: U32) -> Array<U32> & Nx:
  up.of(Array.get(U32, m, (i * 8 + 16 + f : U32)))

# The root of i; r holds i's parent.
def root(fuel: Nat, +f: U32, +i: U32, r: Array<U32> & Nx) -> Array<U32> & U32:
  match fuel:
    case 0n:
      (m, n) = r
      (m, i)
    case 1n+g:
      (m, n) = r
      match n:
        case NEnd{}:
          (m, i)
        case NAt{+j}:
          root(g, f, j, up(m, f, j))

# Every variable on the path from i points at the root r0 afterwards.
def compress(fuel: Nat, +f: U32, +r0: U32, +i: U32, r: Array<U32> & Nx) -> Array<U32>:
  match fuel:
    case 0n:
      (m, n) = r
      m
    case 1n+g:
      (m, n) = r
      match n:
        case NEnd{}:
          m
        case NAt{+j}:
          compress(g, f, r0, j, up(Array.set(U32, m, (i * 8 + 16 + f : U32), (r0 + 1 : U32)), f, j))

def found(+f: U32, +i: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (m, +r0) = r
  (compress(big(), f, r0, i, up(m, f, i)), r0)

def find.m(m: Array<U32>, +f: U32, +i: U32) -> Array<U32> & U32:
  found(f, i, root(big(), f, i, up(m, f, i)))

# find with path compression: on the bangs (f = 1) or the tags (f = 4).
def find(s: St, +f: U32, +i: U32) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      st.m(ps, tg, x, find.m(m, f, i))

# Bang classes
# ------------

def decide.at(free: Bool, zero: Bool, nz: Bool, ge: Bool) -> Dc:
  match free:
    case True{}:
      DcSet{}
    case False{}:
      match zero:
        case True{}:
          match nz:
            case True{}:
              DcKeep{}
            case False{}:
              DcNeedNew{}
        case False{}:
          match nz:
            case True{}:
              DcNeedOld{}
            case False{}:
              match ge:
                case True{}:
                  DcKeep{}
                case False{}:
                  DcSet{}

# Constraining a class (its word c) to kind k (1 forced zero, 2 forced
# level) at level n.
def decide(+c: U32, +k: U32, +n: U32) -> Dc:
  decide.at(U32.is_zero((c .&. 3 : U32)), U32.is_eq((c .&. 3 : U32), 1), U32.is_eq(k, 1), U32.is_ge((c >> 2n : U32), n))

def cls.store(+root: U32, +c: U32, r: St & U32) -> St:
  (s, +id) = r
  wr(wr(s, (root * 8 + 18 : U32), c), (root * 8 + 19 : U32), id)

def conflict(need.new: Bool, nb: Blame, r: St & Blame) -> St & Bool:
  match need.new:
    case True{}:
      (s, ob) = r
      (fail(s, BoxConflict{nb, ob}), False{})
    case False{}:
      (s, ob) = r
      (fail(s, BoxConflict{ob, nb}), False{})

def blame.of.id(r: St & U32) -> St & Blame:
  (s, +id) = r
  blame.get(s, id)

# A class's blame.
def blame.of(s: St, +root: U32) -> St & Blame:
  blame.of.id(rd(s, (root * 8 + 19 : U32)))

def constrain.act(d: Dc, s: St, +root: U32, +k: U32, +n: U32, b: Blame) -> St & Bool:
  match d:
    case DcKeep{}:
      (s, False{})
    case DcSet{}:
      (cls.store(root, (n * 4 + k : U32), blame.add(s, b)), True{})
    case DcNeedNew{}:
      conflict(True{}, b, blame.of(s, root))
    case DcNeedOld{}:
      conflict(False{}, b, blame.of(s, root))

def constrain.cls(+root: U32, +k: U32, +n: U32, b: Blame, r: St & U32) -> St & Bool:
  (s, +c) = r
  constrain.act(decide(c, k, n), s, root, k, n, b)

def constrain.found(+k: U32, +n: U32, b: Blame, over: Bool, r: St & U32) -> St & Bool:
  match over:
    case True{}:
      (s, root) = r
      (fail(s, GaveUp{"bang level exceeded cap of 4096: " ++ blame.show(b)}), False{})
    case False{}:
      (s, +root) = r
      constrain.cls(root, k, n, b, rd(s, (root * 8 + 18 : U32)))

# constrainB to forced zero (k = 1) or to forced level n (k = 2): whether
# the class changed.
def constrain(s: St, +b: U32, +k: U32, +n: U32, bl: Blame) -> St & Bool:
  constrain.found(k, n, bl, U32.is_eq(k, 2) && U32.is_gt(n, level.cap()), find(s, 1, b))

def forced.zero.done(+b: U32, r: St & Bool) -> St & U32:
  (s, changed) = r
  (s, b)

def forced.zero.at(bl: Blame, r: St & U32) -> St & U32:
  (s, +b) = r
  forced.zero.done(b, constrain(s, b, 1, 0, bl))

# forcedZeroB
def forced.zero(s: St, bl: Blame) -> St & U32:
  forced.zero.at(bl, fresh(s))

def plain.at(+t: U32, r: St & U32) -> St & Sig:
  (s, +b) = r
  (s, Sig{b, t})

# plainSigma: a value constructor's own type, locally unboxed.
def plain(s: St, +loc: Lc.Loc, +what: String, +t: U32) -> St & Sig:
  plain.at(t, forced.zero(s, Blame{loc, what}))

def union.pick.at(afree: Bool, azero: Bool, bfree: Bool, bzero: Bool, ge: Bool) -> Mg:
  match afree:
    case True{}:
      MgB{}
    case False{}:
      match azero:
        case True{}:
          match bfree:
            case True{}:
              MgA{}
            case False{}:
              match bzero:
                case True{}:
                  MgA{}
                case False{}:
                  MgNeedB{}
        case False{}:
          match bfree:
            case True{}:
              MgA{}
            case False{}:
              match bzero:
                case True{}:
                  MgNeedA{}
                case False{}:
                  match ge:
                    case True{}:
                      MgA{}
                    case False{}:
                      MgB{}

# Which class a union keeps, of a's (word ca) and b's (word cb): mergeClasses,
# a's first.
def union.pick(+ca: U32, +cb: U32) -> Mg:
  union.pick.at(U32.is_zero((ca .&. 3 : U32)), U32.is_eq((ca .&. 3 : U32), 1), U32.is_zero((cb .&. 3 : U32)),
    U32.is_eq((cb .&. 3 : U32), 1), U32.is_ge((ca >> 2n : U32), (cb >> 2n : U32)))

def union.clash.b(need.b: Bool, ba: Blame, r: St & Blame) -> St:
  match need.b:
    case True{}:
      (s, bb) = r
      fail(s, BoxConflict{bb, ba})
    case False{}:
      (s, bb) = r
      fail(s, BoxConflict{ba, bb})

def union.clash(need.b: Bool, +rb: U32, r: St & Blame) -> St:
  (s, ba) = r
  union.clash.b(need.b, ba, blame.of(s, rb))

def union.keep.a(+ra: U32, +rb: U32, +ca: U32, r: St & U32) -> St:
  (s, +id) = r
  wr(wr(wr(wr(s, (ra * 8 + 17 : U32), (rb + 1 : U32)), (rb * 8 + 18 : U32), ca), (rb * 8 + 19 : U32), id), (ra * 8 + 18 : U32), 0)

def union.act(d: Mg, s: St, +ra: U32, +rb: U32, +ca: U32) -> St:
  match d:
    case MgA{}:
      union.keep.a(ra, rb, ca, rd(s, (ra * 8 + 19 : U32)))
    case MgB{}:
      wr(wr(s, (ra * 8 + 17 : U32), (rb + 1 : U32)), (ra * 8 + 18 : U32), 0)
    case MgNeedB{}:
      union.clash(True{}, rb, blame.of(s, ra))
    case MgNeedA{}:
      union.clash(False{}, rb, blame.of(s, ra))

def union.cb(+ra: U32, +rb: U32, +ca: U32, r: St & U32) -> St:
  (s, +cb) = r
  union.act(union.pick(ca, cb), s, ra, rb, ca)

def union.ca(+ra: U32, +rb: U32, r: St & U32) -> St:
  (s, +ca) = r
  union.cb(ra, rb, ca, rd(s, (rb * 8 + 18 : U32)))

def union.same(same: Bool, s: St, +ra: U32, +rb: U32) -> St:
  match same:
    case True{}:
      s
    case False{}:
      union.ca(ra, rb, rd(s, (ra * 8 + 18 : U32)))

def union.rb(+ra: U32, r: St & U32) -> St:
  (s, +rb) = r
  union.same(U32.is_eq(ra, rb), s, ra, rb)

def union.ra(+b: U32, r: St & U32) -> St:
  (s, +ra) = r
  union.rb(ra, find(s, 1, b))

# unionB: the root of a points at b's, which keeps the merged class.
def union.b(s: St, +a: U32, +b: U32) -> St:
  union.ra(b, find(s, 1, a))

# Tag classes
# -----------

def keys(ts: List<&2, TE>) -> List<&2, U32>:
  match ts:
    case Nil{}:
      []
    case Con{e, rest}:
      match e:
        case TE{tag, cb, ct}:
          tag <> keys(rest)

def caps.at(r: St & U32) -> St & List<&2, TE>:
  (s, +root) = r
  tg.get(s, root)

# The tags of i's class, with their captures (capturesOf).
def caps(s: St, +i: U32) -> St & List<&2, TE>:
  caps.at(find(s, 4, i))

def keys.of(r: St & List<&2, TE>) -> St & List<&2, U32>:
  (s, ts) = r
  (s, keys(ts))

# tagSetOf
def tag.set(s: St, +i: U32) -> St & List<&2, U32>:
  keys.of(caps(s, i))

def fresh.code.at(+tag: U32, r: St & U32) -> St & U32:
  (s, +i) = r
  (tg.set(s, i, [TE{tag, none(), 0}]), code.t(i))

# A fresh code class holding exactly this tag (freshCode).
def fresh.code(s: St, +tag: U32) -> St & U32:
  fresh.code.at(tag, fresh(s))

def with.cap(ts: List<&2, U32>, +cb: U32, +ct: U32) -> List<&2, TE>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      TE{t, cb, ct} <> with.cap(rest, cb, ct)

def package.at(ts: List<&2, U32>, +cap: Sig, r: St & U32) -> St & U32:
  match cap:
    case Sig{+cb, +ct}:
      (s, +p) = r
      (tg.set(s, p, with.cap(ts, cb, ct)), p)

def package.ts(+cap: Sig, r: St & List<&2, U32>) -> St & U32:
  (s, ts) = r
  package.at(ts, cap, fresh(s))

# A closure package: the tags of code class i, each carrying this capture
# (packageClass).
def package(s: St, +i: U32, +cap: Sig) -> St & U32:
  package.ts(cap, tag.set(s, i))

def te.cmp(x: TE, y: TE) -> Cmp:
  match x y:
    case TE{a, xb, xt} TE{b, yb, yt}:
      U32.cmp(a, b)

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
          te.cmp(x, y)

def join.at(has: Bool, +t: U32, +xb: U32, +xt: U32, +yb: U32, +yt: U32) -> TE:
  match has:
    case True{}:
      TE{t, xb, xt}
    case False{}:
      TE{t, yb, yt}

def join.eq(x: TE, y: TE) -> TE:
  match x y:
    case TE{+t, +xb, +xt} TE{u, +yb, +yt}:
      join.at(U32.is_ne(xb, none()), t, xb, xt, yb, yt)

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
  tags.join.go(big(), xs, ys, heads(xs, ys))

def pending.at(both: Bool, +xb: U32, +xt: U32, +yb: U32, +yt: U32, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  match both:
    case True{}:
      WSig{[], none(), loc, Sig{xb, xt}, Sig{yb, yt}} <> rest
    case False{}:
      rest

def pending.one(x: TE, y: TE, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  match x y:
    case TE{t, +xb, +xt} TE{u, +yb, +yt}:
      pending.at(U32.is_ne(xb, none()) && U32.is_ne(yb, none()), xb, xt, yb, yt, loc, rest)

# The captures both classes hold for one tag, in tag order, as unifier
# work: they must unify.
def pending.go(fuel: Nat, +xs: List<&2, TE>, +ys: List<&2, TE>, c: Cmp, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  match fuel:
    case 0n:
      rest
    case 1n+f:
      match xs:
        case Nil{}:
          rest
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              rest
            case Con{+y, +yr}:
              match c:
                case LT{}:
                  pending.go(f, xr, Con{y, yr}, heads(xr, Con{y, yr}), loc, rest)
                case GT{}:
                  pending.go(f, Con{x, xr}, yr, heads(Con{x, xr}, yr), loc, rest)
                case EQ{}:
                  pending.one(x, y, loc, pending.go(f, xr, yr, heads(xr, yr), loc, rest))

def pending(+xs: List<&2, TE>, +ys: List<&2, TE>, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  pending.go(big(), xs, ys, heads(xs, ys), loc, rest)

def union.tags.mb(+ra: U32, +rb: U32, +ma: List<&2, TE>, +loc: Lc.Loc, rest: List<&2, W>, r: St & List<&2, TE>) -> St & List<&2, W>:
  (s, +mb) = r
  (tg.set(tg.set(wr(s, (ra * 8 + 20 : U32), (rb + 1 : U32)), rb, tags.join(ma, mb)), ra, te.none()),
   pending(ma, mb, loc, rest))

def union.tags.ma(+ra: U32, +rb: U32, +loc: Lc.Loc, rest: List<&2, W>, r: St & List<&2, TE>) -> St & List<&2, W>:
  (s, +ma) = r
  union.tags.mb(ra, rb, ma, loc, rest, tg.get(s, rb))

def union.tags.same(same: Bool, s: St, +ra: U32, +rb: U32, +loc: Lc.Loc, rest: List<&2, W>) -> St & List<&2, W>:
  match same:
    case True{}:
      (s, rest)
    case False{}:
      union.tags.ma(ra, rb, loc, rest, tg.get(s, ra))

def union.tags.rb(+ra: U32, +loc: Lc.Loc, rest: List<&2, W>, r: St & U32) -> St & List<&2, W>:
  (s, +rb) = r
  union.tags.same(U32.is_eq(ra, rb), s, ra, rb, loc, rest)

def union.tags.ra(+b: U32, +loc: Lc.Loc, rest: List<&2, W>, r: St & U32) -> St & List<&2, W>:
  (s, +ra) = r
  union.tags.rb(ra, loc, rest, find(s, 4, b))

# unionTags: a's root points at b's, which holds both classes' tags; the
# captures both held for a tag must unify, so they go on the unifier's
# work, first.
def union.tags(s: St, +a: U32, +b: U32, +loc: Lc.Loc, rest: List<&2, W>) -> St & List<&2, W>:
  union.tags.ra(b, loc, rest, find(s, 4, a))


# Types
# -----

def bind.of(r: Array<U32> & U32) -> Array<U32> & Nx:
  (m, +b) = r
  (m, nx.of(U32.is_zero(b), b))

# What a type's walk reads next: a bound variable's binding; anything else
# ends the walk.
def bound.at(var: Bool, +t: U32, m: Array<U32>) -> Array<U32> & Nx:
  match var:
    case True{}:
      bind.of(Array.get(U32, m, (ix(t) * 8 + 16 : U32)))
    case False{}:
      (m, NEnd{})

def bound(+t: U32, m: Array<U32>) -> Array<U32> & Nx:
  bound.at(is.var(t), t, m)

def walk.go(fuel: Nat, +t: U32, r: Array<U32> & Nx) -> Array<U32> & U32:
  match fuel:
    case 0n:
      (m, n) = r
      (m, t)
    case 1n+g:
      (m, n) = r
      match n:
        case NEnd{}:
          (m, t)
        case NAt{+b}:
          walk.go(g, b, bound(b, m))

# walkTau
def walk(s: St, +t: U32) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      st.m(ps, tg, x, walk.go(big(), t, bound(t, m)))

def occurs.pair(ts: List<&2, U32>, r: St & Pr) -> St & OS:
  (s, pr) = r
  match pr:
    case Pr{b1, t1, b2, t2}:
      (s, OS{False{}, t1 <> t2 <> ts})

def occurs.kind(k: K, +i: U32, s: St, +w: U32, ts: List<&2, U32>) -> St & OS:
  match k:
    case KVar{}:
      (s, OS{U32.is_eq(ix(w), i), ts})
    case KPair{}:
      occurs.pair(ts, pair.get(s, w))
    case _:
      (s, OS{False{}, ts})

def occurs.walked(+i: U32, ts: List<&2, U32>, r: St & U32) -> St & OS:
  (s, +w) = r
  occurs.kind(kind(w), i, s, w, ts)

def occurs.go(fuel: Nat, +i: U32, r: St & OS) -> St & Bool:
  match fuel:
    case 0n:
      (s, o) = r
      (s, False{})
    case 1n+g:
      (s, o) = r
      match o:
        case OS{hit, ts}:
          match hit:
            case True{}:
              (s, True{})
            case False{}:
              match ts:
                case Nil{}:
                  (s, False{})
                case Con{+t, rest}:
                  occurs.go(g, i, occurs.walked(i, rest, walk(s, t)))

# Whether variable i occurs in t.
def occurs(s: St, +i: U32, +t: U32) -> St & Bool:
  occurs.go(big(), i, (s, OS{False{}, [t]}))

# deepShowTau, for mismatch reports: the texts come out on a stack, a
# pair's once both sides are shown.

def ds.push(js: List<&2, DS>, vs: List<&2, String>, s: St, +v: String) -> St & DQ:
  (s, DQ{js, v <> vs})

def ds.walked(+d: U32, js: List<&2, DS>, vs: List<&2, String>, r: St & U32) -> St & DQ:
  (s, +w) = r
  (s, DQ{DsWalked{kind(w), w, d} <> js, vs})

def ds.code.p(+root: U32, ts: List<&2, U32>, js: List<&2, DS>, vs: List<&2, String>, r: St & P) -> St & DQ:
  (s, +p) = r
  (s, DQ{js, ("Code#" ++ U32.show(root) ++ tags.show(p, ts)) <> vs})

def ds.code.ts(+root: U32, js: List<&2, DS>, vs: List<&2, String>, r: St & List<&2, U32>) -> St & DQ:
  (s, ts) = r
  ds.code.p(root, ts, js, vs, prog(s))

def ds.code(+i: U32, js: List<&2, DS>, vs: List<&2, String>, r: St & U32) -> St & DQ:
  (s, +root) = r
  ds.code.ts(root, js, vs, tag.set(s, i))

def ds.cap(js: List<&2, DS>, vs: List<&2, String>, r: St & U32) -> St & DQ:
  (s, +root) = r
  (s, DQ{js, ("Cap#" ++ U32.show(root)) <> vs})

def ds.pair(+d: U32, js: List<&2, DS>, vs: List<&2, String>, r: St & Pr) -> St & DQ:
  (s, pr) = r
  match pr:
    case Pr{b1, t1, b2, t2}:
      (s, DQ{DsTau{t1, (d - 1 : U32)} <> DsTau{t2, (d - 1 : U32)} <> DsJoin{} <> js, vs})

def ds.join(vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Con{sb, r1}:
      match r1:
        case Con{sa, r2}:
          ("(" ++ sa ++ ", " ++ sb ++ ")") <> r2
        case Nil{}:
          [sb]
    case Nil{}:
      []

def ds.tau(stop: Bool, s: St, +t: U32, +d: U32, js: List<&2, DS>, vs: List<&2, String>) -> St & DQ:
  match stop:
    case True{}:
      ds.push(js, vs, s, "...")
    case False{}:
      ds.walked(d, js, vs, walk(s, t))

def ds.step(s: St, j: DS, js: List<&2, DS>, vs: List<&2, String>) -> St & DQ:
  match j:
    case DsTau{+t, +d}:
      ds.tau(U32.is_zero(d), s, t, d, js, vs)
    case DsWalked{k, +w, +d}:
      match k:
        case KData{}:
          ds.push(js, vs, s, "D")
        case KVar{}:
          ds.push(js, vs, s, "t" ++ U32.show(ix(w)))
        case KCode{}:
          ds.code(ix(w), js, vs, find(s, 4, ix(w)))
        case KCap{}:
          ds.cap(js, vs, find(s, 4, ix(w)))
        case KPair{}:
          ds.pair(d, js, vs, pair.get(s, w))
    case DsJoin{}:
      (s, DQ{js, ds.join(vs)})

def ds.go(fuel: Nat, r: St & DQ) -> St & String:
  match fuel:
    case 0n:
      (s, q) = r
      (s, "...")
    case 1n+f:
      (s, q) = r
      match q:
        case DQ{js, vs}:
          match js:
            case Con{j, rest}:
              ds.go(f, ds.step(s, j, rest, vs))
            case Nil{}:
              match vs:
                case Con{v, more}:
                  (s, v)
                case Nil{}:
                  (s, "...")

def deep.show(s: St, +t: U32) -> St & String:
  ds.go(big(), (s, DQ{[DsTau{t, 5}], []}))

def mismatch.p(+loc: Lc.Loc, +mode: U32, +a: U32, +b: U32, +da: String, +db: String, r: St & P) -> St & List<&2, W>:
  (s, +p) = r
  (fail(s, TypeMismatch{loc, describe(a) ++ " vs " ++ describe(b) ++ " [mode " ++ mode.show(p, mode) ++ "; "
    ++ da ++ " ||| " ++ db ++ "]"}), [])

def mismatch.b(+loc: Lc.Loc, +mode: U32, +a: U32, +b: U32, +da: String, r: St & String) -> St & List<&2, W>:
  (s, +db) = r
  mismatch.p(loc, mode, a, b, da, db, prog(s))

def mismatch.a(+loc: Lc.Loc, +mode: U32, +a: U32, +b: U32, r: St & String) -> St & List<&2, W>:
  (s, +da) = r
  mismatch.b(loc, mode, a, b, da, deep.show(s, b))

# Two walked types that cannot unify: the unification stops here.
def mismatch(s: St, +loc: Lc.Loc, +mode: U32, +a: U32, +b: U32) -> St & List<&2, W>:
  mismatch.a(loc, mode, a, b, deep.show(s, a))

# Unification
# -----------

def bind.at(cyclic: Bool, s: St, +loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>) -> St & List<&2, W>:
  match cyclic:
    case True{}:
      (wr(s, (i * 8 + 16 : U32), data()), WTau{[], none(), loc, t, data()} <> rest)
    case False{}:
      (wr(s, (i * 8 + 16 : U32), t), rest)

def bind.occ(+loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>, r: St & Bool) -> St & List<&2, W>:
  (s, cyclic) = r
  bind.at(cyclic, s, loc, i, t, rest)

# bindTVar: a cyclic binding collapses to data.
def bind.var(s: St, +loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>) -> St & List<&2, W>:
  bind.occ(loc, i, t, rest, occurs(s, i, t))

def member(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      U32.is_eq(x, y) || member(rest, x)

def te.cap(e: TE) -> Sig:
  match e:
    case TE{tag, cb, ct}:
      Sig{cb, ct}

def head.cmp(ts: List<&2, TE>, +t: U32) -> Cmp:
  match ts:
    case Nil{}:
      GT{}
    case Con{e, rest}:
      match e:
        case TE{tag, cb, ct}:
          U32.cmp(tag, t)

def lookup.at(fuel: Nat, +ts: List<&2, TE>, +t: U32, c: Cmp) -> Sig:
  match fuel:
    case 0n:
      Sig{none(), 0}
    case 1n+f:
      match ts:
        case Nil{}:
          Sig{none(), 0}
        case Con{+e, +rest}:
          match c:
            case LT{}:
              lookup.at(f, rest, t, head.cmp(rest, t))
            case EQ{}:
              te.cap(e)
            case GT{}:
              Sig{none(), 0}

# The capture a class holds for one tag (its bang none() when there is
# none).
def lookup(+ts: List<&2, TE>, +t: U32) -> Sig:
  lookup.at(big(), ts, t, head.cmp(ts, t))

def cap.one(no: Bool, +ct: U32, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>) -> List<&2, W>:
  match no:
    case True{}:
      rest
    case False{}:
      WTau{vis, mode, loc, ct, t} <> rest

def cap.all(cs: List<&2, TE>, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>) -> List<&2, W>:
  match cs:
    case Nil{}:
      rest
    case Con{e, er}:
      match e:
        case TE{tag, +cb, ct}:
          cap.one(U32.is_eq(cb, none()), ct, vis, mode, loc, t, cap.all(er, vis, mode, loc, t, rest))

def cap.pick(no: Bool, +ct: U32, +cs: List<&2, TE>, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>) -> List<&2, W>:
  match no:
    case True{}:
      cap.all(cs, vis, mode, loc, t, rest)
    case False{}:
      WTau{vis, mode, loc, ct, t} <> rest

def cap.mode(m: Sig, +cs: List<&2, TE>, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>) -> List<&2, W>:
  match m:
    case Sig{+cb, ct}:
      cap.pick(U32.is_eq(cb, none()), ct, cs, vis, mode, loc, t, rest)

def cap.for.at(no: Bool, +mode: U32, +cs: List<&2, TE>) -> Sig:
  match no:
    case True{}:
      Sig{none(), 0}
    case False{}:
      lookup(cs, mode)

def cap.for(+mode: U32, +cs: List<&2, TE>) -> Sig:
  cap.for.at(U32.is_eq(mode, none()), mode, cs)

def cap.caps(+root: U32, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>, r: St & List<&2, TE>) -> St & List<&2, W>:
  (s, +cs) = r
  (s, cap.mode(cap.for(mode, cs), cs, root <> vis, mode, loc, t, rest))

def cap.seen(seen: Bool, s: St, +root: U32, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>) -> St & List<&2, W>:
  match seen:
    case True{}:
      (s, rest)
    case False{}:
      cap.caps(root, vis, mode, loc, t, rest, tg.get(s, root))

def cap.found(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>, r: St & U32) -> St & List<&2, W>:
  (s, +root) = r
  cap.seen(member(vis, root), s, root, vis, mode, loc, t, rest)

# resolveCapT: under a dispatch mode the package holds, that tag's capture
# is meant; otherwise every capture the package holds must fit.
def cap.resolve(s: St, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>) -> St & List<&2, W>:
  cap.found(vis, mode, loc, t, rest, find(s, 4, i))

def colls(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, rest: List<&2, W>, r: St & Pr) -> St & List<&2, W>:
  (s, pr) = r
  match pr:
    case Pr{b1, t1, b2, t2}:
      (s, WColl{vis, mode, loc, Sig{b1, t1}} <> WColl{vis, mode, loc, Sig{b2, t2}} <> rest)

def pairs.b(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, pa: Pr, rest: List<&2, W>, r: St & Pr) -> St & List<&2, W>:
  match pa:
    case Pr{a1, s1, a2, s2}:
      (s, pb) = r
      match pb:
        case Pr{b1, t1, b2, t2}:
          (s, WSig{vis, mode, loc, Sig{a1, s1}, Sig{b1, t1}} <> WSig{vis, mode, loc, Sig{a2, s2}, Sig{b2, t2}} <> rest)

def pairs.a(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +b: U32, rest: List<&2, W>, r: St & Pr) -> St & List<&2, W>:
  (s, pa) = r
  pairs.b(vis, mode, loc, pa, rest, pair.get(s, b))

def same.var(same: Bool, s: St, +loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>) -> St & List<&2, W>:
  match same:
    case True{}:
      (s, rest)
    case False{}:
      bind.var(s, loc, i, t, rest)

# unifyTauAt, on walked types: its immediate effect, then the work left.
def walked(ka: K, kb: K, s: St, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> St & List<&2, W>:
  match ka:
    case KVar{}:
      match kb:
        case KVar{}:
          same.var(U32.is_eq(a, b), s, loc, ix(a), b, rest)
        case _:
          bind.var(s, loc, ix(a), b, rest)
    case KData{}:
      match kb:
        case KVar{}:
          bind.var(s, loc, ix(b), a, rest)
        case KData{}:
          (s, rest)
        case KCap{}:
          cap.resolve(s, vis, mode, loc, ix(b), a, rest)
        case KPair{}:
          colls(vis, mode, loc, rest, pair.get(s, b))
        case KCode{}:
          mismatch(s, loc, mode, a, b)
    case KCode{}:
      match kb:
        case KVar{}:
          bind.var(s, loc, ix(b), a, rest)
        case KCode{}:
          union.tags(s, ix(a), ix(b), loc, rest)
        case KCap{}:
          cap.resolve(s, vis, mode, loc, ix(b), a, rest)
        case _:
          mismatch(s, loc, mode, a, b)
    case KCap{}:
      match kb:
        case KVar{}:
          bind.var(s, loc, ix(b), a, rest)
        case KCap{}:
          union.tags(s, ix(a), ix(b), loc, rest)
        case _:
          cap.resolve(s, vis, mode, loc, ix(a), b, rest)
    case KPair{}:
      match kb:
        case KVar{}:
          bind.var(s, loc, ix(b), a, rest)
        case KCap{}:
          cap.resolve(s, vis, mode, loc, ix(b), a, rest)
        case KPair{}:
          pairs.a(vis, mode, loc, b, rest, pair.get(s, a))
        case KData{}:
          colls(vis, mode, loc, rest, pair.get(s, a))
        case KCode{}:
          mismatch(s, loc, mode, a, b)

def unify.wb(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +wa: U32, rest: List<&2, W>, r: St & U32) -> St & List<&2, W>:
  (s, +wb) = r
  walked(kind(wa), kind(wb), s, vis, mode, loc, wa, wb, rest)

def unify.wa(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +b: U32, rest: List<&2, W>, r: St & U32) -> St & List<&2, W>:
  (s, +wa) = r
  unify.wb(vis, mode, loc, wa, rest, walk(s, b))

def unify.coll(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>, r: St & Bool) -> St & List<&2, W>:
  (s, changed) = r
  (s, WTau{vis, mode, loc, t, data()} <> rest)

def unify.one(s: St, w: W, rest: List<&2, W>) -> St & List<&2, W>:
  match w:
    case WSig{+vis, +mode, +loc, a, b}:
      match a b:
        case Sig{+ba, ta} Sig{+bb, tb}:
          (union.b(s, ba, bb), WTau{vis, mode, loc, ta, tb} <> rest)
    case WTau{+vis, +mode, +loc, +a, +b}:
      unify.wa(vis, mode, loc, b, rest, walk(s, a))
    case WColl{+vis, +mode, +loc, sg}:
      match sg:
        case Sig{+b, +t}:
          unify.coll(vis, mode, loc, t, rest, constrain(s, b, 1, 0, Blame{loc, "component of a data pair is unboxed data"}))

def unify.ok(w: W, rest: List<&2, W>, r: St & Bool) -> St & List<&2, W>:
  (s, ok) = r
  match ok:
    case True{}:
      unify.one(s, w, rest)
    case False{}:
      (s, [])

def unify.go(fuel: Nat, r: St & List<&2, W>) -> St:
  match fuel:
    case 0n:
      (s, ws) = r
      fail(s, Internal{"unification ran out of steps"})
    case 1n+f:
      (s, ws) = r
      match ws:
        case Nil{}:
          s
        case Con{w, rest}:
          unify.go(f, unify.ok(w, rest, ok.of(s)))

# unifySigmaAt with an empty visited set.
def unify.at(s: St, +mode: U32, +loc: Lc.Loc, a: Sig, b: Sig) -> St:
  unify.go(big(), (s, [WSig{[], mode, loc, a, b}]))

# unifySigma
def unify(s: St, +loc: Lc.Loc, a: Sig, b: Sig) -> St:
  unify.at(s, none(), loc, a, b)


# Constraint generation (viewNode, intrinsic)
# -------------------------------------------

def a.loc(t: A) -> Lc.Loc:
  match t:
    case AZero{loc}:
      loc
    case APair{loc, a, b}:
      loc
    case AEnv{loc}:
      loc
    case ASetEnv{loc, x}:
      loc
    case AGate{loc}:
      loc
    case ALeft{loc, x}:
      loc
    case ARight{loc, x}:
      loc
    case AAbort{loc}:
      loc
    case ACheck{loc, c}:
      loc
    case ARef{loc, r}:
      loc

def occ.b(+tau: U32, r: St & U32) -> St & Sig:
  (s, +b) = r
  (s, Sig{b, tau})

def occ.slack(+bang: U32, +tau: U32, +here: List<&2, U32>, +loc: Lc.Loc, +d: U32, r: St & U32) -> St & Sig:
  (s, +slack) = r
  occ.b(tau, forced.zero(sum.eq(sum.eq(s, loc, "env occurrence depth = domain bang + slack", [bang, slack], d),
    loc, "env occurrence depth matches its path boxes", here, d), Blame{loc, "variable occurrence is locally unboxed"}))

def occ.d(+bang: U32, +tau: U32, +here: List<&2, U32>, +loc: Lc.Loc, r: St & U32) -> St & Sig:
  (s, +d) = r
  occ.slack(bang, tau, here, loc, d, fresh(s))

# envOccurrence
def occurrence(s: St, +ctx: Ctx, +here: List<&2, U32>, +loc: Lc.Loc) -> St & Sig:
  match ctx:
    case Ctx{+bang, +tau, depth}:
      occ.d(bang, tau, here, loc, fresh(s))

def leaf.code.at(+loc: Lc.Loc, +what: String, r: St & U32) -> St & Sig:
  (s, +ct) = r
  plain(s, loc, what, ct)

# A code constant: a fresh code class holding its tag, locally unboxed.
def leaf.code(s: St, +loc: Lc.Loc, +tag: U32, +what: String) -> St & Sig:
  leaf.code.at(loc, what, fresh.code(s, tag))

def pair.plain(+loc: Lc.Loc, r: St & U32) -> St & Sig:
  (s, +t) = r
  plain(s, loc, "pair constructor is locally unboxed", t)

def pair.pkg.b(+loc: Lc.Loc, +sa: Sig, +sb: Sig, r: St & U32) -> St & Sig:
  (s, +p) = r
  pair.plain(loc, pair.new(s, Pr{sig.b(sa), sig.t(sa), sig.b(sb), cap.t(p)}))

# A pair: a code-headed one is a closure package, whose right side the
# package's tags hold as their capture.
def pair.of(code: Bool, s: St, +loc: Lc.Loc, +sa: Sig, +sb: Sig, +w: U32) -> St & Sig:
  match code:
    case True{}:
      pair.pkg.b(loc, sa, sb, package(s, ix(w), sb))
    case False{}:
      pair.plain(loc, pair.new(s, Pr{sig.b(sa), sig.t(sa), sig.b(sb), sig.t(sb)}))

def gen.ret0(ks: List<&2, GK>, r: St & Sig) -> St & GJ:
  (s, sg) = r
  (s, GRet{sg, ks})

def gen.pair(+loc: Lc.Loc, +sa: Sig, +sb: Sig, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +w) = r
  gen.ret0(ks, pair.of(is.code(w), s, loc, sa, sb, w))

def se.done(+loc: Lc.Loc, +depth: U32, +fnt: U32, +si: Sig, +so: Sig, +sx: Sig, +pairb: U32, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +t) = r
  (site.add(unify(s, loc, sx, Sig{pairb, t}), Site{fnt, si, so, depth, loc, []}), GRet{so, ks})

def se.pairb(+loc: Lc.Loc, +depth: U32, +fnt: U32, +fnb: U32, +si: Sig, +so: Sig, +sx: Sig, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +pairb) = r
  se.done(loc, depth, fnt, si, so, sx, pairb, ks, pair.new(s, Pr{fnb, fnt, sig.b(si), sig.t(si)}))

def se.fnb(+loc: Lc.Loc, +depth: U32, +fnt: U32, +si: Sig, +so: Sig, +sx: Sig, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +fnb) = r
  se.pairb(loc, depth, fnt, fnb, si, so, sx, ks, fresh(s))

def se.fnt(+loc: Lc.Loc, +depth: U32, +si: Sig, +so: Sig, +sx: Sig, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +fnt) = r
  se.fnb(loc, depth, fnt, si, so, sx, ks, forced.zero(s, Blame{loc, "applied function must be unboxed"}))

def se.so(+loc: Lc.Loc, +depth: U32, +si: Sig, +sx: Sig, ks: List<&2, GK>, r: St & Sig) -> St & GJ:
  (s, +so) = r
  se.fnt(loc, depth, si, so, sx, ks, fresh.tau(s))

def se.si(+loc: Lc.Loc, +depth: U32, +sx: Sig, ks: List<&2, GK>, r: St & Sig) -> St & GJ:
  (s, +si) = r
  se.so(loc, depth, si, sx, ks, fresh.sig(s))

def pj.done(left: Bool, +loc: Lc.Loc, +sl: Sig, +sr: Sig, +sx: Sig, +pb: U32, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  match left:
    case True{}:
      (s, +t) = r
      (unify(s, loc, sx, Sig{pb, t}), GRet{sl, ks})
    case False{}:
      (s, +t) = r
      (unify(s, loc, sx, Sig{pb, t}), GRet{sr, ks})

def pj.pb(left: Bool, +loc: Lc.Loc, +sl: Sig, +sr: Sig, +sx: Sig, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +pb) = r
  pj.done(left, loc, sl, sr, sx, pb, ks, pair.new(s, Pr{sig.b(sl), sig.t(sl), sig.b(sr), sig.t(sr)}))

def pj.sr(left: Bool, +loc: Lc.Loc, +sl: Sig, +sx: Sig, ks: List<&2, GK>, r: St & Sig) -> St & GJ:
  (s, +sr) = r
  pj.pb(left, loc, sl, sr, sx, ks, fresh(s))

def pj.sl(left: Bool, +loc: Lc.Loc, +sx: Sig, ks: List<&2, GK>, r: St & Sig) -> St & GJ:
  (s, +sl) = r
  pj.sr(left, loc, sl, sx, ks, fresh.sig(s))

def gen.viewed(+w: U32, +bi: U32, +ti: U32, +loc: Lc.Loc, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +v) = r
  (sum.eq(s, loc, "view bangs = edge boxes + intrinsic bangs", [w, bi], v), GRet{Sig{v, ti}, ks})

# A result handed to the frame waiting for it.
def gen.ret(s: St, k: GK, sg: Sig, ks: List<&2, GK>) -> St & GJ:
  match k:
    case KView{+w, +loc}:
      match sg:
        case Sig{+bi, +ti}:
          gen.viewed(w, bi, ti, loc, ks, fresh(s))
    case KPairA{+ctx, +here, +loc, +b}:
      (s, GView{ctx, here, b, KPairB{loc, sg} <> ks})
    case KPairB{+loc, +sa}:
      gen.pair(loc, sa, sg, ks, walk(s, sig.t(sa)))
    case KSetEnv{+ctx, +here, +loc}:
      se.si(loc, ctx.depth(ctx), sg, ks, fresh.sig(s))
    case KProj{+loc, left}:
      pj.sl(left, loc, sg, ks, fresh.sig(s))

def gen.view.at(+ctx: Ctx, +here: List<&2, U32>, +t: A, ks: List<&2, GK>, r: St & U32) -> St & GJ:
  (s, +w) = r
  (s, GIntr{ctx, w <> here, t, KView{w, a.loc(t)} <> ks})

def gen.intr(s: St, +ctx: Ctx, +here: List<&2, U32>, t: A, ks: List<&2, GK>) -> St & GJ:
  match t:
    case AZero{+loc}:
      gen.ret0(ks, plain(s, loc, "Zero is an unboxed value", data()))
    case APair{+loc, a, +b}:
      (s, GView{ctx, here, a, KPairA{ctx, here, loc, b} <> ks})
    case AEnv{+loc}:
      gen.ret0(ks, occurrence(s, ctx, here, loc))
    case ASetEnv{+loc, x}:
      (s, GView{ctx, here, x, KSetEnv{ctx, here, loc} <> ks})
    case AGate{+loc}:
      gen.ret0(ks, leaf.code(s, loc, t.gate(), "gate is an unboxed value"))
    case ALeft{+loc, x}:
      (s, GView{ctx, here, x, KProj{loc, True{}} <> ks})
    case ARight{+loc, x}:
      (s, GView{ctx, here, x, KProj{loc, False{}} <> ks})
    case AAbort{+loc}:
      gen.ret0(ks, leaf.code(s, loc, t.abort(), "abort is an unboxed value"))
    case ACheck{loc, c}:
      (s, GIntr{ctx, here, c, ks})
    case ARef{+loc, +r}:
      gen.ret0(ks, leaf.code(s, loc, r, "code constant is an unboxed value"))

def gen.go(fuel: Nat, r: St & GJ) -> St & Sig:
  match fuel:
    case 0n:
      (s, j) = r
      (fail(s, Internal{"term too deep"}), Sig{0, 0})
    case 1n+f:
      (s, j) = r
      match j:
        case GRet{sg, ks}:
          match ks:
            case Nil{}:
              (s, sg)
            case Con{k, rest}:
              gen.go(f, gen.ret(s, k, sg, rest))
        case GView{+ctx, +here, +t, ks}:
          gen.go(f, gen.view.at(ctx, here, t, ks, fresh(s)))
        case GIntr{+ctx, +here, t, ks}:
          gen.go(f, gen.intr(s, ctx, here, t, ks))

# viewNode: a node's type as its parent sees it (view bang = edge boxes +
# intrinsic bang), from its own (intrinsic).
def view(s: St, +ctx: Ctx, +here: List<&2, U32>, +t: A) -> St & Sig:
  gen.go(big(), (s, GView{ctx, here, t, []}))

# Sorted tag lists
# ----------------

def u.heads(xs: List<&2, U32>, ys: List<&2, U32>) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      match ys:
        case Nil{}:
          LT{}
        case Con{y, yr}:
          U32.cmp(x, y)

# xs less ys.
def diff.go(fuel: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, c: Cmp) -> List<&2, U32>:
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
                  x <> diff.go(f, xr, Con{y, yr}, u.heads(xr, Con{y, yr}))
                case GT{}:
                  diff.go(f, Con{x, xr}, yr, u.heads(Con{x, xr}, yr))
                case EQ{}:
                  diff.go(f, xr, yr, u.heads(xr, yr))

def diff(+xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  diff.go(big(), xs, ys, u.heads(xs, ys))

def both.go(fuel: Nat, +xs: List<&2, U32>, +ys: List<&2, U32>, c: Cmp) -> List<&2, U32>:
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
                  x <> both.go(f, xr, Con{y, yr}, u.heads(xr, Con{y, yr}))
                case GT{}:
                  y <> both.go(f, Con{x, xr}, yr, u.heads(Con{x, xr}, yr))
                case EQ{}:
                  x <> both.go(f, xr, yr, u.heads(xr, yr))

# The union of two sorted lists.
def both(+xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  both.go(big(), xs, ys, u.heads(xs, ys))

def te.vs(x: TE, +y: U32) -> Cmp:
  match x:
    case TE{tag, cb, ct}:
      U32.cmp(tag, y)

def te.heads(xs: List<&2, TE>, ys: List<&2, U32>) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      match ys:
        case Nil{}:
          LT{}
        case Con{y, yr}:
          te.vs(x, y)

def te.key(x: TE) -> U32:
  match x:
    case TE{tag, cb, ct}:
      tag

def te.diff.go(fuel: Nat, +xs: List<&2, TE>, +ys: List<&2, U32>, c: Cmp) -> List<&2, U32>:
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
              keys(Con{x, xr})
            case Con{+y, +yr}:
              match c:
                case LT{}:
                  te.key(x) <> te.diff.go(f, xr, Con{y, yr}, te.heads(xr, Con{y, yr}))
                case GT{}:
                  te.diff.go(f, Con{x, xr}, yr, te.heads(Con{x, xr}, yr))
                case EQ{}:
                  te.diff.go(f, xr, yr, te.heads(xr, yr))

# The tags of a class that a sorted list lacks.
def te.diff(+xs: List<&2, TE>, +ys: List<&2, U32>) -> List<&2, U32>:
  te.diff.go(big(), xs, ys, te.heads(xs, ys))

# fnTagsOfCaptures: the code a capture position can hold, when it is
# applied.

def ft.one(no: Bool, +ct: U32, +vis: List<&2, U32>, rest: List<&2, FT>) -> List<&2, FT>:
  match no:
    case True{}:
      rest
    case False{}:
      FtCap{vis, ct} <> rest

def ft.caps(cs: List<&2, TE>, +vis: List<&2, U32>, rest: List<&2, FT>) -> List<&2, FT>:
  match cs:
    case Nil{}:
      rest
    case Con{e, er}:
      match e:
        case TE{tag, +cb, ct}:
          ft.one(U32.is_eq(cb, none()), ct, vis, ft.caps(er, vis, rest))

def fn.caps(+root: U32, +vis: List<&2, U32>, js: List<&2, FT>, +acc: List<&2, U32>, r: St & List<&2, TE>) -> St & FQ:
  (s, cs) = r
  (s, FQ{ft.caps(cs, root <> vis, js), acc})

def fn.seen(seen: Bool, s: St, +root: U32, +vis: List<&2, U32>, js: List<&2, FT>, +acc: List<&2, U32>) -> St & FQ:
  match seen:
    case True{}:
      (s, FQ{js, acc})
    case False{}:
      fn.caps(root, vis, js, acc, tg.get(s, root))

def fn.class(+vis: List<&2, U32>, js: List<&2, FT>, +acc: List<&2, U32>, r: St & U32) -> St & FQ:
  (s, +root) = r
  fn.seen(member(vis, root), s, root, vis, js, acc)

def fn.walked(+vis: List<&2, U32>, js: List<&2, FT>, +acc: List<&2, U32>, r: St & U32) -> St & FQ:
  (s, +w) = r
  (s, FQ{FtWalked{vis, w} <> js, acc})

def fn.ts(js: List<&2, FT>, +acc: List<&2, U32>, r: St & List<&2, U32>) -> St & FQ:
  (s, +ts) = r
  (s, FQ{js, both(acc, ts)})

def fn.w(k: K, s: St, +vis: List<&2, U32>, +w: U32, js: List<&2, FT>, +acc: List<&2, U32>) -> St & FQ:
  match k:
    case KCode{}:
      fn.ts(js, acc, tag.set(s, ix(w)))
    case KCap{}:
      (s, FQ{FtClass{vis, ix(w)} <> js, acc})
    case _:
      (s, FQ{js, acc})

def fn.step(s: St, j: FT, js: List<&2, FT>, +acc: List<&2, U32>) -> St & FQ:
  match j:
    case FtClass{+vis, +i}:
      fn.class(vis, js, acc, find(s, 4, i))
    case FtCap{+vis, +t}:
      fn.walked(vis, js, acc, walk(s, t))
    case FtWalked{+vis, +w}:
      fn.w(kind(w), s, vis, w, js, acc)

def fn.go(fuel: Nat, r: St & FQ) -> St & List<&2, U32>:
  match fuel:
    case 0n:
      (s, q) = r
      (s, [])
    case 1n+f:
      (s, q) = r
      match q:
        case FQ{js, +acc}:
          match js:
            case Nil{}:
              (s, acc)
            case Con{j, rest}:
              fn.go(f, fn.step(s, j, rest, acc))

def fn.tags(s: St, +i: U32) -> St & List<&2, U32>:
  fn.go(big(), (s, FQ{[FtClass{[], i}], []}))

# Dispatch
# --------

def drop.b(r: St & Bool) -> St:
  (s, c) = r
  s

# A body's contraction: its env domain bang must be boxed.
def dup.derive(d: Maybe<&2, Dup>, s: St, +b: U32, +fi: U32) -> St:
  match d:
    case Some{x}:
      match x:
        case Dup{path, loc}:
          drop.b(constrain(s, b, 2, 1, Blame{loc, "env path " ++ steps.show(path) ++ " duplicated in " ++ E.fi.show(fi)}))
    case None{}:
      s

def der.done(+b: U32, +t: U32, r: St & Sig) -> St & Der:
  (s, +sg) = r
  (s, Der{b, t, sg})

def der.t(+b: U32, +depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A, r: St & U32) -> St & Der:
  (s, +t) = r
  der.done(b, t, view(dup.derive(dup, s, b, fi), Ctx{b, t, (depth + 1 : U32)}, [], body))

def der.b(+depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A, r: St & U32) -> St & Der:
  (s, +b) = r
  der.t(b, depth, fi, dup, body, fresh.tau(s))

# A body walked at a dispatch site (captureTemplate's walk).
def derive(s: St, +depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A) -> St & Der:
  der.b(depth, fi, dup, body, fresh(s))

def first.done(+rk: U32, +v0: U32, +d: Der, r: St & U32) -> St & Der:
  (s, +v1) = r
  (ct.set(s, (rk * 2 + 1 : U32), (v1 - v0 : U32)), d)

def first.der(+rk: U32, +v0: U32, r: St & Der) -> St & Der:
  (s, +d) = r
  first.done(rk, v0, d, rd(s, 0))

def first.v0(+rk: U32, +depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A, r: St & U32) -> St & Der:
  (s, +v0) = r
  first.der(rk, v0, derive(s, depth, fi, dup, body))

def again.at(over: Bool, s: St, +depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A) -> St & Der:
  match over:
    case True{}:
      (fail(s, budget.err()), Der{0, 0, Sig{0, 0}})
    case False{}:
      derive(s, depth, fi, dup, body)

def again.base(+size: U32, +depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A, r: St & U32) -> St & Der:
  (s, +base) = r
  again.at(U32.is_ge((base + size : U32), var.budget()), s, depth, fi, dup, body)

def again.size(+depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A, r: St & U32) -> St & Der:
  (s, +size) = r
  again.base(size, depth, fi, dup, body, rd(s, 0))

# The first derivation of a body records how many variables it minted; a
# later one is refused when that many would reach the budget, as copying
# the Haskell's template is.
def derive.pick(first: Bool, s: St, +rk: U32, +depth: U32, +fi: U32, +dup: Maybe<&2, Dup>, +body: A) -> St & Der:
  match first:
    case True{}:
      first.v0(rk, depth, fi, dup, body, rd(s, 0))
    case False{}:
      again.size(depth, fi, dup, body, ct.get(s, (rk * 2 + 1 : U32)))

def dispatch.derived(+tag: U32, +env: Sig, +res: Sig, +loc: Lc.Loc, r: St & Der) -> St:
  (s, d) = r
  match d:
    case Der{+b, +t, +sg}:
      unify(unify.at(s, tag, loc, env, Sig{b, t}), loc, res, sg)

def dispatch.counted(over: Bool, s: St, +count: U32, +rk: U32, +site: Site, +bd: Bd) -> St:
  match over:
    case True{}:
      match bd:
        case Bd{h, fi, dup, t}:
          fail(s, GaveUp{"polyvariance budget: body " ++ E.fi.show(fi)
            ++ " needed more than 16384 derivations (dispatch structure likely exploding)"})
    case False{}:
      match site:
        case Site{fn, +env, +res, +depth, +loc, done}:
          match bd:
            case Bd{h, +fi, +dup, +t}:
              dispatch.derived(rk, env, res, loc,
                derive.pick(U32.is_eq(count, 0), ct.set(s, (rk * 2 : U32), (count + 1 : U32)), rk, depth, fi, dup, t))

def dispatch.count(+rk: U32, +site: Site, +bd: Bd, r: St & U32) -> St:
  (s, +count) = r
  dispatch.counted(U32.is_ge(count, poly.cap()), s, count, rk, site, bd)

def dispatch.found(m: Maybe<&2, Bd>, s: St, +rk: U32, +site: Site) -> St:
  match m:
    case Some{bd}:
      dispatch.count(rk, site, bd, ct.get(s, (rk * 2 : U32)))
    case None{}:
      fail(s, Internal{"dispatched code not in the DeferMap"})

def dispatch.code.p(+rk: U32, +site: Site, r: St & P) -> St:
  (s, +p) = r
  dispatch.found(body.at(p, rk), s, rk, site)

def dispatch.code(deep: Bool, s: St, +rk: U32, +site: Site, +loc: Lc.Loc) -> St:
  match deep:
    case True{}:
      fail(s, GaveUp{"code dispatch depth exceeded 1024 (unbounded self-application?): " ++ Lf.loc.show(loc, False{})})
    case False{}:
      dispatch.code.p(rk, site, prog(s))

def unify.to(+loc: Lc.Loc, +res: Sig, r: St & Sig) -> St:
  (s, +g) = r
  unify(s, loc, res, g)

def gate.ct(+loc: Lc.Loc, +res: Sig, r: St & U32) -> St:
  (s, +ct) = r
  unify.to(loc, res, plain(s, loc, "gate switch function is locally unboxed", ct))

def gate.scr(+loc: Lc.Loc, +env: Sig, +res: Sig, r: St & U32) -> St:
  (s, +scr) = r
  gate.ct(loc, res, fresh.code(unify(s, loc, env, Sig{scr, data()}), t.gatefn()))

def gf.t(+loc: Lc.Loc, +env: Sig, +res: Sig, +se: Sig, +st: Sig, +bb: U32, r: St & U32) -> St:
  (s, +t) = r
  unify(unify(unify(s, loc, env, Sig{bb, t}), loc, res, se), loc, res, st)

def gf.bb(+loc: Lc.Loc, +env: Sig, +res: Sig, +se: Sig, +st: Sig, r: St & U32) -> St:
  (s, +bb) = r
  gf.t(loc, env, res, se, st, bb, pair.new(s, Pr{sig.b(se), sig.t(se), sig.b(st), sig.t(st)}))

def gf.st(+loc: Lc.Loc, +env: Sig, +res: Sig, +se: Sig, r: St & Sig) -> St:
  (s, +st) = r
  gf.bb(loc, env, res, se, st, fresh(s))

def gf.se(+loc: Lc.Loc, +env: Sig, +res: Sig, r: St & Sig) -> St:
  (s, +se) = r
  gf.st(loc, env, res, se, fresh.sig(s))

def abort.ct(+loc: Lc.Loc, +res: Sig, r: St & U32) -> St:
  (s, +ct) = r
  unify.to(loc, res, plain(s, loc, "abort continuation is locally unboxed", ct))

def dispatch.builtin(b: Bi, s: St, site: Site) -> St:
  match b:
    case BiGate{}:
      match site:
        case Site{fn, +env, +res, depth, +loc, done}:
          gate.scr(loc, env, res, forced.zero(s, Blame{loc, "gate scrutinee must be unboxed data"}))
    case BiGateFn{}:
      match site:
        case Site{fn, +env, +res, depth, +loc, done}:
          gf.se(loc, env, res, fresh.sig(s))
    case BiAbort{}:
      match site:
        case Site{fn, env, +res, depth, +loc, done}:
          abort.ct(loc, res, fresh.code(s, t.cont()))
    case BiCont{}:
      match site:
        case Site{fn, +env, +res, depth, +loc, done}:
          unify(s, loc, env, res)

def dispatch.k(code: Bool, s: St, +tag: U32, +site: Site) -> St:
  match code:
    case True{}:
      match site:
        case Site{fn, env, res, +depth, +loc, done}:
          dispatch.code(U32.is_ge(depth, depth.cap()), s, tag, site, loc)
    case False{}:
      dispatch.builtin(builtin(tag), s, site)

# dispatchTag: the constraints of applying one tag at one site.
def dispatch(s: St, +site: Site, +tag: U32) -> St:
  dispatch.k(U32.is_lt(tag, t.gate()), s, tag, site)

# The tags in order, while nothing has failed.
def dispatch.all(ts: List<&2, U32>, +site: Site, r: St & Bool) -> St:
  match ts:
    case Nil{}:
      (s, ok) = r
      s
    case Con{+t, rest}:
      (s, ok) = r
      match ok:
        case True{}:
          dispatch.all(rest, site, ok.of(dispatch(s, site, t)))
        case False{}:
          s

def dispatch.new.at(none: Bool, s: St, +k: U32, +site: Site, new: List<&2, U32>) -> St & Bool:
  match none:
    case True{}:
      (s, False{})
    case False{}:
      (dispatch.all(new, site, ok.of(site.set(s, k, site))), True{})

def dispatch.new.with(+new: List<&2, U32>, s: St, +k: U32, +site: Site) -> St & Bool:
  dispatch.new.at(List.is_empty(&2, U32, new), s, k, site, new)

# dispatchNew: the tags this site has not dispatched yet; marked first.
def dispatch.new(s: St, +k: U32, +site: Site, +tags: List<&2, U32>) -> St & Bool:
  match site:
    case Site{+fn, +env, +res, +depth, +loc, +done}:
      dispatch.new.with(diff(tags, done), s, k, Site{fn, env, res, depth, loc, both(done, tags)})

def site.ts(+k: U32, +site: Site, r: St & List<&2, U32>) -> St & Bool:
  (s, +ts) = r
  dispatch.new(s, k, site, ts)

def dispatch.te.at(none: Bool, s: St, +k: U32, +site: Site, +ts: List<&2, TE>, new: List<&2, U32>) -> St & Bool:
  match none:
    case True{}:
      (s, False{})
    case False{}:
      match site:
        case Site{+fn, +env, +res, +depth, +loc, +done}:
          dispatch.new.at(False{}, s, k, Site{fn, env, res, depth, loc, both(done, keys(ts))}, new)

def dispatch.te(+new: List<&2, U32>, s: St, +k: U32, +site: Site, +ts: List<&2, TE>) -> St & Bool:
  dispatch.te.at(List.is_empty(&2, U32, new), s, k, site, ts, new)

# A code class at a site: the tags not dispatched there yet, compared
# without listing the class's tags first.
def site.caps(+k: U32, +site: Site, r: St & List<&2, TE>) -> St & Bool:
  match site:
    case Site{fn, env, res, depth, loc, +done}:
      (s, +ts) = r
      dispatch.te(te.diff(ts, done), s, k, site, ts)

def site.loc(s: Site) -> Lc.Loc:
  match s:
    case Site{fn, env, res, depth, loc, done}:
      loc

def site.fn(s: Site) -> U32:
  match s:
    case Site{fn, env, res, depth, loc, done}:
      fn

def site.walked(k2: K, s: St, +k: U32, +site: Site, +w: U32) -> St & Bool:
  match k2:
    case KCode{}:
      site.caps(k, site, caps(s, ix(w)))
    case KCap{}:
      site.ts(k, site, fn.tags(s, ix(w)))
    case KPair{}:
      (fail(s, TypeMismatch{site.loc(site), "applied value is pair, not code"}), False{})
    case _:
      (s, False{})

def site.w(+k: U32, +site: Site, r: St & U32) -> St & Bool:
  (s, +w) = r
  site.walked(kind(w), s, k, site, w)

def site.read(+k: U32, r: St & Site) -> St & Bool:
  (s, +site) = r
  site.w(k, site, walk(s, site.fn(site)))

# One site: dispatch whatever new code its function position holds.
def site.resolve(s: St, +k: U32) -> St & Bool:
  site.read(k, site.get(s, k))

def site.flag(c: Bool, r: St & Bool) -> St & SS:
  match c:
    case True{}:
      (s, ok) = r
      (s, Bool.pick(SS, ok, SsNew{}, SsStop{}))
    case False{}:
      (s, ok) = r
      (s, Bool.pick(SS, ok, SsNone{}, SsStop{}))

def site.flagged(r: St & Bool) -> St & SS:
  (s, c) = r
  site.flag(c, ok.of(s))

def site.step.at(more: Bool, s: St, +k: U32) -> St & SS:
  match more:
    case True{}:
      site.flagged(site.resolve(s, k))
    case False{}:
      (s, SsStop{})

# Site k of n.
def site.step(s: St, +k: U32, +n: U32) -> St & SS:
  site.step.at(U32.is_lt(k, n), s, k)

# One round over the sites there were when it began; r is how the site
# before k went.
def round(fuel: Nat, +k: U32, +n: U32, +changed: Bool, r: St & SS) -> St & Bool:
  match fuel:
    case 0n:
      (s, c) = r
      (s, changed)
    case 1n+f:
      (s, c) = r
      match c:
        case SsNone{}:
          round(f, (k + 1 : U32), n, changed, site.step(s, k, n))
        case SsNew{}:
          round(f, (k + 1 : U32), n, True{}, site.step(s, k, n))
        case SsStop{}:
          (s, changed)

def start.of(r: St & Bool) -> St & SS:
  (s, ok) = r
  (s, Bool.pick(SS, ok, SsNone{}, SsStop{}))

def applies.over(over: Bool, r: St & U32) -> St & Bool:
  match over:
    case True{}:
      (s, n) = r
      (fail(s, GaveUp{"application dispatch did not converge"}), False{})
    case False{}:
      (s, +n) = r
      round(U32.to_nat((n + 2 : U32)), 0, n, False{}, start.of(ok.of(s)))

def applies.go(fuel: Nat, +rn: U32, r: St & Bool) -> St:
  match fuel:
    case 0n:
      (s, c) = r
      s
    case 1n+f:
      (s, c) = r
      match c:
        case False{}:
          s
        case True{}:
          applies.go(f, (rn + 1 : U32), applies.over(U32.is_gt(rn, 10000), rd(s, 5)))

# resolveApplies: dispatch every tag every site's function position holds,
# to a fixpoint.
def applies(s: St) -> St:
  applies.go(10003n, 0, (s, True{}))

# virtualMainApply: the run applies the program to its input, so that
# application is certified too: a closure package applies its code to
# (input, captures), bare code to the input alone.

def register.so(+fn: U32, +env: Sig, r: St & Sig) -> St:
  (s, +so) = r
  site.add(s, Site{fn, env, so, 0, Lc.Gen{"virtual application of main to input"}, []})

def register(s: St, +fn: U32, +env: Sig) -> St:
  register.so(fn, env, fresh.sig(s))

def vp.t(+wc: U32, +eb: U32, r: St & U32) -> St:
  (s, +t) = r
  register(s, wc, Sig{eb, t})

def vp.eb(+wc: U32, +ib: U32, +b2: U32, +t2: U32, r: St & U32) -> St:
  (s, +eb) = r
  vp.t(wc, eb, pair.new(s, Pr{ib, data(), b2, t2}))

def vp.ib(+wc: U32, +b2: U32, +t2: U32, r: St & U32) -> St:
  (s, +ib) = r
  vp.eb(wc, ib, b2, t2, fresh(s))

def virtual.pair(ok: Bool, s: St, +wc: U32, +b2: U32, +t2: U32) -> St:
  match ok:
    case True{}:
      vp.ib(wc, b2, t2, fresh(s))
    case False{}:
      s

def virtual.wc(+b2: U32, +t2: U32, r: St & U32) -> St:
  (s, +wc) = r
  virtual.pair(appliable(wc), s, wc, b2, t2)

def virtual.pr(r: St & Pr) -> St:
  (s, pr) = r
  match pr:
    case Pr{b1, +t1, +b2, +t2}:
      virtual.wc(b2, t2, walk(s, t1))

def vt.ib(+w: U32, r: St & U32) -> St:
  (s, +ib) = r
  register(s, w, Sig{ib, data()})

def virtual.top(ok: Bool, s: St, +w: U32) -> St:
  match ok:
    case True{}:
      vt.ib(w, fresh(s))
    case False{}:
      s

def virtual.at(pair: Bool, s: St, +w: U32) -> St:
  match pair:
    case True{}:
      virtual.pr(pair.get(s, w))
    case False{}:
      virtual.top(appliable(w), s, w)

def virtual.w(r: St & U32) -> St:
  (s, +w) = r
  virtual.at(is.pair(w), s, w)

def virtual(s: St, +sg: Sig) -> St:
  virtual.w(walk(s, sig.t(sg)))

def dup.top(d: Maybe<&2, Dup>, s: St, +b: U32, +what: String) -> St:
  match d:
    case Some{x}:
      match x:
        case Dup{path, loc}:
          drop.b(constrain(s, b, 2, 1, Blame{loc, what ++ " path " ++ steps.show(path) ++ " duplicated"}))
    case None{}:
      s

def top.t(+b: U32, +what: String, +dup: Maybe<&2, Dup>, +term: A, r: St & U32) -> St & Sig:
  (s, +t) = r
  view(dup.top(dup, s, b, what), Ctx{b, t, 0}, [], term)

def top.b(+what: String, +dup: Maybe<&2, Dup>, +term: A, r: St & U32) -> St & Sig:
  (s, +b) = r
  top.t(b, what, dup, term, fresh.tau(s))

# The walk of a top-level term over its own env.
def walk.top(s: St, +what: String, +dup: Maybe<&2, Dup>, +term: A) -> St & Sig:
  top.b(what, dup, term, fresh(s))


# Solving
# -------


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


# Nothing merges classes while the solver runs, so the equations' roots
# are found once and their classes copied to a table of their own; both
# passes then work on tables. A derived blame is built only when a class
# keeps it or a conflict names it.


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


# The solver on the state
# -----------------------

def roots.go(ls: List<&2, U32>, acc: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  match ls:
    case Nil{}:
      (m, +x) = r
      (m, List.reverse(&2, U32, x <> acc))
    case Con{+l, rest}:
      (m, +x) = r
      roots.go(rest, x <> acc, find.m(m, 1, l))

# The class roots of these bangs.
def roots.of(ls: List<&2, U32>, m: Array<U32>) -> Array<U32> & List<&2, U32>:
  match ls:
    case Nil{}:
      (m, [])
    case Con{+l, rest}:
      roots.go(rest, [], find.m(m, 1, l))

def eq.rhs(+blame: Blame, ls: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & SumEq:
  (m, +rt) = r
  (m, SumEq{ls, rt, blame})

def eq.lhs(+rhs: U32, +blame: Blame, r: Array<U32> & List<&2, U32>) -> Array<U32> & SumEq:
  (m, ls) = r
  eq.rhs(blame, ls, find.m(m, 1, rhs))

def eq.res(e: SumEq, m: Array<U32>) -> Array<U32> & SumEq:
  match e:
    case SumEq{lhs, +rhs, +blame}:
      eq.lhs(rhs, blame, roots.of(lhs, m))

def resolve.go(es: List<&2, SumEq>, acc: List<&2, SumEq>, r: Array<U32> & SumEq) -> Array<U32> & List<&2, SumEq>:
  match es:
    case Nil{}:
      (m, e) = r
      (m, List.reverse(&2, SumEq, e <> acc))
    case Con{e2, rest}:
      (m, e) = r
      resolve.go(rest, e <> acc, eq.res(e2, m))

# resolveEqs: the equations over class roots.
def resolve.eqs(es: List<&2, SumEq>, m: Array<U32>) -> Array<U32> & List<&2, SumEq>:
  match es:
    case Nil{}:
      (m, [])
    case Con{e, rest}:
      resolve.go(rest, [], eq.res(e, m))

def class.k(free: Bool, zero: Bool, +n: U32, b: Blame) -> Class:
  match free:
    case True{}:
      Unrestricted{}
    case False{}:
      match zero:
        case True{}:
          ForcedZero{b}
        case False{}:
          ForcedLevel{n, b}

def rc.blame(+root: U32, +c: U32, r: St & Blame) -> St & RC:
  (s, b) = r
  (s, RC{root, class.k(U32.is_zero((c .&. 3 : U32)), U32.is_eq((c .&. 3 : U32), 1), (c >> 2n : U32), b)})

def rc.c(+root: U32, r: St & U32) -> St & RC:
  (s, +c) = r
  rc.blame(root, c, blame.of(s, root))

# A root's class, as the solver keeps it.
def class.read(s: St, +root: U32) -> St & RC:
  rc.c(root, rd(s, (root * 8 + 18 : U32)))

def table.go(rs: List<&2, U32>, t: Array<Class>, r: St & RC) -> St & Array<Class>:
  match rs:
    case Nil{}:
      (s, rc) = r
      match rc:
        case RC{+root, c}:
          (s, Array.set(Class, t, root, c))
    case Con{+x, rest}:
      (s, rc) = r
      match rc:
        case RC{+root, c}:
          table.go(rest, Array.set(Class, t, root, c), class.read(s, x))

# The roots' classes, in a table of their own.
def table(rs: List<&2, U32>, t: Array<Class>, s: St) -> St & Array<Class>:
  match rs:
    case Nil{}:
      (s, t)
    case Con{+x, rest}:
      table.go(rest, t, class.read(s, x))

def solve.done(s: St, m: Maybe<&2, Err>) -> St:
  match m:
    case None{}:
      s
    case Some{e}:
      fail(s, e)

def solve.tab(+rs: List<&2, SumEq>, +d: Nat, r: St & Array<Class>) -> St:
  (s, cls) = r
  solve.done(s, assign(rs, d, rounds(U32.to_nat((U32.from_nat(List.length(&2, SumEq, rs)) * 4 + 64 : U32)), rs, PGo{cls, True{}})))

def solve.size(+rs: List<&2, SumEq>, r: St & U32) -> St:
  (s, +size) = r
  solve.tab(rs, (U32.log2(size) - 3n : Nat), table(eq.roots(rs, []), Array.new(Class, (U32.log2(size) - 3n : Nat), Unrestricted{}), s))

def solve.res(ps: Array<Pr>, tg: Array<List<&2, TE>>, x: X, r: Array<U32> & List<&2, SumEq>) -> St:
  (m, +rs) = r
  solve.size(rs, rd(St{m, ps, tg, x}, 1))

def solve.eqs(s: St) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, +eqs, err, p}:
          solve.res(ps, tg, X{sites, bl, ct, eqs, err, p}, resolve.eqs(eqs, m))

def solve.ok(r: St & Bool) -> St:
  (s, ok) = r
  match ok:
    case True{}:
      solve.eqs(s)
    case False{}:
      s

# propagate, then assignValues, over the equations' roots; not after a
# failure.
def solve(s: St) -> St:
  solve.ok(ok.of(s))

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


def s.both.go(fuel: Nat, +xs: List<&2, String>, +ys: List<&2, String>, c: Cmp) -> List<&2, String>:
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
                  x <> s.both.go(f, xr, Con{y, yr}, str.heads(xr, Con{y, yr}))
                case GT{}:
                  y <> s.both.go(f, Con{x, xr}, yr, str.heads(Con{x, xr}, yr))
                case EQ{}:
                  x <> s.both.go(f, xr, yr, str.heads(xr, yr))

# The union of two sorted lists.
def s.both(+xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  s.both.go(big(), xs, ys, str.heads(xs, ys))
def body.fi(b: Lf.Body) -> U32:
  match b:
    case Lf.Body{fi, body}:
      fi

def body.l(b: Lf.Body) -> Lf.L:
  match b:
    case Lf.Body{fi, body}:
      body


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
      s.both(acc, [h])
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
def verdicts.map(xs: List<&2, HB>, acc: Map<&2, Bool>) -> Map<&2, Bool>:
  match xs:
    case Nil{}:
      acc
    case Con{x, rest}:
      match x:
        case HB{h, ok}:
          verdicts.map(rest, Map.set(&2, Bool, acc, h, ok))

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

# Capture shapes
# --------------

def sh.walked(js: List<&2, SJ>, vs: List<&2, Lf.Shape>, r: St & U32) -> St & SQ:
  (s, +w) = r
  (s, SQ{SjWalked{kind(w), w} <> js, vs})

def sh.pair(js: List<&2, SJ>, vs: List<&2, Lf.Shape>, r: St & Pr) -> St & SQ:
  (s, pr) = r
  match pr:
    case Pr{b1, t1, b2, t2}:
      (s, SQ{SjTau{t1} <> SjTau{t2} <> SjPair{} <> js, vs})

def sh.join(vs: List<&2, Lf.Shape>) -> List<&2, Lf.Shape>:
  match vs:
    case Con{b, r1}:
      match r1:
        case Con{a, r2}:
          Lf.CapPair{a, b} <> r2
        case Nil{}:
          [b]
    case Nil{}:
      []

def sh.step(s: St, j: SJ, js: List<&2, SJ>, vs: List<&2, Lf.Shape>) -> St & SQ:
  match j:
    case SjTau{+t}:
      sh.walked(js, vs, walk(s, t))
    case SjWalked{k, +w}:
      match k:
        case KData{}:
          (s, SQ{js, Lf.CapData{} <> vs})
        case KPair{}:
          sh.pair(js, vs, pair.get(s, w))
        case KCode{}:
          (s, SQ{js, Lf.CapCode{} <> vs})
        case _:
          (s, SQ{js, Lf.CapOther{} <> vs})
    case SjPair{}:
      (s, SQ{js, sh.join(vs)})

def sh.go(fuel: Nat, r: St & SQ) -> St & Lf.Shape:
  match fuel:
    case 0n:
      (s, q) = r
      (s, Lf.CapOther{})
    case 1n+f:
      (s, q) = r
      match q:
        case SQ{js, vs}:
          match js:
            case Con{j, rest}:
              sh.go(f, sh.step(s, j, rest, vs))
            case Nil{}:
              match vs:
                case Con{v, more}:
                  (s, v)
                case Nil{}:
                  (s, Lf.CapOther{})

# shapeOfSigma, of a type.
def shape(s: St, +t: U32) -> St & Lf.Shape:
  sh.go(big(), (s, SQ{[SjTau{t}], []}))

def shp.add(+h: String, acc: Map<&2, Lf.Shape>, r: St & Lf.Shape) -> St & Map<&2, Lf.Shape>:
  (s, +sh) = r
  (s, shape.add(h, sh, Map.has(&2, Lf.Shape, acc, h)))

def shp.te(ok: Bool, s: St, +tag: U32, +ct: U32, +p: P, acc: Map<&2, Lf.Shape>) -> St & Map<&2, Lf.Shape>:
  match ok:
    case True{}:
      shp.add(bd.hash(body.at(p, tag)), acc, shape(s, ct))
    case False{}:
      (s, acc)

def shapes.caps(ts: List<&2, TE>, +p: P, r: St & Map<&2, Lf.Shape>) -> St & Map<&2, Lf.Shape>:
  match ts:
    case Nil{}:
      r
    case Con{e, rest}:
      match e:
        case TE{+tag, +cb, +ct}:
          (s, acc) = r
          shapes.caps(rest, p, shp.te(U32.is_lt(tag, t.gate()) && U32.is_ne(cb, none()), s, tag, ct, p, acc))

def shapes.ts(+p: P, acc: Map<&2, Lf.Shape>, r: St & List<&2, TE>) -> St & Map<&2, Lf.Shape>:
  (s, ts) = r
  shapes.caps(ts, p, (s, acc))

def shapes.go(fuel: Nat, more: Bool, +i: U32, +n: U32, +p: P, r: St & Map<&2, Lf.Shape>) -> St & Map<&2, Lf.Shape>:
  match fuel:
    case 0n:
      r
    case 1n+f:
      match more:
        case False{}:
          r
        case True{}:
          (s, acc) = r
          shapes.go(f, U32.is_lt((i + 1 : U32), n), (i + 1 : U32), n, p, shapes.ts(p, acc, tg.get(s, i)))

def shapes.n(+p: P, r: St & U32) -> St & Map<&2, Lf.Shape>:
  (s, +n) = r
  shapes.go(U32.to_nat((n + 1 : U32)), U32.is_lt(0, n), 0, n, p, (s, Map.new(&2, Lf.Shape)))

def shapes.p(r: St & P) -> St & Map<&2, Lf.Shape>:
  (s, +p) = r
  shapes.n(p, rd(s, 0))

# groundCaptureShapes: every closure package's capture shape, met per hash
# over the sites it is built at.
def shapes(s: St) -> St & Map<&2, Lf.Shape>:
  shapes.p(prog(s))

# The whole analysis
# ------------------

def first.err(es: List<&2, Err>) -> Maybe<&2, Err>:
  match es:
    case Nil{}:
      None{}
    case Con{e, rest}:
      Some{e}

def st.err(s: St) -> Maybe<&2, Err>:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, bl, ct, eqs, err, p}:
          first.err(err)

def an.walked(apply: Bool, r: St & Sig) -> St & Sig:
  match apply:
    case True{}:
      (s, +sg) = r
      (solve(applies(virtual(applies(s), sg))), sg)
    case False{}:
      (s, +sg) = r
      (solve(applies(s)), sg)

# analyzeTopWith: a top-level term (the program, or a body standalone) over
# its own env, every dispatch, and the solve; the program is also applied
# to its input.
def analyze(s: St, apply: Bool, +what: String, +dup: Maybe<&2, Dup>, +term: A) -> St & Sig:
  an.walked(apply, walk.top(s, what, dup, term))

def failure.of(r: St & Sig) -> Maybe<&2, Err>:
  (s, sg) = r
  st.err(s)

# summarizeBody: why a body does not certify standalone, if it does not.
def standalone(+p: P, b: Bd) -> Maybe<&2, Err>:
  match b:
    case Bd{h, +fi, +dup, +t}:
      failure.of(analyze(st.new(p), False{}, "env of lifted body " ++ E.fi.show(fi), dup, t))

def verdict.one(+p: P, m: Maybe<&2, Bd>) -> List<&2, HB>:
  match m:
    case Some{b}:
      match b:
        case Bd{+h, +fi, +dup, +t}:
          [HB{h, Maybe.is_none(&2, Err, standalone(p, Bd{h, fi, dup, t}))}]
    case None{}:
      []

def verdicts.go(+fuel: Nat, +p: P, +lo: U32, +n: U32, one: Bool) -> List<&2, HB>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match one:
        case True{}:
          verdict.one(p, body.at(p, lo))
        case False{}:
          a b = verdicts.go(f, p, lo, U32.shr(n), U32.is_le(U32.shr(n), 1)) verdicts.go(f, p, (lo + U32.shr(n) : U32), (n - U32.shr(n) : U32), U32.is_le((n - U32.shr(n) : U32), 1))
          List.append(&2, HB, a, b)

def p.n(p: P) -> U32:
  match p:
    case P{n, size, bt}:
      n

# Every body's standalone verdict (summarizeBody), computed in parallel: a
# balanced fork-join over the bodies in hash order.
def verdicts(+p: P) -> Map<&2, Bool>:
  verdicts.map(verdicts.go(U32.to_nat((U32.from_nat(U32.log2(p.n(p))) + 3 : U32)), p, 0, p.n(p), U32.is_le(p.n(p), 1)),
    Map.new(&2, Bool))

def main.at(m: Maybe<&2, Err>, sh: Lf.Shape) -> Result<&2, &2, Err, Lf.Shape>:
  match m:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{sh}

def main.done(r: St & Lf.Shape) -> Result<&2, &2, Err, Lf.Shape>:
  (s, sh) = r
  main.at(st.err(s), sh)


# The entry points
# ----------------

def main.sg(r: St & Sig) -> Result<&2, &2, Err, Lf.Shape>:
  (s, +sg) = r
  main.done(shape(s, sig.t(sg)))

# The program's main shape, or why it does not certify.
def main.shape(+p: P, +dup: Maybe<&2, Dup>, +term: A) -> Result<&2, &2, Err, Lf.Shape>:
  main.sg(analyze(st.new(p), True{}, "program input", dup, term))

def inferred.at(r: DR, main: Result<&2, &2, Err, Lf.Shape>) -> Result<&2, &2, Err, Lf.Shape>:
  match r:
    case DR{memo, failed}:
      match failed:
        case Some{d}:
          Fail{DependencyFailed{d}}
        case None{}:
          main

def inferred.with(+bodies: Map<&2, Lf.Body>, +main: Lf.L, +pre: Map<&2, Bool>, r: Result<&2, &2, Err, Lf.Shape>) -> Result<&2, &2, Err, Lf.Shape>:
  inferred.at(check.deps(bodies, pre, refs(main, []), Map.new(&2, Bool)), r)

def inferred.p(+bodies: Map<&2, Lf.Body>, +main: Lf.L, +rk: Map<&2, U32>, +p: P) -> Result<&2, &2, Err, Lf.Shape>:
  pre r = verdicts(p) main.shape(p, dup.of(main), to.a(main, rk))
  inferred.with(bodies, main, pre, r)

# ealLiftedMain: the program's main shape, or why it does not certify, its
# dependencies first. The bodies' standalone verdicts and the whole
# program's analysis run in parallel.
def inferred(t: Lf.Lifted) -> Result<&2, &2, Err, Lf.Shape>:
  match t:
    case Lf.Lifted{+bodies, +main}:
      inferred.p(bodies, main, ranks(bodies), program(bodies, ranks(bodies)))

# certifyMain: why the program is not certified, if it is not.
def certify(t: Lf.Lifted) -> Maybe<&2, Err>:
  certified(inferred(t))

# ealGuidance's verdicts: whether each body certifies, its dependencies
# first.
def gated(+bodies: Map<&2, Lf.Body>) -> Map<&2, Bool>:
  dr.memo(deps(big(), bodies, verdicts(program(bodies, ranks(bodies))),
    DjAll{Map.keys(&2, Lf.Body, bodies), Map.new(&2, Bool)}))

def summary.at(+fi: U32, +body: Lf.L, +rk: Map<&2, U32>, +p: P) -> Maybe<&2, Err>:
  standalone(p, Bd{"", fi, dup.of(body), to.a(body, rk)})

# summarizeBody's failure: why a body does not certify standalone, if it
# does not.
def summary(+bodies: Map<&2, Lf.Body>, b: Lf.Body) -> Maybe<&2, Err>:
  match b:
    case Lf.Body{+fi, +body}:
      summary.at(fi, body, ranks(bodies), program(bodies, ranks(bodies)))

def lay.done(r: St & Map<&2, Lf.Shape>) -> Maybe<&2, Map<&2, Lf.Shape>>:
  (s, m) = r
  Some{m}

def lay.flag(r: St & Bool) -> Maybe<&2, Map<&2, Lf.Shape>>:
  (s, ok) = r
  match ok:
    case True{}:
      lay.done(shapes(s))
    case False{}:
      None{}

def lay.sg(r: St & Sig) -> Maybe<&2, Map<&2, Lf.Shape>>:
  (s, sg) = r
  lay.flag(ok.of(s))

# The capture shapes of the whole program's closure packages, when its
# analysis succeeds.
def main.shapes(+p: P, +dup: Maybe<&2, Dup>, +term: A) -> Maybe<&2, Map<&2, Lf.Shape>>:
  lay.sg(analyze(st.new(p), True{}, "program input", dup, term))

def layouts.ran(+bodies: Map<&2, Lf.Body>, +main: Lf.L, +p: P, r: Maybe<&2, Map<&2, Lf.Shape>>) -> Map<&2, Lf.Shape>:
  match r:
    case None{}:
      Map.new(&2, Lf.Shape)
    case Some{m}:
      layouts.with(bodies, main, verdicts(p), m)

def layouts.p(+bodies: Map<&2, Lf.Body>, +main: Lf.L, +rk: Map<&2, U32>, +p: P) -> Map<&2, Lf.Shape>:
  layouts.ran(bodies, main, p, main.shapes(p, dup.of(main), to.a(main, rk)))

# ealCaptureLayouts: the capture shape of each closure code the whole
# program builds, for the codes that certify standalone; none when the
# program does not certify. The bodies' verdicts matter only when the
# whole program's analysis succeeds, so only then are they computed.
def layouts(t: Lf.Lifted) -> Map<&2, Lf.Shape>:
  match t:
    case Lf.Lifted{+bodies, +main}:
      layouts.p(bodies, main, ranks(bodies), program(bodies, ranks(bodies)))
