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
# - Steps the Haskell repeats to no effect are skipped: a pair already
#   collapsed to data and unboxed bangs (ground) is not collapsed again, a
#   type is not unified with itself, and an apply site whose code class is
#   the same, with the same tags, as at its last look is not looked at
#   again.
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
#   blame (a number in the blames' table), its tag class's parent plus one
#   and a stamp of its tags. Before the variables, the table keeps its
#   counters. A pair has eight words in a table of its own, an apply site
#   four (besides its record).
# - The solver copies the classes its equations name into tables of words
#   and runs over the equations as rows of words.
# - A failure is kept in the state, the first one only, and every loop
#   stops at it.
# - Branches go on small enumerations (a type's kind, a class merge's
#   outcome) or on Bools, never on a U32's literal values: a U32 case
#   compiles to a test per bit, each with its own copy of the default.

# Types
# -----

type Blame is Data:
  Blame{+loc: Lc.Loc, +why: String}

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
# (ApplySite, but for its function position, in the sites' rows); `done`
# are the tags already dispatched there.
type Site is Data:
  Site{+env: Sig, +res: Sig, +depth: U32, +loc: Lc.Loc, +done: List<&2, U32>}

# What is not the variables: the apply sites and their rows, the blames,
# two counters per body (derivations so far, and the variables the first
# one minted), the sum equations newest first, the first failure (a list,
# which keeps it boxed), and the program.
type X is Type:
  X{sites: Array<Site>, sv: Array<U32>, bl: Array<Blame>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P}

# The state: the variables and counters, the pairs, the tags of each tag
# class root, and the rest.
type St is Type:
  St{m: Array<U32>, ps: Array<U32>, tg: Array<List<&2, TE>>, x: X}

# Work for the unifier, all at a visited set of capture classes and a
# dispatch mode (the dispatching tag, or none()).
type W is Data:
  WSig{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: Sig, +b: Sig}
  WTau{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32}
  WColl{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +s: Sig}
  WGround{+p: U32}

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

# A derivation of a code body: its env domain bang and type, and its result.
type Der is Data:
  Der{+b: U32, +t: U32, +s: Sig}

# A step of occurs: whether it hit, and the types left.
type OS is Data:
  OS{+hit: Bool, +ts: List<&2, U32>}

# A class word's kind: unrestricted, forced to zero, forced to a level.
type CK is Data:
  CFree{}
  CZero{}
  CLevel{}

# The solver's state: each root's class word (as a variable's) and blame
# (by the root's number), the equations as rows of words in q, each
# [summands, total, summand roots...], with their blames in qb, each
# root's value (its class's lower bound until the assignment) and how many
# equations it is a summand of, and whether the pass's round changed
# anything; or the first failure.
type Sv is Type:
  Sv{c: Array<U32>, cb: Array<Blame>, q: Array<U32>, qb: Array<Blame>, v: Array<U32>, n: Array<U32>, ch: Bool}
  SvErr{e: Err}

# An equation's summands: whether all are forced to zero, the sum of their
# lower bounds, how many may be boxed, and the last of those.
type Sm is Data:
  Sm{+fz: Bool, +sum: U32, +free: U32, +lone: U32}

# The solver's passes over the rows.
type Pass is Data:
  PProp{}
  PAdjust{}
  PHolds{}

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
  Site{Sig{0, 0}, Sig{0, 0}, 0, Lc.Unknown{}, []}

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
      St{m.new(), Array.new(U32, 9n, 0), Array.new(List<&2, TE>, 8n, te.none()),
         X{Array.new(Site, 6n, site.none()), Array.new(U32, 8n, 0), Array.new(Blame, 6n, blame.none()),
           Array.new(U32, (U32.log2((n * 2 + 1 : U32)) + 1n : Nat), 0), [], [], p}}

def st.m(ps: Array<U32>, tg: Array<List<&2, TE>>, x: X, r: Array<U32> & U32) -> St & U32:
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
    case X{sites, sv, bl, ct, eqs, err, p}:
      X{sites, sv, bl, ct, eqs, [e], p}

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

# Pair type t (pair n is n * 8 + 4) has its words in ps from t - 4: its
# sides' bangs and types (b1, t1, b2, t2), then, at t itself, whether it
# is ground (see colls).

def pair.set(s: St, +n: U32, pr: Pr) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      match pr:
        case Pr{+b1, +t1, +b2, +t2}:
          (St{Array.set(U32, m, 2, (n + 1 : U32)),
              Array.set(U32, Array.set(U32, Array.set(U32, Array.set(U32, ps, (n * 8 : U32), b1), (n * 8 + 1 : U32), t1),
                (n * 8 + 2 : U32), b2), (n * 8 + 3 : U32), t2),
              tg, x}, (n * 8 + 4 : U32))

def pair.grow(s: St, +cap: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      St{Array.set(U32, m, 3, (cap * 2 : U32)), ANode{ps, Array.new(U32, U32.log2((cap * 8 : U32)), 0)}, tg, x}

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

def pr.t2(+b1: U32, +t1: U32, +b2: U32, r: Array<U32> & U32) -> Array<U32> & Pr:
  (ps, +t2) = r
  (ps, Pr{b1, t1, b2, t2})

def pr.b2(+o: U32, +b1: U32, +t1: U32, r: Array<U32> & U32) -> Array<U32> & Pr:
  (ps, +b2) = r
  pr.t2(b1, t1, b2, ps[(o + 3 : U32)])

def pr.t1(+o: U32, +b1: U32, r: Array<U32> & U32) -> Array<U32> & Pr:
  (ps, +t1) = r
  pr.b2(o, b1, t1, ps[(o + 2 : U32)])

def pr.b1(+o: U32, r: Array<U32> & U32) -> Array<U32> & Pr:
  (ps, +b1) = r
  pr.t1(o, b1, ps[(o + 1 : U32)])

def pair.got(m: Array<U32>, tg: Array<List<&2, TE>>, x: X, r: Array<U32> & Pr) -> St & Pr:
  (ps, pr) = r
  (St{m, ps, tg, x}, pr)

# A pair type's sides.
def pair.get(s: St, +t: U32) -> St & Pr:
  match s:
    case St{m, ps, tg, x}:
      pair.got(m, tg, x, pr.b1((t - 4 : U32), ps[(t - 4 : U32)]))

def ground.got(m: Array<U32>, tg: Array<List<&2, TE>>, x: X, r: Array<U32> & U32) -> St & Bool:
  (ps, +g) = r
  (St{m, ps, tg, x}, U32.is_ne(g, 0))

# Whether a pair type is ground.
def ground.of(s: St, +t: U32) -> St & Bool:
  match s:
    case St{m, ps, tg, x}:
      ground.got(m, tg, x, ps[(t : U32)])

def ground.set(s: St, +t: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      St{m, ps[t] <- 1, tg, x}

# Tag sets
# --------

def tg.got(m: Array<U32>, ps: Array<U32>, x: X, r: Array<List<&2, TE>> & List<&2, TE>) -> St & List<&2, TE>:
  (tg, ts) = r
  (St{m, ps, tg, x}, ts)

# The tags held at a variable (a tag class's root).
def tg.get(s: St, +i: U32) -> St & List<&2, TE>:
  match s:
    case St{m, ps, tg, x}:
      tg.got(m, ps, x, Array.get(List<&2, TE>, tg, i))

def tg.bump(+i: U32, r: St & U32) -> St:
  (s, +v) = r
  wr(s, (i * 8 + 21 : U32), (v + 1 : U32))

# Every write of a variable's tags stamps it anew (word 5 of the variable),
# so that an unchanged stamp means unchanged tags.
def tg.set(s: St, +i: U32, ts: List<&2, TE>) -> St:
  match s:
    case St{m, ps, tg, x}:
      tg.bump(i, rd(St{m, ps, Array.set(List<&2, TE>, tg, i, ts), x}, (i * 8 + 21 : U32)))

# Blames, sites, equations, counters
# ----------------------------------

def bl.set(s: St, +n: U32, b: Blame) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          (St{Array.set(U32, m, 7, (n + 1 : U32)), ps, tg, X{sites, sv, Array.set(Blame, bl, n, b), ct, eqs, err, p}}, n)

def bl.grow(s: St, +cap: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          St{Array.set(U32, m, 8, (cap * 2 : U32)), ps, tg,
             X{sites, sv, ANode{bl, Array.new(Blame, U32.log2(cap), blame.none())}, ct, eqs, err, p}}

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

def bl.got(m: Array<U32>, ps: Array<U32>, tg: Array<List<&2, TE>>, sites: Array<Site>, sv: Array<U32>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P, r: Array<Blame> & Blame) -> St & Blame:
  (bl, b) = r
  (St{m, ps, tg, X{sites, sv, bl, ct, eqs, err, p}}, b)

def blame.get(s: St, +n: U32) -> St & Blame:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          bl.got(m, ps, tg, sites, sv, ct, eqs, err, p, Array.get(Blame, bl, n))

def sv.got(m: Array<U32>, ps: Array<U32>, tg: Array<List<&2, TE>>, sites: Array<Site>, bl: Array<Blame>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P, r: Array<U32> & U32) -> St & U32:
  (sv, v) = r
  (St{m, ps, tg, X{sites, sv, bl, ct, eqs, err, p}}, v)

# Word i of the sites' rows: site k's are its function position's type
# (4k), and the tag class root and stamp its last look saw (4k + 1, 4k + 2;
# see site.resolve).
def sv.rd(s: St, +i: U32) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          sv.got(m, ps, tg, sites, bl, ct, eqs, err, p, Array.get(U32, sv, i))

def sv.wr(s: St, +i: U32, +v: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          St{m, ps, tg, X{sites, Array.set(U32, sv, i, v), bl, ct, eqs, err, p}}

def site.set(s: St, +n: U32, site: Site) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          St{m, ps, tg, X{Array.set(Site, sites, n, site), sv, bl, ct, eqs, err, p}}

def site.grow(s: St, +cap: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          St{Array.set(U32, m, 6, (cap * 2 : U32)), ps, tg,
             X{ANode{sites, Array.new(Site, U32.log2(cap), site.none())}, ANode{sv, Array.new(U32, U32.log2((cap * 4 : U32)), 0)},
               bl, ct, eqs, err, p}}

def site.row(s: St, +n: U32, +fn: U32, site: Site) -> St:
  wr(sv.wr(sv.wr(site.set(s, n, site), (n * 4 : U32), fn), (n * 4 + 1 : U32), none()), 5, (n + 1 : U32))

def site.room(full: Bool, s: St, +n: U32, +cap: U32, +fn: U32, site: Site) -> St:
  match full:
    case True{}:
      site.row(site.grow(s, cap), n, fn, site)
    case False{}:
      site.row(s, n, fn, site)

def site.cap(+n: U32, +fn: U32, site: Site, r: St & U32) -> St:
  (s, +cap) = r
  site.room(U32.is_ge(n, cap), s, n, cap, fn, site)

def site.n(+fn: U32, site: Site, r: St & U32) -> St:
  (s, +n) = r
  site.cap(n, fn, site, rd(s, 6))

# registerApply: a site applying fn.
def site.add(s: St, +fn: U32, site: Site) -> St:
  site.n(fn, site, rd(s, 5))

def site.got(m: Array<U32>, ps: Array<U32>, tg: Array<List<&2, TE>>, sv: Array<U32>, bl: Array<Blame>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P, r: Array<Site> & Site) -> St & Site:
  (sites, site) = r
  (St{m, ps, tg, X{sites, sv, bl, ct, eqs, err, p}}, site)

def site.get(s: St, +n: U32) -> St & Site:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          site.got(m, ps, tg, sv, bl, ct, eqs, err, p, Array.get(Site, sites, n))

def eq.add(s: St, e: SumEq) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          St{m, ps, tg, X{sites, sv, bl, ct, e <> eqs, err, p}}

def sum.eq(s: St, +loc: Lc.Loc, +what: String, lhs: List<&2, U32>, +rhs: U32) -> St:
  eq.add(s, SumEq{lhs, rhs, Blame{loc, what}})

def ct.got(m: Array<U32>, ps: Array<U32>, tg: Array<List<&2, TE>>, sites: Array<Site>, sv: Array<U32>, bl: Array<Blame>, eqs: List<&2, SumEq>, err: List<&2, Err>, p: P, r: Array<U32> & U32) -> St & U32:
  (ct, v) = r
  (St{m, ps, tg, X{sites, sv, bl, ct, eqs, err, p}}, v)

# A body's counter: its derivations so far (2r), or the variables its
# first one minted (2r + 1).
def ct.get(s: St, +i: U32) -> St & U32:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          ct.got(m, ps, tg, sites, sv, bl, eqs, err, p, Array.get(U32, ct, i))

def ct.set(s: St, +i: U32, +v: U32) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, p}:
          St{m, ps, tg, X{sites, sv, bl, Array.set(U32, ct, i, v), eqs, err, p}}

def p.got(m: Array<U32>, ps: Array<U32>, tg: Array<List<&2, TE>>, sites: Array<Site>, sv: Array<U32>, bl: Array<Blame>, ct: Array<U32>, eqs: List<&2, SumEq>, err: List<&2, Err>, +p: P) -> St & P:
  (St{m, ps, tg, X{sites, sv, bl, ct, eqs, err, p}}, p)

# The program.
def prog(s: St) -> St & P:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, eqs, err, +p}:
          p.got(m, ps, tg, sites, sv, bl, ct, eqs, err, p)


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

# A walked side of a collapsed pair is ground when it is data or a ground
# pair.
def side.k(k: K, s: St, +w: U32) -> St & Bool:
  match k:
    case KData{}:
      (s, True{})
    case KPair{}:
      ground.of(s, w)
    case _:
      (s, False{})

def side.ok(r: St & U32) -> St & Bool:
  (s, +w) = r
  side.k(kind(w), s, w)

def ground.t2(+p: U32, r: St & Bool) -> St:
  (s, ok) = r
  match ok:
    case True{}:
      ground.set(s, p)
    case False{}:
      s

def ground.t1(+p: U32, +t2: U32, r: St & Bool) -> St:
  (s, ok) = r
  match ok:
    case True{}:
      ground.t2(p, side.ok(walk(s, t2)))
    case False{}:
      s

def ground.pr(+p: U32, r: St & Pr) -> St:
  (s, pr) = r
  match pr:
    case Pr{b1, +t1, b2, +t2}:
      ground.t1(p, t2, side.ok(walk(s, t1)))

# A pair just collapsed is ground when both its sides are.
def ground.mark(s: St, +p: U32) -> St:
  ground.pr(p, pair.get(s, p))

def colls(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +p: U32, rest: List<&2, W>, r: St & Pr) -> St & List<&2, W>:
  (s, pr) = r
  match pr:
    case Pr{b1, t1, b2, t2}:
      (s, WColl{vis, mode, loc, Sig{b1, t1}} <> WColl{vis, mode, loc, Sig{b2, t2}} <> WGround{p} <> rest)

def coll.at(ground: Bool, s: St, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +p: U32, rest: List<&2, W>) -> St & List<&2, W>:
  match ground:
    case True{}:
      (s, rest)
    case False{}:
      colls(vis, mode, loc, p, rest, pair.get(s, p))

def coll.g(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +p: U32, rest: List<&2, W>, r: St & Bool) -> St & List<&2, W>:
  (s, g) = r
  coll.at(g, s, vis, mode, loc, p, rest)

# A pair meets data: each side's bang is unboxed and its type meets data,
# and then the pair is ground if its sides are. Nothing unbinds a type
# variable, and a class forced to zero stays so (or the analysis fails),
# so collapsing a ground pair again would change nothing: it is skipped.
def coll(s: St, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +p: U32, rest: List<&2, W>) -> St & List<&2, W>:
  coll.g(vis, mode, loc, p, rest, ground.of(s, p))

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

# unifyTauAt, on two different walked types: its immediate effect, then
# the work left.
def walked(ka: K, kb: K, s: St, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> St & List<&2, W>:
  match ka:
    case KVar{}:
      match kb:
        case KVar{}:
          bind.var(s, loc, ix(a), b, rest)
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
          coll(s, vis, mode, loc, b, rest)
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
          coll(s, vis, mode, loc, a, rest)
        case KCode{}:
          mismatch(s, loc, mode, a, b)

# A type unifies with itself without effect (for a pair, side by side).
def unify.same(same: Bool, s: St, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> St & List<&2, W>:
  match same:
    case True{}:
      (s, rest)
    case False{}:
      walked(kind(a), kind(b), s, vis, mode, loc, a, b, rest)

def unify.wb(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +wa: U32, rest: List<&2, W>, r: St & U32) -> St & List<&2, W>:
  (s, +wb) = r
  unify.same(U32.is_eq(wa, wb), s, vis, mode, loc, wa, wb, rest)

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
    case WGround{+p}:
      (ground.mark(s, p), rest)

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
  (site.add(unify(s, loc, sx, Sig{pairb, t}), fnt, Site{si, so, depth, loc, []}), GRet{so, ks})

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
        case Site{+env, +res, +depth, +loc, done}:
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
        case Site{+env, +res, depth, +loc, done}:
          gate.scr(loc, env, res, forced.zero(s, Blame{loc, "gate scrutinee must be unboxed data"}))
    case BiGateFn{}:
      match site:
        case Site{+env, +res, depth, +loc, done}:
          gf.se(loc, env, res, fresh.sig(s))
    case BiAbort{}:
      match site:
        case Site{env, +res, depth, +loc, done}:
          abort.ct(loc, res, fresh.code(s, t.cont()))
    case BiCont{}:
      match site:
        case Site{+env, +res, depth, +loc, done}:
          unify(s, loc, env, res)

def dispatch.k(code: Bool, s: St, +tag: U32, +site: Site) -> St:
  match code:
    case True{}:
      match site:
        case Site{env, res, +depth, +loc, done}:
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
    case Site{+env, +res, +depth, +loc, +done}:
      dispatch.new.with(diff(tags, done), s, k, Site{env, res, depth, loc, both(done, tags)})

def site.ts(+k: U32, +site: Site, r: St & List<&2, U32>) -> St & Bool:
  (s, +ts) = r
  dispatch.new(s, k, site, ts)

def dispatch.te.at(none: Bool, s: St, +k: U32, +site: Site, +ts: List<&2, TE>, new: List<&2, U32>) -> St & Bool:
  match none:
    case True{}:
      (s, False{})
    case False{}:
      match site:
        case Site{+env, +res, +depth, +loc, +done}:
          dispatch.new.at(False{}, s, k, Site{env, res, depth, loc, both(done, keys(ts))}, new)

def dispatch.te(+new: List<&2, U32>, s: St, +k: U32, +site: Site, +ts: List<&2, TE>) -> St & Bool:
  dispatch.te.at(List.is_empty(&2, U32, new), s, k, site, ts, new)

# A code class at a site: the tags not dispatched there yet, compared
# without listing the class's tags first.
def site.caps(+k: U32, +site: Site, r: St & List<&2, TE>) -> St & Bool:
  match site:
    case Site{env, res, depth, loc, +done}:
      (s, +ts) = r
      dispatch.te(te.diff(ts, done), s, k, site, ts)

def site.loc(s: Site) -> Lc.Loc:
  match s:
    case Site{env, res, depth, loc, done}:
      loc

def site.full(+k: U32, +root: U32, r: St & Site) -> St & Bool:
  (s, +site) = r
  site.caps(k, site, tg.get(s, root))

def site.same(same: Bool, s: St, +k: U32, +root: U32, +stamp: U32) -> St & Bool:
  match same:
    case True{}:
      (s, False{})
    case False{}:
      site.full(k, root, site.get(sv.wr(sv.wr(s, (k * 4 + 1 : U32), root), (k * 4 + 2 : U32), stamp), k))

def site.ms(+k: U32, +root: U32, +stamp: U32, +mr: U32, r: St & U32) -> St & Bool:
  (s, +ms) = r
  site.same(U32.is_eq(mr, root) && U32.is_eq(ms, stamp), s, k, root, stamp)

def site.mr(+k: U32, +root: U32, +stamp: U32, r: St & U32) -> St & Bool:
  (s, +mr) = r
  site.ms(k, root, stamp, mr, sv.rd(s, (k * 4 + 2 : U32)))

def site.stamp(+k: U32, +root: U32, r: St & U32) -> St & Bool:
  (s, +stamp) = r
  site.mr(k, root, stamp, sv.rd(s, (k * 4 + 1 : U32)))

# A code class at a site. Its look records the class's root and stamp:
# the tags it saw are all dispatched (or being so) from then on, so while
# the root and its stamp stay the same there is nothing new to look for.
def site.code(+k: U32, r: St & U32) -> St & Bool:
  (s, +root) = r
  site.stamp(k, root, rd(s, (root * 8 + 21 : U32)))

def site.capw(+k: U32, +w: U32, r: St & Site) -> St & Bool:
  (s, +site) = r
  site.ts(k, site, fn.tags(s, ix(w)))

def site.pairw(r: St & Site) -> St & Bool:
  (s, site) = r
  (fail(s, TypeMismatch{site.loc(site), "applied value is pair, not code"}), False{})

def site.walked(k2: K, s: St, +k: U32, +w: U32) -> St & Bool:
  match k2:
    case KCode{}:
      site.code(k, find(s, 4, ix(w)))
    case KCap{}:
      site.capw(k, w, site.get(s, k))
    case KPair{}:
      site.pairw(site.get(s, k))
    case _:
      (s, False{})

def site.w(+k: U32, r: St & U32) -> St & Bool:
  (s, +w) = r
  site.walked(kind(w), s, k, w)

def site.fn(+k: U32, r: St & U32) -> St & Bool:
  (s, +fn) = r
  site.w(k, walk(s, fn))

# One site: dispatch whatever new code its function position holds.
def site.resolve(s: St, +k: U32) -> St & Bool:
  site.fn(k, sv.rd(s, (k * 4 : U32)))

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
  site.add(s, fn, Site{env, so, 0, Lc.Gen{"virtual application of main to input"}, []})

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

# The solver's tables are built once the walk and dispatch are done. The
# equations are resolved to class roots then, and nothing merges classes
# afterwards, so their roots stay roots.

def derived(+what: String, b: Blame) -> Blame:
  match b:
    case Blame{loc, why}:
      Blame{loc, what ++ ": " ++ why}

def give.up(+what: String, b: Blame) -> Err:
  GaveUp{what ++ ": " ++ blame.show(b)}

# A class word's kind.
def ck(+w: U32) -> CK:
  Bool.pick(CK, U32.is_zero((w .&. 3 : U32)), CFree{}, Bool.pick(CK, U32.is_eq((w .&. 3 : U32), 1), CZero{}, CLevel{}))

def is.zero(+w: U32) -> Bool:
  U32.is_eq((w .&. 3 : U32), 1)

def sv.fail(sv: Sv, e: Err) -> Sv:
  match sv:
    case Sv{c, cb, q, qb, v, n, ch}:
      SvErr{e}
    case SvErr{x}:
      SvErr{x}

def c.got(cb: Array<Blame>, q: Array<U32>, qb: Array<Blame>, v: Array<U32>, n: Array<U32>, +ch: Bool, r: Array<U32> & U32) -> Sv & U32:
  (c, w) = r
  (Sv{c, cb, q, qb, v, n, ch}, w)

# Root r's class word.
def c.rd(sv: Sv, +r: U32) -> Sv & U32:
  match sv:
    case Sv{c, cb, q, qb, v, n, +ch}:
      c.got(cb, q, qb, v, n, ch, Array.get(U32, c, r))
    case SvErr{e}:
      (SvErr{e}, 0)

# Root r's class becomes word w, blamed on b: a change. Until the
# assignment, a root's value is its class's lower bound.
def c.wr(sv: Sv, +r: U32, +w: U32, b: Blame) -> Sv:
  match sv:
    case Sv{c, cb, q, qb, v, n, ch}:
      Sv{Array.set(U32, c, r, w), Array.set(Blame, cb, r, b), q, qb, Array.set(U32, v, r, (w >> 2n : U32)), n, True{}}
    case SvErr{e}:
      SvErr{e}

def cb.got(c: Array<U32>, q: Array<U32>, qb: Array<Blame>, v: Array<U32>, n: Array<U32>, +ch: Bool, r: Array<Blame> & Blame) -> Sv & Blame:
  (cb, b) = r
  (Sv{c, cb, q, qb, v, n, ch}, b)

# Root r's class's blame.
def cb.rd(sv: Sv, +r: U32) -> Sv & Blame:
  match sv:
    case Sv{c, cb, q, qb, v, n, +ch}:
      cb.got(c, q, qb, v, n, ch, Array.get(Blame, cb, r))
    case SvErr{e}:
      (SvErr{e}, blame.none())

def q.got(c: Array<U32>, cb: Array<Blame>, qb: Array<Blame>, v: Array<U32>, n: Array<U32>, +ch: Bool, r: Array<U32> & U32) -> Sv & U32:
  (q, w) = r
  (Sv{c, cb, q, qb, v, n, ch}, w)

# Word i of the equations' rows.
def q.rd(sv: Sv, +i: U32) -> Sv & U32:
  match sv:
    case Sv{c, cb, q, qb, v, n, +ch}:
      q.got(c, cb, qb, v, n, ch, Array.get(U32, q, i))
    case SvErr{e}:
      (SvErr{e}, 0)

def qb.got(c: Array<U32>, cb: Array<Blame>, q: Array<U32>, v: Array<U32>, n: Array<U32>, +ch: Bool, r: Array<Blame> & Blame) -> Sv & Blame:
  (qb, b) = r
  (Sv{c, cb, q, qb, v, n, ch}, b)

# Equation e's blame.
def qb.rd(sv: Sv, +e: U32) -> Sv & Blame:
  match sv:
    case Sv{c, cb, q, qb, v, n, +ch}:
      qb.got(c, cb, q, v, n, ch, Array.get(Blame, qb, e))
    case SvErr{x}:
      (SvErr{x}, blame.none())

def v.got(c: Array<U32>, cb: Array<Blame>, q: Array<U32>, qb: Array<Blame>, n: Array<U32>, +ch: Bool, r: Array<U32> & U32) -> Sv & U32:
  (v, x) = r
  (Sv{c, cb, q, qb, v, n, ch}, x)

# Root r's value.
def v.rd(sv: Sv, +r: U32) -> Sv & U32:
  match sv:
    case Sv{c, cb, q, qb, v, n, +ch}:
      v.got(c, cb, q, qb, n, ch, Array.get(U32, v, r))
    case SvErr{e}:
      (SvErr{e}, 0)

# Root r's value becomes x: a change.
def v.wr(sv: Sv, +r: U32, +x: U32) -> Sv:
  match sv:
    case Sv{c, cb, q, qb, v, n, ch}:
      Sv{c, cb, q, qb, Array.set(U32, v, r, x), n, True{}}
    case SvErr{e}:
      SvErr{e}

def n.got(c: Array<U32>, cb: Array<Blame>, q: Array<U32>, qb: Array<Blame>, v: Array<U32>, +ch: Bool, r: Array<U32> & U32) -> Sv & U32:
  (n, x) = r
  (Sv{c, cb, q, qb, v, n, ch}, x)

# How many equations root r is a summand of.
def n.rd(sv: Sv, +r: U32) -> Sv & U32:
  match sv:
    case Sv{c, cb, q, qb, v, n, +ch}:
      n.got(c, cb, q, qb, v, ch, Array.get(U32, n, r))
    case SvErr{e}:
      (SvErr{e}, 0)


def q.wr(sv: Sv, +i: U32, +w: U32) -> Sv:
  match sv:
    case Sv{c, cb, q, qb, v, n, ch}:
      Sv{c, cb, Array.set(U32, q, i, w), qb, v, n, ch}
    case SvErr{e}:
      SvErr{e}

def qb.wr(sv: Sv, +e: U32, b: Blame) -> Sv:
  match sv:
    case Sv{c, cb, q, qb, v, n, ch}:
      Sv{c, cb, q, Array.set(Blame, qb, e, b), v, n, ch}
    case SvErr{x}:
      SvErr{x}

def n.inc.at(+r: U32, c: Array<U32>, cb: Array<Blame>, q: Array<U32>, qb: Array<Blame>, v: Array<U32>, +ch: Bool, p: Array<U32> & U32) -> Sv:
  (n, +x) = p
  Sv{c, cb, q, qb, v, Array.set(U32, n, r, (x + 1 : U32)), ch}

# One more equation has root r as a summand.
def n.inc(sv: Sv, +r: U32) -> Sv:
  match sv:
    case Sv{c, cb, q, qb, v, n, +ch}:
      n.inc.at(r, c, cb, q, qb, v, ch, Array.get(U32, n, r))
    case SvErr{e}:
      SvErr{e}

def sv.err(sv: Sv) -> Maybe<&2, Err>:
  match sv:
    case Sv{c, cb, q, qb, v, n, ch}:
      None{}
    case SvErr{e}:
      Some{e}

# propagate
# ---------

def zero.clash(+ob: Blame, +what: String, r: Sv & Blame) -> Sv:
  (sv, b) = r
  sv.fail(sv, BoxConflict{ob, derived(what, b)})

def zero.old(+what: String, +e: U32, r: Sv & Blame) -> Sv:
  (sv, +ob) = r
  zero.clash(ob, what, qb.rd(sv, e))

def zero.set(+r: U32, +what: String, p: Sv & Blame) -> Sv:
  (sv, b) = p
  c.wr(sv, r, 1, derived(what, b))

def zero.at(k: CK, sv: Sv, +r: U32, +what: String, +e: U32) -> Sv:
  match k:
    case CFree{}:
      zero.set(r, what, qb.rd(sv, e))
    case CZero{}:
      sv
    case CLevel{}:
      zero.old(what, e, cb.rd(sv, r))

def zero.w(+r: U32, +what: String, +e: U32, p: Sv & U32) -> Sv:
  (sv, +w) = p
  zero.at(ck(w), sv, r, what, e)

# constrainB to forced zero, on root r, for equation e (whose blame the
# class's derives from).
def zero(sv: Sv, +r: U32, +what: String, +e: U32) -> Sv:
  zero.w(r, what, e, c.rd(sv, r))

def level.set(+r: U32, +lv: U32, +what: String, p: Sv & Blame) -> Sv:
  (sv, b) = p
  c.wr(sv, r, (lv * 4 + 2 : U32), derived(what, b))

def level.clash(+ob: Blame, +what: String, p: Sv & Blame) -> Sv:
  (sv, b) = p
  sv.fail(sv, BoxConflict{derived(what, b), ob})

def level.old(+what: String, +e: U32, p: Sv & Blame) -> Sv:
  (sv, +ob) = p
  level.clash(ob, what, qb.rd(sv, e))

def level.keep(keep: Bool, sv: Sv, +r: U32, +lv: U32, +what: String, +e: U32) -> Sv:
  match keep:
    case True{}:
      sv
    case False{}:
      level.set(r, lv, what, qb.rd(sv, e))

def level.at(k: CK, sv: Sv, +r: U32, +lv: U32, +la: U32, +what: String, +e: U32) -> Sv:
  match k:
    case CFree{}:
      level.set(r, lv, what, qb.rd(sv, e))
    case CZero{}:
      level.old(what, e, cb.rd(sv, r))
    case CLevel{}:
      level.keep(U32.is_ge(la, lv), sv, r, lv, what, e)

def level.w(+r: U32, +lv: U32, +what: String, +e: U32, p: Sv & U32) -> Sv:
  (sv, +w) = p
  level.at(ck(w), sv, r, lv, (w >> 2n : U32), what, e)

def level.over.at(+what: String, p: Sv & Blame) -> Sv:
  (sv, b) = p
  sv.fail(sv, GaveUp{"bang level exceeded cap of 4096: " ++ blame.show(derived(what, b))})

def level.over(over: Bool, sv: Sv, +r: U32, +lv: U32, +what: String, +e: U32) -> Sv:
  match over:
    case True{}:
      level.over.at(what, qb.rd(sv, e))
    case False{}:
      level.w(r, lv, what, e, c.rd(sv, r))

# constrainB to forced level lv, on root r, for equation e; past the level
# cap, it gives up.
def level(sv: Sv, +r: U32, +lv: U32, +what: String, +e: U32) -> Sv:
  level.over(U32.is_gt(lv, level.cap()), sv, r, lv, what, e)

def zero.q(+e: U32, p: Sv & U32) -> Sv:
  (sv, +l) = p
  zero(sv, l, "summand of an unboxed total", e)

# The k summands from row word i are forced to zero.
def zeros(k: Nat, +e: U32, +i: U32, sv: Sv) -> Sv:
  match k:
    case 0n:
      sv
    case 1n+j:
      zeros(j, e, (i + 1 : U32), zero.q(e, q.rd(sv, i)))

def sm.add(s: Sm, +l: U32, +w: U32) -> Sm:
  match s:
    case Sm{fz, +sum, +free, +lone}:
      Sm{fz && is.zero(w), (sum + (w >> 2n : U32) : U32),
         Bool.pick(U32, is.zero(w), free, (free + 1 : U32)), Bool.pick(U32, is.zero(w), lone, l)}

def sm.w(+l: U32, s: Sm, p: Sv & U32) -> Sv & Sm:
  (sv, +w) = p
  (sv, sm.add(s, l, w))

def sm.l(s: Sm, p: Sv & U32) -> Sv & Sm:
  (sv, +l) = p
  sm.w(l, s, c.rd(sv, l))

# The k summands from row word i, summed up.
def sm.go(k: Nat, +i: U32, p: Sv & Sm) -> Sv & Sm:
  match k:
    case 0n:
      p
    case 1n+j:
      (sv, s) = p
      sm.go(j, (i + 1 : U32), sm.l(s, q.rd(sv, i)))

# An unboxed total unboxes every summand.
def prop.c1(fz: Bool, sv: Sv, +nl: U32, +o: U32, +e: U32) -> Sv:
  match fz:
    case True{}:
      zeros(U32.to_nat(nl), e, (o + 2 : U32), sv)
    case False{}:
      sv

# Summands all unboxed unbox the total.
def prop.c2(all: Bool, sv: Sv, +rhs: U32, +e: U32) -> Sv:
  match all:
    case True{}:
      zero(sv, rhs, "all summands unboxed", e)
    case False{}:
      sv

# The summands' lower bounds bound the total.
def prop.c3(some: Bool, sv: Sv, +rhs: U32, +sum: U32, +e: U32) -> Sv:
  match some:
    case True{}:
      level(sv, rhs, sum, "sum of summand lower bounds", e)
    case False{}:
      sv

def c4.at(k: CK, sv: Sv, +lone: U32, +lb: U32, +e: U32) -> Sv:
  match k:
    case CLevel{}:
      level(sv, lone, lb, "only boxable summand", e)
    case _:
      sv

def c4.w(+lone: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +w) = p
  c4.at(ck(w), sv, lone, (w >> 2n : U32), e)

# A boxed total's only boxable summand takes its level.
def prop.c4(one: Bool, sv: Sv, +lone: U32, +rhs: U32, +e: U32) -> Sv:
  match one:
    case True{}:
      c4.w(lone, e, c.rd(sv, rhs))
    case False{}:
      sv

def step.sm(+rhs: U32, +e: U32, p: Sv & Sm) -> Sv:
  (sv, s) = p
  match s:
    case Sm{fz, +sum, +free, +lone}:
      prop.c4(U32.is_eq(free, 1), prop.c3(U32.is_gt(sum, 0), prop.c2(fz, sv, rhs, e), rhs, sum, e), lone, rhs, e)

def step.ri(+nl: U32, +rhs: U32, +o: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +ri) = p
  step.sm(rhs, e, sm.go(U32.to_nat(nl), (o + 2 : U32), (prop.c1(is.zero(ri), sv, nl, o, e), Sm{True{}, 0, 0, 0})))

def step.rhs(+nl: U32, +o: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +rhs) = p
  step.ri(nl, rhs, o, e, c.rd(sv, rhs))

def step.nl(+o: U32, +e: U32, p: Sv & U32) -> Sv & U32:
  (sv, +nl) = p
  (step.rhs(nl, o, e, q.rd(sv, (o + 1 : U32))), (o + 2 + nl : U32))

# One equation's propagation step (equation e, its row at o); the next
# row's offset.
def step(sv: Sv, +o: U32, +e: U32) -> Sv & U32:
  step.nl(o, e, q.rd(sv, o))

# assignValues
# ------------

def a.err(+what: String, p: Sv & Blame) -> Sv:
  (sv, b) = p
  sv.fail(sv, give.up(what, b))

def a.plus(+acc: U32, p: Sv & U32) -> Sv & U32:
  (sv, +x) = p
  (sv, (acc + x : U32))

def a.l(+acc: U32, p: Sv & U32) -> Sv & U32:
  (sv, +l) = p
  a.plus(acc, v.rd(sv, l))

# The sum of the values of the k summands from row word i.
def a.sum(k: Nat, +i: U32, p: Sv & U32) -> Sv & U32:
  match k:
    case 0n:
      p
    case 1n+j:
      (sv, +acc) = p
      a.sum(j, (i + 1 : U32), a.l(acc, q.rd(sv, i)))

def pk.cmp(k: Pk, +l: U32, +cnt: U32) -> Pk:
  match k:
    case Pk{+best, +bc}:
      +better = U32.is_lt(cnt, bc) || (U32.is_eq(cnt, bc) && U32.is_lt(l, best))
      Pk{Bool.pick(U32, better, l, best), Bool.pick(U32, better, cnt, bc)}

def pk.n(+l: U32, k: Pk, p: Sv & U32) -> Sv & Pk:
  (sv, +cnt) = p
  (sv, pk.cmp(k, l, cnt))

def pk.z(z: Bool, +l: U32, k: Pk, sv: Sv) -> Sv & Pk:
  match z:
    case True{}:
      (sv, k)
    case False{}:
      pk.n(l, k, n.rd(sv, l))

def pk.w(+l: U32, k: Pk, p: Sv & U32) -> Sv & Pk:
  (sv, +w) = p
  pk.z(is.zero(w), l, k, sv)

def pk.l(k: Pk, p: Sv & U32) -> Sv & Pk:
  (sv, +l) = p
  pk.w(l, k, c.rd(sv, l))

# minimumBy on (count, root) over the k summands from row word i that may
# be boxed: the summand in the fewest equations, then the lowest; none()
# if no summand may be.
def pk.go(k: Nat, +i: U32, p: Sv & Pk) -> Sv & Pk:
  match k:
    case 0n:
      p
    case 1n+j:
      (sv, x) = p
      pk.go(j, (i + 1 : U32), pk.l(x, q.rd(sv, i)))

def adj.set(over: Bool, sv: Sv, +r: U32, +x: U32, +e: U32) -> Sv:
  match over:
    case True{}:
      a.err("assignment exceeded level cap", qb.rd(sv, e))
    case False{}:
      v.wr(sv, r, x)

def adj.raise(+short: U32, +e: U32, +r: U32, p: Sv & U32) -> Sv:
  (sv, +x) = p
  adj.set(U32.is_gt((x + short : U32), level.cap()), sv, r, (x + short : U32), e)

def adj.empty(empty: Bool, sv: Sv, +best: U32, +short: U32, +e: U32) -> Sv:
  match empty:
    case True{}:
      a.err("no boxable position to absorb required boxes", qb.rd(sv, e))
    case False{}:
      adj.raise(short, e, best, v.rd(sv, best))

# The sum falls short: raise one free summand by the difference.
def adj.pick(+short: U32, +e: U32, p: Sv & Pk) -> Sv:
  (sv, k) = p
  match k:
    case Pk{+best, bc}:
      adj.empty(U32.is_eq(best, none()), sv, best, short, e)

def adj.over(zero: Bool, over: Bool, sv: Sv, +rhs: U32, +sum: U32, +e: U32) -> Sv:
  match zero:
    case True{}:
      a.err("sum exceeds an unboxed total", qb.rd(sv, e))
    case False{}:
      adj.set(over, sv, rhs, sum, e)

# The sum exceeds the total: raise the total.
def adj.gt(+rhs: U32, +sum: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +w) = p
  adj.over(is.zero(w), U32.is_gt(sum, level.cap()), sv, rhs, sum, e)

def adj.cmp(c: Cmp, sv: Sv, +nl: U32, +o: U32, +rhs: U32, +sum: U32, +t: U32, +e: U32) -> Sv:
  match c:
    case EQ{}:
      sv
    case GT{}:
      adj.gt(rhs, sum, e, c.rd(sv, rhs))
    case LT{}:
      adj.pick((t - sum : U32), e, pk.go(U32.to_nat(nl), (o + 2 : U32), (sv, Pk{none(), none()})))

def adj.t(+nl: U32, +o: U32, +rhs: U32, +sum: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +t) = p
  adj.cmp(U32.cmp(sum, t), sv, nl, o, rhs, sum, t, e)

def adj.sum(+nl: U32, +o: U32, +rhs: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +sum) = p
  adj.t(nl, o, rhs, sum, e, v.rd(sv, rhs))

def adj.rhs(+nl: U32, +o: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +rhs) = p
  adj.sum(nl, o, rhs, e, a.sum(U32.to_nat(nl), (o + 2 : U32), (sv, 0)))

def adj.nl(+o: U32, +e: U32, p: Sv & U32) -> Sv & U32:
  (sv, +nl) = p
  (adj.rhs(nl, o, e, q.rd(sv, (o + 1 : U32))), (o + 2 + nl : U32))

# adjust: raise the total, or one summand, so that one equation holds.
def adjust(sv: Sv, +o: U32, +e: U32) -> Sv & U32:
  adj.nl(o, e, q.rd(sv, o))

def holds.at(ok: Bool, sv: Sv, +e: U32) -> Sv:
  match ok:
    case True{}:
      sv
    case False{}:
      a.err("assignment verification failed", qb.rd(sv, e))

def holds.t(+sum: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +t) = p
  holds.at(U32.is_eq(sum, t), sv, e)

def holds.sum(+rhs: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +sum) = p
  holds.t(sum, e, v.rd(sv, rhs))

def holds.rhs(+nl: U32, +o: U32, +e: U32, p: Sv & U32) -> Sv:
  (sv, +rhs) = p
  holds.sum(rhs, e, a.sum(U32.to_nat(nl), (o + 2 : U32), (sv, 0)))

def holds.nl(+o: U32, +e: U32, p: Sv & U32) -> Sv & U32:
  (sv, +nl) = p
  (holds.rhs(nl, o, e, q.rd(sv, (o + 1 : U32))), (o + 2 + nl : U32))

# The assignment satisfies one equation exactly.
def holds(sv: Sv, +o: U32, +e: U32) -> Sv & U32:
  holds.nl(o, e, q.rd(sv, o))

# The passes
# ----------

def pass.step(ps: Pass, sv: Sv, +o: U32, +e: U32) -> Sv & U32:
  match ps:
    case PProp{}:
      step(sv, o, e)
    case PAdjust{}:
      adjust(sv, o, e)
    case PHolds{}:
      holds(sv, o, e)

# One pass over the k equations left, from equation e (r holds its row's
# offset); it stops at a failure.
def rows(k: Nat, +ps: Pass, +e: U32, r: Sv & U32) -> Sv:
  match k:
    case 0n:
      (sv, o) = r
      sv
    case 1n+j:
      (sv, +o) = r
      match sv:
        case SvErr{x}:
          SvErr{x}
        case Sv{c, cb, q, qb, v, n, ch}:
          rows(j, ps, (e + 1 : U32), pass.step(ps, Sv{c, cb, q, qb, v, n, ch}, o, e))

def stuck(ps: Pass) -> Err:
  match ps:
    case PProp{}:
      GaveUp{"constraint propagation did not converge"}
    case _:
      GaveUp{"assignment did not converge"}

# A pass round after round, while a round changes anything, within fuel
# rounds.
def rounds(fuel: Nat, +k: Nat, +ps: Pass, sv: Sv) -> Sv:
  match fuel:
    case 0n:
      match sv:
        case Sv{c, cb, q, qb, v, n, ch}:
          match ch:
            case True{}:
              SvErr{stuck(ps)}
            case False{}:
              Sv{c, cb, q, qb, v, n, False{}}
        case SvErr{e}:
          SvErr{e}
    case 1n+f:
      match sv:
        case Sv{c, cb, q, qb, v, n, ch}:
          match ch:
            case True{}:
              rounds(f, k, ps, rows(k, ps, 0, (Sv{c, cb, q, qb, v, n, False{}}, 0)))
            case False{}:
              Sv{c, cb, q, qb, v, n, False{}}
        case SvErr{e}:
          SvErr{e}

def sv.dirty(sv: Sv) -> Sv:
  match sv:
    case Sv{c, cb, q, qb, v, n, ch}:
      Sv{c, cb, q, qb, v, n, True{}}
    case SvErr{e}:
      SvErr{e}

# propagate, then assignValues (from the lower bounds, greedily raising
# free summands) and its verification; only whether it all holds matters
# here.
def run(+k: Nat, sv: Sv) -> Maybe<&2, Err>:
  sv.err(rows(k, PHolds{}, 0, (rounds(U32.to_nat((U32.from_nat(k) * 4 + 16 : U32)), k, PAdjust{},
    sv.dirty(rounds(U32.to_nat((U32.from_nat(k) * 4 + 64 : U32)), k, PProp{}, sv))), 0)))


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

# The words the equations' rows take.
def rows.size(es: List<&2, SumEq>, +acc: U32) -> U32:
  match es:
    case Nil{}:
      acc
    case Con{e, rest}:
      match e:
        case SumEq{lhs, rhs, blame}:
          rows.size(rest, (acc + 2 + U32.from_nat(List.length(&2, U32, lhs)) : U32))

def fill.b(+r: U32, +w: U32, sv: Sv, p: St & Blame) -> St & Sv:
  (s, b) = p
  (s, c.wr(sv, r, w, b))

def fill.id(+r: U32, +w: U32, sv: Sv, p: St & U32) -> St & Sv:
  (s, +id) = p
  fill.b(r, w, sv, blame.get(s, id))

def fill.w(+r: U32, sv: Sv, p: St & U32) -> St & Sv:
  (s, +w) = p
  fill.id(r, w, sv, rd(s, (r * 8 + 19 : U32)))

# Root r's class word and blame, copied from the state to the tables.
def fill.root(+r: U32, p: St & Sv) -> St & Sv:
  (s, sv) = p
  fill.w(r, sv, rd(s, (r * 8 + 18 : U32)))

def fill.lhs(ls: List<&2, U32>, +i: U32, p: St & Sv) -> St & Sv:
  match ls:
    case Nil{}:
      p
    case Con{+l, rest}:
      (s, sv) = p
      fill.lhs(rest, (i + 1 : U32), fill.root(l, (s, n.inc(q.wr(sv, i, l), l))))

# The equations, resolved to roots, as rows from equation e at offset o,
# with their roots' classes.
def fill(es: List<&2, SumEq>, +e: U32, +o: U32, p: St & Sv) -> St & Sv:
  match es:
    case Nil{}:
      p
    case Con{x, rest}:
      match x:
        case SumEq{+lhs, +rhs, blame}:
          (s, sv) = p
          +nl = U32.from_nat(List.length(&2, U32, lhs))
          fill(rest, (e + 1 : U32), (o + 2 + nl : U32),
            fill.lhs(lhs, (o + 2 : U32), fill.root(rhs, (s, qb.wr(q.wr(q.wr(sv, o, nl), (o + 1 : U32), rhs), e, blame)))))

def solve.done(s: St, m: Maybe<&2, Err>) -> St:
  match m:
    case None{}:
      s
    case Some{e}:
      fail(s, e)

def solve.sv(+k: Nat, r: St & Sv) -> St:
  (s, sv) = r
  solve.done(s, run(k, sv))

# The tables: a root's words by its number (as many as there may be
# variables), and the rows.
def solve.size(+rs: List<&2, SumEq>, r: St & U32) -> St:
  (s, +size) = r
  +d = (U32.log2(size) - 3n : Nat)
  +k = List.length(&2, SumEq, rs)
  solve.sv(k, fill(rs, 0, 0, (s, Sv{Array.new(U32, d, 0), Array.new(Blame, d, blame.none()),
    Array.new(U32, (U32.log2((rows.size(rs, 0) + 1 : U32)) + 1n : Nat), 0),
    Array.new(Blame, (U32.log2((U32.from_nat(k) + 1 : U32)) + 1n : Nat), blame.none()),
    Array.new(U32, d, 0), Array.new(U32, d, 0), True{}})))

def solve.res(ps: Array<U32>, tg: Array<List<&2, TE>>, x: X, r: Array<U32> & List<&2, SumEq>) -> St:
  (m, +rs) = r
  solve.size(rs, rd(St{m, ps, tg, x}, 1))

def solve.eqs(s: St) -> St:
  match s:
    case St{m, ps, tg, x}:
      match x:
        case X{sites, sv, bl, ct, +eqs, err, p}:
          solve.res(ps, tg, X{sites, sv, bl, ct, eqs, err, p}, resolve.eqs(eqs, m))

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
        case X{sites, sv, bl, ct, eqs, err, p}:
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
