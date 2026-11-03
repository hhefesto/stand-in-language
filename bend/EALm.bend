import Base

import ./Show.bend as Sh

import ./Loc.bend as Lc

import ./Core.bend as Co

import ./Lift.bend as Lf

import ./Linear.bend as Ln

# Elementary Affine Logic certification, master's Telomare.EAL (98de497c):
# box levels for a defer-lifted program as linear constraints over the
# naturals, solved exactly (Linear.bend). Every DeferRef occurrence
# instantiates its body once, from a per-body template, and the tag it
# mints carries that instance's interface (env, result, doors); apply
# sites only unify, to a fixpoint, so nothing needs a budget.
#
# The Haskell is followed step for step: fresh variables are minted in its
# order, maps are walked in its key order and the unifier's work list pops
# last in first, so roots, variable numbers and the first error are its.
#
# Layout:
# - One counter numbers bang variables, type variables and tag classes, as
#   esNextVar does; per number the state keeps a type binding, a bang
#   parent, a class, a tag parent and a tag set, in arrays that double as
#   the counter passes their size.
# - A type is one word: its kind in the low three bits (1 a variable, 2 a
#   code class, 3 a capture selection, 4 a pair, 5 data, 6 aborted) and the
#   variable, class or pair number above them. A pair is four words in the
#   pairs' table (each side's bang and type).
# - A tag is one word: a body's rank among the hashes (Ord Tag orders code
#   by hash), or, above every rank, the gate and the gate function.
# - The first failure is kept in the state, and every loop stops at it.

# Types
# -----

# A Blame: where, why, and the body (its index plus one, 0 for none) whose
# walk made it.
type Blame is Data:
  Blame{+loc: Lc.Loc, +why: String, +fr: U32}

type Err is Data:
  TypeMismatch{+loc: Lc.Loc, +msg: String}
  BoxConflict{+need: Blame, +forbid: Blame}
  GaveUp{+msg: String}
  Unsat{+bs: List<&2, Blame>}
  DependencyFailed{+h: String}
  Internal{+msg: String}

# A bang class: unrestricted, forced to zero, or at least a level (>= 1).
type CI is Data:
  CUnr{}
  CZero{+bl: Blame}
  CLevel{+n: U32, +bl: Blame}

# A sigma: a bang and a type word.
type Sg is Data:
  Sg{+b: U32, +t: U32}

# An instance's interface: the env it consumes, the value it yields, and
# its doors.
type If is Data:
  If{+env: Sg, +res: Sg, +doors: List<&2, U32>}

# A tag of a class, with the capture riding with it and its interface.
type TE is Data:
  TE{+tag: U32, +cap: Maybe<&2, Sg>, +ifc: Maybe<&2, If>}

type SumEq is Data:
  SumEq{+lhs: List<&2, U32>, +rhs: U32, +bl: Blame}

# An apply site: its function position, operand, result, place, and the
# tags dispatched there (sorted).
type Ap is Data:
  Ap{+fn: U32, +env: Sg, +res: Sg, +loc: Lc.Loc, +done: List<&2, U32>}

# A body instance's env bang.
type Df is Data:
  Df{+fi: U32, +b: U32}

# A leaf: the body it sits in (index plus one, 0 for main), the base of
# its frame and its depth.
type Lp is Data:
  Lp{+fr: U32, +base: U32, +d: U32}

# A lifted term, references by rank. AAbort is master's AbortF (the port's
# SetEnv (Pair Abort m)); ABot an abort outside that shape.
type A is Data:
  AZero{+loc: Lc.Loc}
  APair{+loc: Lc.Loc, +a: A, +b: A}
  AEnv{+loc: Lc.Loc}
  AUns{+loc: Lc.Loc}
  ASetEnv{+loc: Lc.Loc, +x: A}
  AGate{+loc: Lc.Loc}
  ALeft{+loc: Lc.Loc, +x: A}
  ARight{+loc: Lc.Loc, +x: A}
  AAbort{+loc: Lc.Loc, +m: A}
  ABot{+loc: Lc.Loc}
  ACheck{+loc: Lc.Loc, +c: A}
  ARef{+loc: Lc.Loc, +r: U32}

# A body: its hash, index, whether it is a sized recursion chain's link
# (unsizedStepMrfb), and its term.
type Bd is Data:
  Bd{+h: String, +fi: U32, +link: Bool, +t: A}

# A pair (word, value) of a template's block.
type KV is Data:
  KV{+k: U32, +v: U32}

type KC is Data:
  KC{+k: U32, +c: CI}

type KT is Data:
  KT{+k: U32, +es: List<&2, TE>}

# A body's walk as a template (BodyTemplate): its block of variables
# (from v0, size) and pairs (from p0, psz), what the walk wrote there, the
# append-only deltas (newest first, applies oldest first), and the
# interface. Leaves keep their body and depth (the base is the instance's).
type Tm is Data:
  Tm{+fi: U32, +v0: U32, +size: U32, +p0: U32, +psz: U32, +bp: List<&2, KV>, +ci: List<&2, KC>,
     +tb: List<&2, KV>, +tp: List<&2, KV>, +ts: List<&2, KT>, +pr: List<&2, KV>, +eqs: List<&2, SumEq>,
     +lfs: List<&2, KV>, +aps: List<&2, Ap>, +dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg,
     +doors: List<&2, U32>}

type Mt is Data:
  MtNone{}
  MtSome{+t: Tm}

# A cycle note of presolve's cycleStep, kept for rendering: the cycle's
# members and the equations touching it, shown. A derived blame holds a
# placeholder for it (\1 number \2), expanded only when an error is
# rendered (the Haskell builds the note lazily, and it is long).
type CN is Data:
  CN{+id: U32, +ms: List<&2, U32>, +tl: List<&2, String>}

# The state (EALState).
type S is Type:
  S{tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>,
    pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat,
    na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>,
    nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32}

type K is Data:
  KVar{}
  KCode{}
  KCap{}
  KPair{}
  KData{}
  KAbort{}

# Pairs
# -----

type PS is Data:
  PS{+a: Sg, +b: Sg}

type WkN is Type:
  WkMore{s: S, +t: U32}
  WkStop{s: S, +t: U32}

# Union-find over bangs
# ---------------------

type BFN is Type:
  BFMore{s: S, +j: U32}
  BFStop{s: S, +r: U32}

type BFP is Type:
  BFPMore{s: S, +j: U32}
  BFPStop{s: S}

# Union-find over tag classes
# ---------------------------

type TFN is Type:
  TFMore{s: S, +j: U32}
  TFStop{s: S, +r: U32}

type TFP is Type:
  TFPMore{s: S, +j: U32}
  TFPStop{s: S}

type OcN is Type:
  OcGo{s: S, +i: U32, ts: List<&2, U32>}
  OcHit{s: S}
  OcNo{s: S}

type ExN is Type:
  ExGo{s: S, ts: List<&2, U32>, acc: List<&2, U32>}
  ExDone{s: S, acc: List<&2, U32>}

# selfReferential
# ---------------

type SrI is Data:
  SrTy{+vis: List<&2, U32>, +path: List<&2, U32>, +t: U32}
  SrArg{+vis: List<&2, U32>, +path: List<&2, U32>, +t: U32}

type SrN is Type:
  SrGo{s: S, +r0: U32, st: List<&2, SrI>}
  SrFound{s: S, +path: List<&2, U32>}
  SrNo{s: S}

# The unifier
# -----------

# A job of the unifier's work list: unify two sigmas or types (with the
# capture classes visited and the dispatch's tag, none() outside one),
# unify two records of one tag, merge two lists of bangs, or reject a
# class that is its own interface's.
type W is Data:
  WSig{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: Sg, +b: Sg}
  WTau{+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32}
  WInfo{+loc: Lc.Loc, +a: TE, +b: TE}
  WBangs{+xs: List<&2, U32>, +ys: List<&2, U32>}
  WSelf{+loc: Lc.Loc, +c: U32}

type UN is Type:
  UnGo{s: S, js: List<&2, W>}
  UnDone{s: S}

# Env usage (envUsageL, contractionSites)
# ---------

# An env use: its path (innermost projection first), count, first place.
type Use is Data:
  Use{+path: List<&2, U32>, +n: U32, +loc: Lc.Loc}

type Site is Data:
  Site{+path: List<&2, U32>, +loc: Lc.Loc}

# Frames
# ------

type KD is Data:
  KD{+path: List<&2, U32>, +inner: U32}

type Door is Data:
  Door{+path: List<&2, U32>, +door: U32, +inner: U32}

# DeferCtx: the frame's env bang and type, the unit, the doors, the body
# (index plus one, 0 for main) and per duplicated capture path what the
# body opens of it.
type Ctx is Data:
  Ctx{+bang: U32, +tau: U32, +unit: U32, +doorl: List<&2, U32>, +idx: U32, +doors: List<&2, KD>}

# Paths: the node's depth plus one (0 at a frame root) and the frame's
# global depth.
type Pa is Data:
  Pa{+par: U32, +base: U32}

# envComponent's state: the bangs stepped through (last first) and the
# component.
type EC is Data:
  EC{+bangs: List<&2, U32>, +cur: Sg}

# Templates (BodyTemplate)
# ---------

# The counters a template's deltas start from.
type Snap is Data:
  Snap{+v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32}

# The shift of an instance: its variables' and pairs' offsets from the
# template's.
type Sh is Data:
  Sh{+v0: U32, +sh: U32, +p0: U32, +psh: U32}

# The walk (viewNode, intrinsic, instantiateBody)
# --------
#
# One machine runs the walk: a task (view a node, type it intrinsically,
# view a pair's component, instantiate a body, or return a value) and a
# stack of frames, each the rest of a Haskell do block waiting for the
# value of the task below it.

type R is Data:
  RSg{+sg: Sg}
  RView{+sg: Sg, +d: U32}
  RIf{+ifc: If}

type Task is Data:
  TView{+c: Ctx, +p: Pa, +t: A}
  TIntr{+c: Ctx, +p: Pa, +t: A}
  TChild{+c: Ctx, +p: Pa, +t: A}
  TInst{+unit: U32, +p: Pa, +r: U32}
  TRet{+v: R}

type Fr is Data:
  FView{+loc: Lc.Loc, +w: U32, +d: U32}
  FPairA{+c: Ctx, +p: Pa, +loc: Lc.Loc, +b: A}
  FPairB{+loc: Lc.Loc, +sa: Sg}
  FSetEnv{+loc: Lc.Loc}
  FProj{+loc: Lc.Loc, +left: Bool}
  FAbort{}
  FRef{+loc: Lc.Loc, +r: U32}
  FCap{+r: U32, +fi: U32, +z: Snap, +frame0: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>}
  FChA{+c: Ctx, +p: Pa, +loc: Lc.Loc, +bloc: Lc.Loc, +prev: A, +trb: A, +plink: Bool, +dlink: U32}
  FChP{+c: Ctx, +ip: Pa, +loc: Lc.Loc, +bloc: Lc.Loc, +trb: A, +plink: Bool, +dlink: U32, +sa: Sg, +w2: U32, +d2: U32}
  FChT{+loc: Lc.Loc, +bloc: Lc.Loc, +sa: Sg, +w2: U32, +d2: U32, +sprev: Sg, +plink: Bool}

type WM is Type:
  WmGo{s: S, task: Task, st: List<&2, Fr>}
  WmEnd{s: S, v: R}

type CK is Data:
  CkGo{+vis: List<&2, U32>, +i: U32}
  CkRet{+m: List<&2, TE>}

type CF is Data:
  CfFold{+vis: List<&2, U32>, +rest: List<&2, TE>, +acc: List<&2, TE>}

type CM is Type:
  CmGo{s: S, +loc: Lc.Loc, task: CK, st: List<&2, CF>}
  CmEnd{s: S, m: List<&2, TE>}

type RA is Type:
  RaGo{s: S}
  RaDone{s: S}

# Constraint solving (presolve, solveConstraints)
# -------------------

# A sum equation over class roots (EqR).
type ER is Data:
  ER{+lhs: List<&2, U32>, +rhs: U32, +bl: Blame}

# cycleStep: Data.Graph.stronglyConnComp, in its order
# ---------

# A dfs frame: a vertex and its successors still to visit.
type DFr is Data:
  DFr{+v: U32, +ks: List<&2, U32>}

# The graph (graphFromEdges over the sorted nodes): each number's vertex
# plus one (vx), each vertex's number (nd), the successors (g) and the
# transpose's (gt), the pass that visited each vertex (vis), each
# vertex's cyclic component plus one (sc), the vertex count; the first
# pass's postorder (last first), the tree being walked (preorder, last
# first), the cyclic components (last first) and their count, the dfs
# stack, the roots to go, and the pass (1 on the transpose, 2 on g).
type GR is Type:
  GR{vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, String>>}

# dfs, as a machine: the stack holds each open vertex with the successors
# it has left; a tree ends when the stack empties.
type DN is Type:
  DnMore{g: GR}
  DnStop{g: GR}

# The second half of cycleStep, planned over the graph: for every live
# equation whose total is on a cycle, the numbers to force to zero.
type ZP is Data:
  ZP{+xs: List<&2, U32>, +bl: Blame}

# Members of the total's component (counted) and the other summands
# (last first).
type PT is Data:
  PT{+mem: U32, +oth: List<&2, U32>}

# presolve: the four steps, in rounds, to a fixpoint (or the first error).
type PSt is Type:
  PsMore{s: S}
  PsStop{s: S}

# The solver's inputs over the live numbers renumbered densely in
# ascending order (the Haskell's IntMap order): lower bounds, weights.
type SV is Type:
  SV{s: S, g: GR, cnt: Array<U32>, lb: Array<U32>, w: Array<U32>}

# The walk's interface: the env's bang and type, and the result.
type WT is Data:
  WT{+benv: U32, +tenv: U32, +res: Sg}

# The result (goMain)
# ----------

# Values of roots: the state and the solved values.
type VS is Type:
  VS{s: S, a: Array<U32>}

# Leaves: the deepest (leafDepths), and each body's deepest
# (bodyLeafDepths).
type LD is Type:
  LD{v: VS, +mx: U32, m: Map<&2, KV>}

# shapeOfSigma, as a machine over the type's pairs.
type SJ is Data:
  SjTau{+t: U32}
  SjWalked{+k: K, +w: U32}
  SjPair{}

type SQ is Type:
  SqGo{s: S, +js: List<&2, SJ>, +vs: List<&2, Lf.Shape>}
  SqEnd{s: S, +v: Lf.Shape}

# A certified main pass (EALResult, the capture layouts, the bodies'
# levels).
type MR is Data:
  MR{+top: U32, +defers: List<&2, KV>, +max: U32, +shape: Lf.Shape, +shapes: Map<&2, Lf.Shape>, +levels: List<&2, KV>}

# inferEALLifted
# --------------

# A lifted program as data, for the runs over it: the bodies by rank,
# each body's direct references (refsOf, as sorted ranks), main and its
# references.
type PG is Data:
  PG{+bds: List<&2, Bd>, +refs: List<&2, List<&2, U32>>, +n: U32, +main: A, +mrefs: List<&2, U32>}

# The verdicts withDeps reads, as a machine over the DAG: each frame a
# body (the extra rank n stands for main) and the references it has yet
# to see; a body fails at its first failing reference, else by its own
# summary. Verdicts: 0 unknown, 1 certifies, 2 fails.
type VF is Data:
  VF{+r: U32, +ds: List<&2, U32>}

type VQ is Type:
  VqGo{v: Array<U32>, +st: List<&2, VF>}
  VqEnd{v: Array<U32>}

# appliedClosure: SetEnv (SetEnv (Pair tw (Pair operand (Pair (DeferRef
# code) cap)))), its parts.
type AC is Data:
  AC{+a1: Lc.Loc, +a2: Lc.Loc, +a3: Lc.Loc, +tw: Lf.L, +a4: Lc.Loc, +operand: Lf.L, +a5: Lc.Loc, +a6: Lc.Loc, +code: String, +cap: Lf.L}

# Pair (DeferRef code) cap
type PR is Data:
  PR{+loc: Lc.Loc, +cloc: Lc.Loc, +code: String, +cap: Lf.L}

# The specialization's state (SpecState): the bodies (growing), each
# specialized body's origin, the memo, deep, the substitutable keys (all,
# if none), the body being specialized (its index plus one, 0 for main),
# and the SpecInfo: every substitutable definition, and per body (by
# fi.key) the keys it could substitute.
type SP is Data:
  SP{+bodies: Map<&2, Lf.Body>, +origin: Map<&2, String>, +memo: Map<&2, String>, +deep: Bool, +allowed: Maybe<&2, Map<&2, Bool>>, +body: U32, +defs: Map<&2, Bool>, +reads: Map<&2, Map<&2, Bool>>}

type SV2 is Data:
  VL{+l: Lf.L}
  VH{+h: String}

type SK is Data:
  SkTerm{+sub: Map<&2, Lf.L>, +t: Lf.L}
  SkBody{+h: String, +sub: Map<&2, Lf.L>}
  SkPair{+loc: Lc.Loc}
  SkSetEnv{+loc: Lc.Loc}
  SkLeft{+loc: Lc.Loc}
  SkRight{+loc: Lc.Loc}
  SkCheck{+loc: Lc.Loc, +o: Lc.Origin}
  SkApp1{+sub: Map<&2, Lf.L>, +c: AC}
  SkApp2{+c: AC, +o: Lf.L, +k: Lf.L}
  SkPRef1{+sub: Map<&2, Lf.L>, +p: PR}
  SkPRef2{+loc: Lc.Loc, +cloc: Lc.Loc, +k: Lf.L}
  SkRef{+loc: Lc.Loc}
  SkBodyEnd{+h: String, +key: String, +fi: U32, +outer: U32, +body: Lf.L}

type SM is Data:
  SmGo{+sp: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>}
  SmEnd{+sp: SP, +vs: List<&2, SV2>}

# specializeLets: the bodies (grown), the origins, main specialized, and
# the SpecInfo (every definition met, and per body what it reads).
type SR is Data:
  SR{+bodies: Map<&2, Lf.Body>, +origin: Map<&2, String>, +main: Lf.L, +defs: Map<&2, Bool>, +reads: Map<&2, Map<&2, Bool>>}

# reach: the bodies each body reaches, itself included (by fi.key), per
# rank, as a machine over the DAG.
type RF is Data:
  RF{+r: U32, +ds: List<&2, U32>}

type RQ is Type:
  RqGo{a: Array<Map<&2, Bool>>, d: Array<U32>, +st: List<&2, RF>}
  RqEnd{a: Array<Map<&2, Bool>>}

# What the narrowing reads: the program's ranks, every body's reach, and
# the full deep specialization's SpecInfo.
type NI is Data:
  NI{+rk: Map<&2, U32>, +reach: List<&2, Map<&2, Bool>>, +defs: Map<&2, Bool>, +reads: Map<&2, Map<&2, Bool>>}

# narrowed: substitute only what failures point at, adding to it until
# the program certifies or nothing is left to add.
type NF is Data:
  NfGo{+allowed: Map<&2, Bool>, +e: Err}
  NfDone{+r: Maybe<&2, MR>}

# Words
# -----

def none() -> U32:
  4294967295

def big() -> Nat:
  U32.to_nat(4294967295)

def tag.gate() -> U32:
  4294967293

def tag.gatefn() -> U32:
  4294967294

def ty.var(+i: U32) -> U32:
  ((i << 3n : U32) + 1 : U32)

def ty.code(+i: U32) -> U32:
  ((i << 3n : U32) + 2 : U32)

def ty.cap(+i: U32) -> U32:
  ((i << 3n : U32) + 3 : U32)

def ty.pair(+p: U32) -> U32:
  ((p << 3n : U32) + 4 : U32)

def ty.data() -> U32:
  5

def ty.abort() -> U32:
  6

def ty.of(+t: U32) -> U32:
  (t >> 3n : U32)

def kind.at(+k: U32) -> K:
  Bool.pick(K, U32.is_eq(k, 1), KVar{}, Bool.pick(K, U32.is_eq(k, 2), KCode{},
    Bool.pick(K, U32.is_eq(k, 3), KCap{}, Bool.pick(K, U32.is_eq(k, 4), KPair{},
    Bool.pick(K, U32.is_eq(k, 5), KData{}, KAbort{})))))

def kind(+t: U32) -> K:
  kind.at((t .&. 7 : U32))

def describe.k(k: K, +t: U32) -> String:
  match k:
    case KVar{}:
      "t" ++ U32.show(ty.of(t))
    case KCode{}:
      "code"
    case KCap{}:
      "capture"
    case KPair{}:
      "pair"
    case KData{}:
      "data"
    case KAbort{}:
      "aborted"

def describe(+t: U32) -> String:
  describe.k(kind(t), t)

def gen(+why: String) -> Lc.Loc:
  Lc.Gen{why}

def blame(+loc: Lc.Loc, +why: String) -> Blame:
  Blame{loc, why, 0}

# Lists of words
# --------------

def u.has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, rest}:
      Bool.or(U32.is_eq(x, y), u.has(rest, x))

def u.len(xs: List<&2, U32>) -> U32:
  U32.from_nat(List.length(&2, U32, xs))

# A path's steps (0 = L, 1 = R), innermost projection first.
def steps.go(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, rest}:
      Bool.pick(String, U32.is_eq(x, 0), "L", "R") ++ steps.go(rest)

def steps.show(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "<whole env>"
    case Con{+x, rest}:
      steps.go(Con{x, rest})

def cmp.then(c: Cmp, r: Cmp) -> Cmp:
  match c:
    case EQ{}:
      r
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# Ord [Step]: lexicographic, a prefix first.
def steps.cmp(xs: List<&2, U32>, ys: List<&2, U32>) -> Cmp:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          EQ{}
        case Con{y, yr}:
          LT{}
    case Con{+x, xr}:
      match ys:
        case Nil{}:
          GT{}
        case Con{+y, yr}:
          cmp.then(U32.cmp(x, y), steps.cmp(xr, yr))

def steps.prefix(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, xr}:
      match ys:
        case Nil{}:
          False{}
        case Con{+y, yr}:
          Bool.and(U32.is_eq(x, y), steps.prefix(xr, yr))

# The term
# --------

def to.a(l: Lf.L, +rk: Map<&2, U32>) -> A:
  match l:
    case Lf.LZero{loc}:
      AZero{loc}
    case Lf.LPair{loc, a, b}:
      APair{loc, to.a(a, rk), to.a(b, rk)}
    case Lf.LEnv{loc}:
      AEnv{loc}
    case Lf.LSetEnv{loc, x}:
      match x:
        case Lf.LPair{pl, a, b}:
          match a:
            case Lf.LAbort{al}:
              AAbort{loc, to.a(b, rk)}
            case other:
              ASetEnv{loc, APair{pl, to.a(other, rk), to.a(b, rk)}}
        case other:
          ASetEnv{loc, to.a(other, rk)}
    case Lf.LGate{loc}:
      AGate{loc}
    case Lf.LLeft{loc, x}:
      ALeft{loc, to.a(x, rk)}
    case Lf.LRight{loc, x}:
      ARight{loc, to.a(x, rk)}
    case Lf.LAbort{loc}:
      ABot{loc}
    case Lf.LUnsized{loc, tok}:
      AUns{loc}
    case Lf.LCheck{loc, o, tc, c}:
      ACheck{loc, to.a(c, rk)}
    case Lf.LRef{loc, h}:
      ARef{loc, Pair.snd(Map<&2, U32>, U32, Map.get(U32, none(), rk, h))}

def a.loc(t: A) -> Lc.Loc:
  match t:
    case AZero{loc}:
      loc
    case APair{loc, a, b}:
      loc
    case AEnv{loc}:
      loc
    case AUns{loc}:
      loc
    case ASetEnv{loc, x}:
      loc
    case AGate{loc}:
      loc
    case ALeft{loc, x}:
      loc
    case ARight{loc, x}:
      loc
    case AAbort{loc, m}:
      loc
    case ABot{loc}:
      loc
    case ACheck{loc, c}:
      loc
    case ARef{loc, r}:
      loc

# A closed data tree (dataLiteral).
def data.lit(t: A) -> Bool:
  match t:
    case AZero{loc}:
      True{}
    case APair{loc, a, b}:
      Bool.and(data.lit(a), data.lit(b))
    case other:
      False{}

def path.snoc(m: Maybe<&2, List<&2, U32>>, +s: U32) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{p}:
      Some{List.append(&2, U32, p, [s])}
    case None{}:
      None{}

# The env path of an occurrence (envPath), innermost projection first.
def env.path(t: A) -> Maybe<&2, List<&2, U32>>:
  match t:
    case AEnv{loc}:
      Some{[]}
    case AUns{loc}:
      Some{[]}
    case ALeft{loc, x}:
      path.snoc(env.path(x), 0)
    case ARight{loc, x}:
      path.snoc(env.path(x), 1)
    case ACheck{loc, c}:
      env.path(c)
    case other:
      None{}

# Rendering (Telomare.Error)
# ---------

def render.at(m: Maybe<&2, String>) -> String:
  match m:
    case Some{place}:
      " (at " ++ place ++ ")"
    case None{}:
      ""

def blame.render(b: Blame) -> String:
  match b:
    case Blame{loc, why, fr}:
      why ++ render.at(Lc.render_compact(loc))

def blames.render(bs: List<&2, Blame>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{b, rest}:
      "  " ++ blame.render(b) ++ "\n" ++ blames.render(rest)

# renderEALError
def render(e: Err) -> String:
  match e:
    case TypeMismatch{loc, msg}:
      "certification failed: " ++ msg ++ render.at(Lc.render_compact(loc))
    case BoxConflict{need, forbid}:
      "certification failed: a duplicated value cannot be boxed:\n  boxing required: "
        ++ blame.render(need) ++ "\n  boxing forbidden: " ++ blame.render(forbid)
    case GaveUp{msg}:
      "certification gave up (the constraint solver ran out of budget):\n  " ++ msg
    case Unsat{bs}:
      "certification failed: no box decoration satisfies these constraints together:\n" ++ blames.render(bs)
    case DependencyFailed{h}:
      "a function body this program depends on failed certification: " ++ h
    case Internal{msg}:
      "certification internal error (analyzer bug): " ++ msg

# Accessors (generated: /tmp/bx/eal2/acc.py)
# ---------

def s.tb.got(bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (tb, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.tb(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.tb.got(bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, tb, i))

def s.tb.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{Array.set(U32, tb, i, x), bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.tb.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{x, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, tb)

def s.bp.got(tb: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (bp, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.bp(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.bp.got(tb, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, bp, i))

def s.bp.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, Array.set(U32, bp, i, x), ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.bp.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, x, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, bp)

def s.ci.got(tb: Array<U32>, bp: Array<U32>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<CI> & CI) -> S & CI:
  (ci, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.ci(s: S, +i: U32) -> S & CI:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.ci.got(tb, bp, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(CI, ci, i))

def s.ci.set(s: S, +i: U32, x: CI) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, Array.set(CI, ci, i, x), tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ci.swap(s: S, x: Array<CI>) -> S & Array<CI>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, x, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ci)

def s.tp.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (tp, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.tp(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.tp.got(tb, bp, ci, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, tp, i))

def s.tp.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, Array.set(U32, tp, i, x), ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.tp.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, x, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, tp)

def s.ts.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<List<&2, TE>> & List<&2, TE>) -> S & List<&2, TE>:
  (ts, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.ts(s: S, +i: U32) -> S & List<&2, TE>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.ts.got(tb, bp, ci, tp, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(List<&2, TE>, ts, i))

def s.ts.set(s: S, +i: U32, x: List<&2, TE>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, Array.set(List<&2, TE>, ts, i, x), pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ts.swap(s: S, x: Array<List<&2, TE>>) -> S & Array<List<&2, TE>>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, x, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ts)

def s.pr.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (pr, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.pr(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.pr.got(tb, bp, ci, tp, ts, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, pr, i))

def s.pr.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, Array.set(U32, pr, i, x), ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.pr.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, x, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, pr)

def s.ap.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<Ap> & Ap) -> S & Ap:
  (ap, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.ap(s: S, +i: U32) -> S & Ap:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.ap.got(tb, bp, ci, tp, ts, pr, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(Ap, ap, i))

def s.ap.set(s: S, +i: U32, x: Ap) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, Array.set(Ap, ap, i, x), tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ap.swap(s: S, x: Array<Ap>) -> S & Array<Ap>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, x, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ap)

def s.tm.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<Mt> & Mt) -> S & Mt:
  (tm, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.tm(s: S, +i: U32) -> S & Mt:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.tm.got(tb, bp, ci, tp, ts, pr, ap, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(Mt, tm, i))

def s.tm.set(s: S, +i: U32, x: Mt) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, Array.set(Mt, tm, i, x), bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.tm.swap(s: S, x: Array<Mt>) -> S & Array<Mt>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, x, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, tm)

def s.bd.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<Bd> & Bd) -> S & Bd:
  (bd, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.bd(s: S, +i: U32) -> S & Bd:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.bd.got(tb, bp, ci, tp, ts, pr, ap, tm, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(Bd, bd, i))

def s.bd.set(s: S, +i: U32, x: Bd) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, Array.set(Bd, bd, i, x), nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.bd.swap(s: S, x: Array<Bd>) -> S & Array<Bd>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, x, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, bd)

def s.nv(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, +nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, nv)

def s.nv.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, x, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.nv.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, x, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, nv)

def s.vd(s: S) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, +vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, vd)

def s.vd.set(s: S, x: Nat) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, x, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.vd.swap(s: S, x: Nat) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, x, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, vd)

def s.np(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, +np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, np)

def s.np.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, x, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.np.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, x, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, np)

def s.pd(s: S) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, +pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, pd)

def s.pd.set(s: S, x: Nat) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, x, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.pd.swap(s: S, x: Nat) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, x, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, pd)

def s.na(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, +na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, na)

def s.na.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, x, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.na.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, x, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, na)

def s.ad(s: S) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, +ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ad)

def s.ad.set(s: S, x: Nat) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, x, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ad.swap(s: S, x: Nat) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, x, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ad)

def s.eqs(s: S) -> S & List<&2, SumEq>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, +eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, eqs)

def s.eqs.set(s: S, x: List<&2, SumEq>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, x, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.eqs.swap(s: S, x: List<&2, SumEq>) -> S & List<&2, SumEq>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, x, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, eqs)

def s.neq(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, +neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, neq)

def s.neq.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, x, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.neq.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, x, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, neq)

def s.dfs(s: S) -> S & List<&2, Df>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, +dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, dfs)

def s.dfs.set(s: S, x: List<&2, Df>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, x, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.dfs.swap(s: S, x: List<&2, Df>) -> S & List<&2, Df>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, x, ndf, lfs, nlf, frame, uni, err, cn, ncn}, dfs)

def s.ndf(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, +ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ndf)

def s.ndf.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, x, lfs, nlf, frame, uni, err, cn, ncn}

def s.ndf.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, x, lfs, nlf, frame, uni, err, cn, ncn}, ndf)

def s.lfs(s: S) -> S & List<&2, Lp>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, +lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, lfs)

def s.lfs.set(s: S, x: List<&2, Lp>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, x, nlf, frame, uni, err, cn, ncn}

def s.lfs.swap(s: S, x: List<&2, Lp>) -> S & List<&2, Lp>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, x, nlf, frame, uni, err, cn, ncn}, lfs)

def s.nlf(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, +nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, nlf)

def s.nlf.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, x, frame, uni, err, cn, ncn}

def s.nlf.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, x, frame, uni, err, cn, ncn}, nlf)

def s.frame(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, +frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, frame)

def s.frame.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, x, uni, err, cn, ncn}

def s.frame.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, x, uni, err, cn, ncn}, frame)

def s.uni(s: S) -> S & Bool:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, +uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, uni)

def s.uni.set(s: S, x: Bool) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, x, err, cn, ncn}

def s.uni.swap(s: S, x: Bool) -> S & Bool:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, x, err, cn, ncn}, uni)

def s.err(s: S) -> S & Maybe<&2, Err>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, +err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, err)

def s.err.set(s: S, x: Maybe<&2, Err>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, x, cn, ncn}

def s.err.swap(s: S, x: Maybe<&2, Err>) -> S & Maybe<&2, Err>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, x, cn, ncn}, err)

def s.cn(s: S) -> S & List<&2, CN>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, +cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, cn)

def s.cn.set(s: S, x: List<&2, CN>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, x, ncn}

def s.cn.swap(s: S, x: List<&2, CN>) -> S & List<&2, CN>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, x, ncn}, cn)

def s.ncn(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, +ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ncn)

def s.ncn.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, x}

def s.ncn.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, x}, ncn)

def gr.vx.got(nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, String>>, r: Array<U32> & U32) -> GR & U32:
  (vx, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.vx(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.vx.got(nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, vx, i))

def gr.vx.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{Array.set(U32, vx, i, x), nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.vx.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{x, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, vx)

def gr.nd.got(vx: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, String>>, r: Array<U32> & U32) -> GR & U32:
  (nd, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.nd(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.nd.got(vx, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, nd, i))

def gr.nd.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, Array.set(U32, nd, i, x), g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.nd.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, x, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, nd)

def gr.g.got(vx: Array<U32>, nd: Array<U32>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, String>>, r: Array<List<&2, U32>> & List<&2, U32>) -> GR & List<&2, U32>:
  (g, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.g(s: GR, +i: U32) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.g.got(vx, nd, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(List<&2, U32>, g, i))

def gr.g.set(s: GR, +i: U32, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, Array.set(List<&2, U32>, g, i, x), gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.g.swap(s: GR, x: Array<List<&2, U32>>) -> GR & Array<List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, x, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, g)

def gr.gt.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, String>>, r: Array<List<&2, U32>> & List<&2, U32>) -> GR & List<&2, U32>:
  (gt, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.gt(s: GR, +i: U32) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.gt.got(vx, nd, g, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(List<&2, U32>, gt, i))

def gr.gt.set(s: GR, +i: U32, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, Array.set(List<&2, U32>, gt, i, x), vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.gt.swap(s: GR, x: Array<List<&2, U32>>) -> GR & Array<List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, x, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, gt)

def gr.vis.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, String>>, r: Array<U32> & U32) -> GR & U32:
  (vis, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.vis(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.vis.got(vx, nd, g, gt, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, vis, i))

def gr.vis.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, Array.set(U32, vis, i, x), sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.vis.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, x, sc, n, po, cur, trs, ntr, st, top, pass, tl}, vis)

def gr.sc.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, String>>, r: Array<U32> & U32) -> GR & U32:
  (sc, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.sc(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.sc.got(vx, nd, g, gt, vis, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, sc, i))

def gr.sc.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, Array.set(U32, sc, i, x), n, po, cur, trs, ntr, st, top, pass, tl}

def gr.sc.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, x, n, po, cur, trs, ntr, st, top, pass, tl}, sc)

def gr.n(s: GR) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, +n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, n)

def gr.n.set(s: GR, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, x, po, cur, trs, ntr, st, top, pass, tl}

def gr.n.swap(s: GR, x: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, x, po, cur, trs, ntr, st, top, pass, tl}, n)

def gr.po(s: GR) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, +po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, po)

def gr.po.set(s: GR, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, x, cur, trs, ntr, st, top, pass, tl}

def gr.po.swap(s: GR, x: List<&2, U32>) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, x, cur, trs, ntr, st, top, pass, tl}, po)

def gr.cur(s: GR) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, +cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, cur)

def gr.cur.set(s: GR, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, x, trs, ntr, st, top, pass, tl}

def gr.cur.swap(s: GR, x: List<&2, U32>) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, x, trs, ntr, st, top, pass, tl}, cur)

def gr.trs(s: GR) -> GR & List<&2, List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, +trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, trs)

def gr.trs.set(s: GR, x: List<&2, List<&2, U32>>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, x, ntr, st, top, pass, tl}

def gr.trs.swap(s: GR, x: List<&2, List<&2, U32>>) -> GR & List<&2, List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, x, ntr, st, top, pass, tl}, trs)

def gr.ntr(s: GR) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, +ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, ntr)

def gr.ntr.set(s: GR, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, x, st, top, pass, tl}

def gr.ntr.swap(s: GR, x: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, x, st, top, pass, tl}, ntr)

def gr.st(s: GR) -> GR & List<&2, DFr>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, +st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, st)

def gr.st.set(s: GR, x: List<&2, DFr>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, x, top, pass, tl}

def gr.st.swap(s: GR, x: List<&2, DFr>) -> GR & List<&2, DFr>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, x, top, pass, tl}, st)

def gr.top(s: GR) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, +top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, top)

def gr.top.set(s: GR, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, x, pass, tl}

def gr.top.swap(s: GR, x: List<&2, U32>) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, x, pass, tl}, top)

def gr.pass(s: GR) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, +pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, pass)

def gr.pass.set(s: GR, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, x, tl}

def gr.pass.swap(s: GR, x: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, x, tl}, pass)

def gr.tl.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, r: Array<List<&2, String>> & List<&2, String>) -> GR & List<&2, String>:
  (tl, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.tl(s: GR, +i: U32) -> GR & List<&2, String>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.tl.got(vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, Array.get(List<&2, String>, tl, i))

def gr.tl.set(s: GR, +i: U32, x: List<&2, String>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, Array.set(List<&2, String>, tl, i, x)}

def gr.tl.swap(s: GR, x: Array<List<&2, String>>) -> GR & Array<List<&2, String>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, x}, tl)

# Failure
# -------

def fail.at(m: Maybe<&2, Err>, s: S, e: Err) -> S:
  match m:
    case Some{x}:
      s.err.set(s, Some{x})
    case None{}:
      s.err.set(s, Some{e})

# Keep the first failure.
def fail.k1(e: Err, kr: S & Maybe<&2, Err>) -> S:
  (s, m) = kr
  fail.at(m, s, e)

def fail(s: S, e: Err) -> S:
  fail.k1(e, s.err.swap(s, None{}))

def failed.at(m: Maybe<&2, Err>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def failed.k1(kr: S & Maybe<&2, Err>) -> S & Bool:
  (s, m) = kr
  (s, failed.at(m))

def failed(s: S) -> S & Bool:
  failed.k1(s.err(s))

# Variables
# ---------

def grow(s: S) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, +vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{ANode{tb, Array.new(U32, vd, 0)}, ANode{bp, Array.new(U32, vd, 0)}, ANode{ci, Array.new(CI, vd, CUnr{})},
        ANode{tp, Array.new(U32, vd, 0)}, ANode{ts, Array.new(List<&2, TE>, vd, [])}, pr, ap, tm, bd, nv,
        (vd + 1n : Nat), np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def fresh.at(full: Bool, s: S, +i: U32) -> S & U32:
  match full:
    case True{}:
      (s.nv.set(grow(s), (i + 1 : U32)), i)
    case False{}:
      (s.nv.set(s, (i + 1 : U32)), i)

# freshInt
def fresh.k2(+i: U32, kr: S & Nat) -> S & U32:
  (s, +vd) = kr
  fresh.at(U32.is_ge(i, U32.shln(1, vd)), s, i)

def fresh.k1(kr: S & U32) -> S & U32:
  (s, +i) = kr
  fresh.k2(i, s.vd(s))

def fresh(s: S) -> S & U32:
  fresh.k1(s.nv(s))

def fresh.tau.k1(kr: S & U32) -> S & U32:
  (s, +i) = kr
  (s, ty.var(i))

def fresh.tau(s: S) -> S & U32:
  fresh.tau.k1(fresh(s))

# freshSigma: the bang, then the type.
def fresh.sig.k2(+b: U32, kr: S & U32) -> S & Sg:
  (s, +t) = kr
  (s, Sg{b, t})

def fresh.sig.k1(kr: S & U32) -> S & Sg:
  (s, +b) = kr
  fresh.sig.k2(b, fresh.tau(s))

def fresh.sig(s: S) -> S & Sg:
  fresh.sig.k1(fresh(s))

def pr.grow(s: S) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, +pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, ANode{pr, Array.new(U32, pd, 0)}, ap, tm, bd, nv, vd, np, (pd + 1n : Nat), na, ad,
        eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def pair.write(s: S, +p: U32, a: Sg, b: Sg) -> S & U32:
  match a:
    case Sg{+ab, +at}:
      match b:
        case Sg{+bb, +bt}:
          +w: U32 = (p * 4 : U32)
          (s.np.set(s.pr.set(s.pr.set(s.pr.set(s.pr.set(s, w, ab), (w + 1 : U32), at), (w + 2 : U32), bb),
            (w + 3 : U32), bt), (p + 1 : U32)), ty.pair(p))

def pair.put(full: Bool, s: S, +p: U32, a: Sg, b: Sg) -> S & U32:
  match full:
    case True{}:
      pair.write(pr.grow(s), p, a, b)
    case False{}:
      pair.write(s, p, a, b)

# A new pair type of two sigmas.
def pair.new.k2(a: Sg, b: Sg, +p: U32, kr: S & Nat) -> S & U32:
  (s, +pd) = kr
  pair.put(U32.is_gt(((p + 1 : U32) * 4 : U32), U32.shln(1, pd)), s, p, a, b)

def pair.new.k1(a: Sg, b: Sg, kr: S & U32) -> S & U32:
  (s, +p) = kr
  pair.new.k2(a, b, p, s.pd(s))

def pair.new(s: S, a: Sg, b: Sg) -> S & U32:
  pair.new.k1(a, b, s.np(s))

# The sigmas of a pair type.
def pair.get.k4(+ab: U32, +at: U32, +bb: U32, kr: S & U32) -> S & PS:
  (s, +bt) = kr
  (s, PS{Sg{ab, at}, Sg{bb, bt}})

def pair.get.k3(+w: U32, +ab: U32, +at: U32, kr: S & U32) -> S & PS:
  (s, +bb) = kr
  pair.get.k4(ab, at, bb, s.pr(s, (w + 3 : U32)))

def pair.get.k2(+w: U32, +ab: U32, kr: S & U32) -> S & PS:
  (s, +at) = kr
  pair.get.k3(w, ab, at, s.pr(s, (w + 2 : U32)))

def pair.get.k1(+w: U32, kr: S & U32) -> S & PS:
  (s, +ab) = kr
  pair.get.k2(w, ab, s.pr(s, (w + 1 : U32)))

def pair.get(s: S, +t: U32) -> S & PS:
  +w: U32 = (ty.of(t) * 4 : U32)
  pair.get.k1(w, s.pr(s, w))

def is.var(+t: U32) -> Bool:
  U32.is_eq((t .&. 7 : U32), 1)

def walk.var(var: Bool, s: S, +b: U32) -> WkN:
  match var:
    case True{}:
      WkMore{s, b}
    case False{}:
      WkStop{s, b}

def walk.at(unbound: Bool, s: S, +t: U32, +b: U32) -> WkN:
  match unbound:
    case True{}:
      WkStop{s, t}
    case False{}:
      walk.var(is.var(b), s, b)

def walk.step.k1(+t: U32, kr: S & U32) -> WkN:
  (s, +b) = kr
  walk.at(U32.is_eq(b, 0), s, t, b)

def walk.step(s: S, +t: U32) -> WkN:
  walk.step.k1(t, s.tb(s, ty.of(t)))

def walk.fin(n: WkN) -> S & U32:
  match n:
    case WkMore{s, +t}:
      (s, t)
    case WkStop{s, +t}:
      (s, t)

def walk.loop(fuel: Nat, n: WkN) -> S & U32:
  match fuel:
    case 0n:
      walk.fin(n)
    case 1n+f:
      match n:
        case WkMore{s, +t}:
          walk.loop(f, walk.step(s, t))
        case WkStop{s, +t}:
          (s, t)

# walkTau
def walk(s: S, +t: U32) -> S & U32:
  walk.loop(big(), walk.var(is.var(t), s, t))

def bf.at(root: Bool, s: S, +j: U32, +p: U32) -> BFN:
  match root:
    case True{}:
      BFStop{s, j}
    case False{}:
      BFMore{s, (p - 1 : U32)}

def bf.step.k1(+j: U32, kr: S & U32) -> BFN:
  (s, +p) = kr
  bf.at(U32.is_eq(p, 0), s, j, p)

def bf.step(s: S, +j: U32) -> BFN:
  bf.step.k1(j, s.bp(s, j))

def bf.fin(n: BFN) -> S & U32:
  match n:
    case BFMore{s, +j}:
      (s, j)
    case BFStop{s, +r}:
      (s, r)

def bf.loop(fuel: Nat, n: BFN) -> S & U32:
  match fuel:
    case 0n:
      bf.fin(n)
    case 1n+f:
      match n:
        case BFMore{s, +j}:
          bf.loop(f, bf.step(s, j))
        case BFStop{s, +r}:
          (s, r)

def bf.pat(stop: Bool, s: S, +j: U32, +r: U32, +p: U32) -> BFP:
  match stop:
    case True{}:
      BFPStop{s}
    case False{}:
      BFPMore{s.bp.set(s, j, (r + 1 : U32)), (p - 1 : U32)}

def bf.pstep.k1(+j: U32, +r: U32, kr: S & U32) -> BFP:
  (s, +p) = kr
  bf.pat(Bool.or(U32.is_eq(p, 0), U32.is_eq(p, (r + 1 : U32))), s, j, r, p)

def bf.pstep(s: S, +j: U32, +r: U32) -> BFP:
  bf.pstep.k1(j, r, s.bp(s, j))

def bf.pfin(n: BFP) -> S:
  match n:
    case BFPMore{s, +j}:
      s
    case BFPStop{s}:
      s

def bf.ploop(fuel: Nat, n: BFP, +r: U32) -> S:
  match fuel:
    case 0n:
      bf.pfin(n)
    case 1n+f:
      match n:
        case BFPMore{s, +j}:
          bf.ploop(f, bf.pstep(s, j, r), r)
        case BFPStop{s}:
          s

# The root, without compression.
def root.b(s: S, +b: U32) -> S & U32:
  bf.loop(big(), bf.step(s, b))

# The root, with path compression.
def find.b.k1(+b: U32, kr: S & U32) -> S & U32:
  (s, +r) = kr
  (bf.ploop(big(), bf.pstep(s, b, r), r), r)

def find.b(s: S, +b: U32) -> S & U32:
  find.b.k1(b, root.b(s, b))

def bl.in(+fr: U32, b: Blame) -> Blame:
  match b:
    case Blame{+loc, +why, +bf}:
      Blame{loc, why, Bool.pick(U32, U32.is_eq(bf, 0), fr, bf)}

# inFrame, on a class's blame.
def ci.in(+fr: U32, c: CI) -> CI:
  match c:
    case CUnr{}:
      CUnr{}
    case CZero{bl}:
      CZero{bl.in(fr, bl)}
    case CLevel{n, bl}:
      CLevel{n, bl.in(fr, bl)}

def ci.zero(c: CI) -> Bool:
  match c:
    case CZero{bl}:
      True{}
    case other:
      False{}

def ci.lb(c: CI) -> U32:
  match c:
    case CLevel{+n, bl}:
      n
    case other:
      0

def lvl.raise(up: Bool, s: S, +r: U32, +n: U32, +bl: Blame) -> S & Bool:
  match up:
    case True{}:
      (s.ci.set(s, r, CLevel{n, bl}), True{})
    case False{}:
      (s, False{})

def constrain.k(c: CI, +nc: CI, s: S, +r: U32) -> S & Bool:
  match c:
    case CUnr{}:
      match nc:
        case CUnr{}:
          (s, False{})
        case other:
          (s.ci.set(s, r, other), True{})
    case CZero{+z}:
      match nc:
        case CLevel{n, +l}:
          (fail(s, BoxConflict{l, z}), False{})
        case other:
          (s, False{})
    case CLevel{+la, +l}:
      match nc:
        case CZero{+z}:
          (fail(s, BoxConflict{l, z}), False{})
        case CLevel{+lb, +bl}:
          lvl.raise(U32.is_lt(la, lb), s, r, lb, bl)
        case CUnr{}:
          (s, False{})

# constrainB: whether the class changed.
def constrain.k3(nc: CI, +fr: U32, +r: U32, kr: S & CI) -> S & Bool:
  (s, +c) = kr
  constrain.k(c, ci.in(fr, nc), s, r)

def constrain.k2(nc: CI, +fr: U32, kr: S & U32) -> S & Bool:
  (s, +r) = kr
  constrain.k3(nc, fr, r, s.ci(s, r))

def constrain.k1(+b: U32, nc: CI, kr: S & U32) -> S & Bool:
  (s, +fr) = kr
  constrain.k2(nc, fr, find.b(s, b))

def constrain(s: S, +b: U32, nc: CI) -> S & Bool:
  constrain.k1(b, nc, s.frame(s))

def constrain_(s: S, +b: U32, nc: CI) -> S:
  Pair.fst(S, Bool, constrain(s, b, nc))

def union.b.put(s: S, +ra: U32, +rb: U32, +m: CI) -> S:
  s.ci.set(s.ci.set(s.bp.set(s, ra, (rb + 1 : U32)), rb, m), ra, CUnr{})

# mergeClasses, then the merge.
def union.b.k(ia: CI, +ib: CI, s: S, +ra: U32, +rb: U32) -> S:
  match ia:
    case CUnr{}:
      union.b.put(s, ra, rb, ib)
    case CZero{+z}:
      match ib:
        case CLevel{n, +l}:
          fail(s, BoxConflict{l, z})
        case other:
          union.b.put(s, ra, rb, CZero{z})
    case CLevel{+la, +l}:
      match ib:
        case CZero{+z}:
          fail(s, BoxConflict{l, z})
        case CLevel{+lb, +l2}:
          union.b.put(s, ra, rb, Bool.pick(CI, U32.is_ge(la, lb), CLevel{la, l}, CLevel{lb, l2}))
        case CUnr{}:
          union.b.put(s, ra, rb, CLevel{la, l})

def union.b.at.k2(+ra: U32, +rb: U32, +ia: CI, kr: S & CI) -> S:
  (s, +ib) = kr
  union.b.k(ia, ib, s, ra, rb)

def union.b.at.k1(+ra: U32, +rb: U32, kr: S & CI) -> S:
  (s, +ia) = kr
  union.b.at.k2(ra, rb, ia, s.ci(s, rb))

def union.b.at(same: Bool, s: S, +ra: U32, +rb: U32) -> S:
  match same:
    case True{}:
      s
    case False{}:
      union.b.at.k1(ra, rb, s.ci(s, ra))

# unionB
def union.b.k2(+ra: U32, kr: S & U32) -> S:
  (s, +rb) = kr
  union.b.at(U32.is_eq(ra, rb), s, ra, rb)

def union.b.k1(+b: U32, kr: S & U32) -> S:
  (s, +ra) = kr
  union.b.k2(ra, find.b(s, b))

def union.b(s: S, +a: U32, +b: U32) -> S:
  union.b.k1(b, find.b(s, a))

def union.bs(xs: List<&2, U32>, ys: List<&2, U32>, s: S) -> S:
  match xs:
    case Nil{}:
      s
    case Con{+x, xr}:
      match ys:
        case Nil{}:
          s
        case Con{+y, yr}:
          union.bs(xr, yr, union.b(s, x, y))

def tf.at(root: Bool, s: S, +j: U32, +p: U32) -> TFN:
  match root:
    case True{}:
      TFStop{s, j}
    case False{}:
      TFMore{s, (p - 1 : U32)}

def tf.step.k1(+j: U32, kr: S & U32) -> TFN:
  (s, +p) = kr
  tf.at(U32.is_eq(p, 0), s, j, p)

def tf.step(s: S, +j: U32) -> TFN:
  tf.step.k1(j, s.tp(s, j))

def tf.fin(n: TFN) -> S & U32:
  match n:
    case TFMore{s, +j}:
      (s, j)
    case TFStop{s, +r}:
      (s, r)

def tf.loop(fuel: Nat, n: TFN) -> S & U32:
  match fuel:
    case 0n:
      tf.fin(n)
    case 1n+f:
      match n:
        case TFMore{s, +j}:
          tf.loop(f, tf.step(s, j))
        case TFStop{s, +r}:
          (s, r)

def tf.pat(stop: Bool, s: S, +j: U32, +r: U32, +p: U32) -> TFP:
  match stop:
    case True{}:
      TFPStop{s}
    case False{}:
      TFPMore{s.tp.set(s, j, (r + 1 : U32)), (p - 1 : U32)}

def tf.pstep.k1(+j: U32, +r: U32, kr: S & U32) -> TFP:
  (s, +p) = kr
  tf.pat(Bool.or(U32.is_eq(p, 0), U32.is_eq(p, (r + 1 : U32))), s, j, r, p)

def tf.pstep(s: S, +j: U32, +r: U32) -> TFP:
  tf.pstep.k1(j, r, s.tp(s, j))

def tf.pfin(n: TFP) -> S:
  match n:
    case TFPMore{s, +j}:
      s
    case TFPStop{s}:
      s

def tf.ploop(fuel: Nat, n: TFP, +r: U32) -> S:
  match fuel:
    case 0n:
      tf.pfin(n)
    case 1n+f:
      match n:
        case TFPMore{s, +j}:
          tf.ploop(f, tf.pstep(s, j, r), r)
        case TFPStop{s}:
          s

# The root, without compression.
def root.t(s: S, +b: U32) -> S & U32:
  tf.loop(big(), tf.step(s, b))

# The root, with path compression.
def find.t.k1(+b: U32, kr: S & U32) -> S & U32:
  (s, +r) = kr
  (tf.ploop(big(), tf.pstep(s, b, r), r), r)

def find.t(s: S, +b: U32) -> S & U32:
  find.t.k1(b, root.t(s, b))

# capturesOf: a class's tags with their records.
def captures.of.k1(kr: S & U32) -> S & List<&2, TE>:
  (s, +r) = kr
  s.ts(s, r)

def captures.of(s: S, +i: U32) -> S & List<&2, TE>:
  captures.of.k1(find.t(s, i))

def te.tags(xs: List<&2, TE>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case TE{+tag, cap, ifc}:
          tag <> te.tags(rest)

def te.with.cap(xs: List<&2, TE>, +c: Sg) -> List<&2, TE>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case TE{+tag, cap, +ifc}:
          TE{tag, Some{c}, ifc} <> te.with.cap(rest, c)

# freshCode: a fresh code class holding these tags.
def fresh.code.k1(+tags: List<&2, TE>, kr: S & U32) -> S & U32:
  (s, +i) = kr
  (s.ts.set(s, i, tags), ty.code(i))

def fresh.code(s: S, +tags: List<&2, TE>) -> S & U32:
  fresh.code.k1(tags, fresh(s))

def builtin.code(s: S, +tag: U32) -> S & U32:
  fresh.code(s, [TE{tag, None{}, None{}}])

# packageClass: the tags of class i, each now carrying this capture.
def package.class.k2(+c: Sg, infos: List<&2, TE>, kr: S & U32) -> S & U32:
  (s, +p) = kr
  (s.ts.set(s, p, te.with.cap(infos, c)), p)

def package.class.k1(+c: Sg, kr: S & List<&2, TE>) -> S & U32:
  (s, infos) = kr
  package.class.k2(c, infos, fresh(s))

def package.class(s: S, +i: U32, +c: Sg) -> S & U32:
  package.class.k1(c, captures.of(s, i))

# Constraints and records
# -----------------------

def forced.zero.k1(+bl: Blame, kr: S & U32) -> S & U32:
  (s, +b) = kr
  (constrain_(s, b, CZero{bl}), b)

def forced.zero(s: S, +bl: Blame) -> S & U32:
  forced.zero.k1(bl, fresh(s))

# plainSigma
def plain.k1(+t: U32, kr: S & U32) -> S & Sg:
  (s, +b) = kr
  (s, Sg{b, t})

def plain(s: S, +loc: Lc.Loc, +what: String, +t: U32) -> S & Sg:
  plain.k1(t, forced.zero(s, blame(loc, what)))

# addSumEq
def add.eq.k3(+bl: Blame, +lhs: List<&2, U32>, +rhs: U32, +fr: U32, old: List<&2, SumEq>, kr: S & U32) -> S:
  (s, +n) = kr
  s.neq.set(s.eqs.set(s, SumEq{lhs, rhs, bl.in(fr, bl)} <> old), (n + 1 : U32))

def add.eq.k2(+bl: Blame, +lhs: List<&2, U32>, +rhs: U32, +fr: U32, kr: S & List<&2, SumEq>) -> S:
  (s, old) = kr
  add.eq.k3(bl, lhs, rhs, fr, old, s.neq(s))

def add.eq.k1(+bl: Blame, +lhs: List<&2, U32>, +rhs: U32, kr: S & U32) -> S:
  (s, +fr) = kr
  add.eq.k2(bl, lhs, rhs, fr, s.eqs.swap(s, []))

def add.eq(s: S, +bl: Blame, +lhs: List<&2, U32>, +rhs: U32) -> S:
  add.eq.k1(bl, lhs, rhs, s.frame(s))

def rec.leaf.k2(+fr: U32, +base: U32, +d: U32, old: List<&2, Lp>, kr: S & U32) -> S:
  (s, +n) = kr
  s.nlf.set(s.lfs.set(s, Lp{fr, base, d} <> old), (n + 1 : U32))

def rec.leaf.k1(+fr: U32, +base: U32, +d: U32, kr: S & List<&2, Lp>) -> S:
  (s, old) = kr
  rec.leaf.k2(fr, base, d, old, s.nlf(s))

def rec.leaf(s: S, +fr: U32, +base: U32, +d: U32) -> S:
  rec.leaf.k1(fr, base, d, s.lfs.swap(s, []))

# recordDefer
def rec.defer.k2(+fi: U32, +b: U32, old: List<&2, Df>, kr: S & U32) -> S:
  (s, +n) = kr
  s.ndf.set(s.dfs.set(s, Df{fi, b} <> old), (n + 1 : U32))

def rec.defer.k1(+fi: U32, +b: U32, kr: S & List<&2, Df>) -> S:
  (s, old) = kr
  rec.defer.k2(fi, b, old, s.ndf(s))

def rec.defer(s: S, +fi: U32, +b: U32) -> S:
  rec.defer.k1(fi, b, s.dfs.swap(s, []))

def ap.none() -> Ap:
  Ap{0, Sg{0, 0}, Sg{0, 0}, Lc.Unknown{}, []}

def ap.grow(s: S) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, +ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ANode{ap, Array.new(Ap, ad, ap.none())}, tm, bd, nv, vd, np, pd, na, (ad + 1n : Nat),
        eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def ap.put(full: Bool, s: S, +n: U32, +a: Ap) -> S:
  match full:
    case True{}:
      s.na.set(s.ap.set(ap.grow(s), n, a), (n + 1 : U32))
    case False{}:
      s.na.set(s.ap.set(s, n, a), (n + 1 : U32))

# Register an apply site under the next number.
def ap.new.k2(+a: Ap, +n: U32, kr: S & Nat) -> S:
  (s, +ad) = kr
  ap.put(U32.is_ge(n, U32.shln(1, ad)), s, n, a)

def ap.new.k1(+a: Ap, kr: S & U32) -> S:
  (s, +n) = kr
  ap.new.k2(a, n, s.ad(s))

def ap.new(s: S, +a: Ap) -> S:
  ap.new.k1(a, s.na(s))

# The state
# ---------

def st.new(bd: Array<Bd>, +nb: U32, +uni: Bool) -> S:
  +d = Ln.depth.of(nb)
  S{Array.new(U32, 10n, 0), Array.new(U32, 10n, 0), Array.new(CI, 10n, CUnr{}), Array.new(U32, 10n, 0),
    Array.new(List<&2, TE>, 10n, []), Array.new(U32, 10n, 0), Array.new(Ap, 6n, ap.none()), Array.new(Mt, d, MtNone{}),
    bd, 0, 10n, 0, 10n, 0, 6n, [], 0, [], 0, [], 0, 0, uni, None{}, [], 0}

# Showing types (deepShowTau)
# -------------

def bd.of(s: S, +r: U32) -> S & Bd:
  s.bd(s, r)

def bd.h(b: Bd) -> String:
  match b:
    case Bd{+h, fi, link, t}:
      h

def bd.fi(b: Bd) -> U32:
  match b:
    case Bd{h, +fi, link, t}:
      fi

def tag.show.code(r: S & Bd) -> S & String:
  (s, b) = r
  (s, "TCode " ++ bd.h(b))

def tag.show.at(gate: Bool, gatefn: Bool, s: S, +tag: U32) -> S & String:
  match gate:
    case True{}:
      (s, "TGate")
    case False{}:
      match gatefn:
        case True{}:
          (s, "TGateFn")
        case False{}:
          tag.show.code(bd.of(s, tag))

# The derived Show of a Tag.
def tag.show(s: S, +tag: U32) -> S & String:
  tag.show.at(U32.is_eq(tag, tag.gate()), U32.is_eq(tag, tag.gatefn()), s, tag)

def tags.show.acc.k1(acc: List<&2, String>, kr: S & String) -> S & List<&2, String>:
  (s, +a) = kr
  (s, a <> acc)

def tags.show.acc(s: S, acc: List<&2, String>, +x: U32) -> S & List<&2, String>:
  tags.show.acc.k1(acc, tag.show(s, x))

def tags.show.go(xs: List<&2, U32>, r: S & List<&2, String>) -> S & List<&2, String>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, acc) = r
      tags.show.go(rest, tags.show.acc(s, acc, x))

# show (Set.toList tags)
def tags.show.k1(kr: S & List<&2, String>) -> S & String:
  (s, acc) = kr
  (s, "[" ++ String.join(List.reverse(&2, String, acc), ",") ++ "]")

def tags.show(s: S, xs: List<&2, U32>) -> S & String:
  tags.show.k1(tags.show.go(xs, (s, [])))

def ds.zero(s: S, +t: U32) -> S & String:
  (s, "...")

def ds.one.pair.k2(+sa: String, kr: S & String) -> S & String:
  (s, +sb) = kr
  (s, "(" ++ sa ++ ", " ++ sb ++ ")")

def ds.one.pair.k1(+bt: U32, kr: S & String) -> S & String:
  (s, +sa) = kr
  ds.one.pair.k2(sa, ds.zero(s, bt))

def ds.one.pair(s: S, ps: PS) -> S & String:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              ds.one.pair.k1(bt, ds.zero(s, at))

def ds.one.k.k3(+r: U32, kr: S & String) -> S & String:
  (s, +ts) = kr
  (s, "Code#" ++ U32.show(r) ++ ts)

def ds.one.k.k2(+r: U32, kr: S & List<&2, TE>) -> S & String:
  (s, es) = kr
  ds.one.k.k3(r, tags.show(s, te.tags(es)))

def ds.one.k.k1(+t: U32, kr: S & U32) -> S & String:
  (s, +r) = kr
  ds.one.k.k2(r, captures.of(s, ty.of(t)))

def ds.one.k.k4(kr: S & U32) -> S & String:
  (s, +r) = kr
  (s, "Cap#" ++ U32.show(r))

def ds.one.k.k5(kr: S & PS) -> S & String:
  (s, ps) = kr
  ds.one.pair(s, ps)

def ds.one.k(k: K, s: S, +t: U32) -> S & String:
  match k:
    case KData{}:
      (s, "D")
    case KVar{}:
      (s, "t" ++ U32.show(ty.of(t)))
    case KCode{}:
      ds.one.k.k1(t, find.t(s, ty.of(t)))
    case KCap{}:
      ds.one.k.k4(find.t(s, ty.of(t)))
    case KAbort{}:
      (s, "_|_")
    case KPair{}:
      ds.one.k.k5(pair.get(s, t))

def ds.one.k1(kr: S & U32) -> S & String:
  (s, +w) = kr
  ds.one.k(kind(w), s, w)

def ds.one(s: S, +t: U32) -> S & String:
  ds.one.k1(walk(s, t))

def ds.two.pair.k2(+sa: String, kr: S & String) -> S & String:
  (s, +sb) = kr
  (s, "(" ++ sa ++ ", " ++ sb ++ ")")

def ds.two.pair.k1(+bt: U32, kr: S & String) -> S & String:
  (s, +sa) = kr
  ds.two.pair.k2(sa, ds.one(s, bt))

def ds.two.pair(s: S, ps: PS) -> S & String:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              ds.two.pair.k1(bt, ds.one(s, at))

def ds.two.k.k3(+r: U32, kr: S & String) -> S & String:
  (s, +ts) = kr
  (s, "Code#" ++ U32.show(r) ++ ts)

def ds.two.k.k2(+r: U32, kr: S & List<&2, TE>) -> S & String:
  (s, es) = kr
  ds.two.k.k3(r, tags.show(s, te.tags(es)))

def ds.two.k.k1(+t: U32, kr: S & U32) -> S & String:
  (s, +r) = kr
  ds.two.k.k2(r, captures.of(s, ty.of(t)))

def ds.two.k.k4(kr: S & U32) -> S & String:
  (s, +r) = kr
  (s, "Cap#" ++ U32.show(r))

def ds.two.k.k5(kr: S & PS) -> S & String:
  (s, ps) = kr
  ds.two.pair(s, ps)

def ds.two.k(k: K, s: S, +t: U32) -> S & String:
  match k:
    case KData{}:
      (s, "D")
    case KVar{}:
      (s, "t" ++ U32.show(ty.of(t)))
    case KCode{}:
      ds.two.k.k1(t, find.t(s, ty.of(t)))
    case KCap{}:
      ds.two.k.k4(find.t(s, ty.of(t)))
    case KAbort{}:
      (s, "_|_")
    case KPair{}:
      ds.two.k.k5(pair.get(s, t))

def ds.two.k1(kr: S & U32) -> S & String:
  (s, +w) = kr
  ds.two.k(kind(w), s, w)

def ds.two(s: S, +t: U32) -> S & String:
  ds.two.k1(walk(s, t))

def ds.three.pair.k2(+sa: String, kr: S & String) -> S & String:
  (s, +sb) = kr
  (s, "(" ++ sa ++ ", " ++ sb ++ ")")

def ds.three.pair.k1(+bt: U32, kr: S & String) -> S & String:
  (s, +sa) = kr
  ds.three.pair.k2(sa, ds.two(s, bt))

def ds.three.pair(s: S, ps: PS) -> S & String:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              ds.three.pair.k1(bt, ds.two(s, at))

def ds.three.k.k3(+r: U32, kr: S & String) -> S & String:
  (s, +ts) = kr
  (s, "Code#" ++ U32.show(r) ++ ts)

def ds.three.k.k2(+r: U32, kr: S & List<&2, TE>) -> S & String:
  (s, es) = kr
  ds.three.k.k3(r, tags.show(s, te.tags(es)))

def ds.three.k.k1(+t: U32, kr: S & U32) -> S & String:
  (s, +r) = kr
  ds.three.k.k2(r, captures.of(s, ty.of(t)))

def ds.three.k.k4(kr: S & U32) -> S & String:
  (s, +r) = kr
  (s, "Cap#" ++ U32.show(r))

def ds.three.k.k5(kr: S & PS) -> S & String:
  (s, ps) = kr
  ds.three.pair(s, ps)

def ds.three.k(k: K, s: S, +t: U32) -> S & String:
  match k:
    case KData{}:
      (s, "D")
    case KVar{}:
      (s, "t" ++ U32.show(ty.of(t)))
    case KCode{}:
      ds.three.k.k1(t, find.t(s, ty.of(t)))
    case KCap{}:
      ds.three.k.k4(find.t(s, ty.of(t)))
    case KAbort{}:
      (s, "_|_")
    case KPair{}:
      ds.three.k.k5(pair.get(s, t))

def ds.three.k1(kr: S & U32) -> S & String:
  (s, +w) = kr
  ds.three.k(kind(w), s, w)

def ds.three(s: S, +t: U32) -> S & String:
  ds.three.k1(walk(s, t))

def ds.four.pair.k2(+sa: String, kr: S & String) -> S & String:
  (s, +sb) = kr
  (s, "(" ++ sa ++ ", " ++ sb ++ ")")

def ds.four.pair.k1(+bt: U32, kr: S & String) -> S & String:
  (s, +sa) = kr
  ds.four.pair.k2(sa, ds.three(s, bt))

def ds.four.pair(s: S, ps: PS) -> S & String:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              ds.four.pair.k1(bt, ds.three(s, at))

def ds.four.k.k3(+r: U32, kr: S & String) -> S & String:
  (s, +ts) = kr
  (s, "Code#" ++ U32.show(r) ++ ts)

def ds.four.k.k2(+r: U32, kr: S & List<&2, TE>) -> S & String:
  (s, es) = kr
  ds.four.k.k3(r, tags.show(s, te.tags(es)))

def ds.four.k.k1(+t: U32, kr: S & U32) -> S & String:
  (s, +r) = kr
  ds.four.k.k2(r, captures.of(s, ty.of(t)))

def ds.four.k.k4(kr: S & U32) -> S & String:
  (s, +r) = kr
  (s, "Cap#" ++ U32.show(r))

def ds.four.k.k5(kr: S & PS) -> S & String:
  (s, ps) = kr
  ds.four.pair(s, ps)

def ds.four.k(k: K, s: S, +t: U32) -> S & String:
  match k:
    case KData{}:
      (s, "D")
    case KVar{}:
      (s, "t" ++ U32.show(ty.of(t)))
    case KCode{}:
      ds.four.k.k1(t, find.t(s, ty.of(t)))
    case KCap{}:
      ds.four.k.k4(find.t(s, ty.of(t)))
    case KAbort{}:
      (s, "_|_")
    case KPair{}:
      ds.four.k.k5(pair.get(s, t))

def ds.four.k1(kr: S & U32) -> S & String:
  (s, +w) = kr
  ds.four.k(kind(w), s, w)

def ds.four(s: S, +t: U32) -> S & String:
  ds.four.k1(walk(s, t))

def ds.five.pair.k2(+sa: String, kr: S & String) -> S & String:
  (s, +sb) = kr
  (s, "(" ++ sa ++ ", " ++ sb ++ ")")

def ds.five.pair.k1(+bt: U32, kr: S & String) -> S & String:
  (s, +sa) = kr
  ds.five.pair.k2(sa, ds.four(s, bt))

def ds.five.pair(s: S, ps: PS) -> S & String:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              ds.five.pair.k1(bt, ds.four(s, at))

def ds.five.k.k3(+r: U32, kr: S & String) -> S & String:
  (s, +ts) = kr
  (s, "Code#" ++ U32.show(r) ++ ts)

def ds.five.k.k2(+r: U32, kr: S & List<&2, TE>) -> S & String:
  (s, es) = kr
  ds.five.k.k3(r, tags.show(s, te.tags(es)))

def ds.five.k.k1(+t: U32, kr: S & U32) -> S & String:
  (s, +r) = kr
  ds.five.k.k2(r, captures.of(s, ty.of(t)))

def ds.five.k.k4(kr: S & U32) -> S & String:
  (s, +r) = kr
  (s, "Cap#" ++ U32.show(r))

def ds.five.k.k5(kr: S & PS) -> S & String:
  (s, ps) = kr
  ds.five.pair(s, ps)

def ds.five.k(k: K, s: S, +t: U32) -> S & String:
  match k:
    case KData{}:
      (s, "D")
    case KVar{}:
      (s, "t" ++ U32.show(ty.of(t)))
    case KCode{}:
      ds.five.k.k1(t, find.t(s, ty.of(t)))
    case KCap{}:
      ds.five.k.k4(find.t(s, ty.of(t)))
    case KAbort{}:
      (s, "_|_")
    case KPair{}:
      ds.five.k.k5(pair.get(s, t))

def ds.five.k1(kr: S & U32) -> S & String:
  (s, +w) = kr
  ds.five.k(kind(w), s, w)

def ds.five(s: S, +t: U32) -> S & String:
  ds.five.k1(walk(s, t))

# Searches over types
# -------------------

def is.pair(+t: U32) -> Bool:
  U32.is_eq((t .&. 7 : U32), 4)

def oc.var(hit: Bool, s: S, +i: U32, rest: List<&2, U32>) -> OcN:
  match hit:
    case True{}:
      OcHit{s}
    case False{}:
      OcGo{s, i, rest}

def oc.pair(ps: PS, s: S, +i: U32, rest: List<&2, U32>) -> OcN:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              OcGo{s, i, at <> (bt <> rest)}

def oc.k.k1(+i: U32, rest: List<&2, U32>, kr: S & PS) -> OcN:
  (s, ps) = kr
  oc.pair(ps, s, i, rest)

def oc.k(k: K, s: S, +i: U32, +w: U32, rest: List<&2, U32>) -> OcN:
  match k:
    case KVar{}:
      oc.var(U32.is_eq(ty.of(w), i), s, i, rest)
    case KPair{}:
      oc.k.k1(i, rest, pair.get(s, w))
    case other:
      OcGo{s, i, rest}

def oc.step.k1(+i: U32, rest: List<&2, U32>, kr: S & U32) -> OcN:
  (s, +w) = kr
  oc.k(kind(w), s, i, w, rest)

def oc.step(ts: List<&2, U32>, s: S, +i: U32) -> OcN:
  match ts:
    case Nil{}:
      OcNo{s}
    case Con{+t, rest}:
      oc.step.k1(i, rest, walk(s, t))

def oc.fin(n: OcN) -> S & Bool:
  match n:
    case OcGo{s, i, ts}:
      (s, False{})
    case OcHit{s}:
      (s, True{})
    case OcNo{s}:
      (s, False{})

def oc.loop(fuel: Nat, n: OcN) -> S & Bool:
  match fuel:
    case 0n:
      oc.fin(n)
    case 1n+f:
      match n:
        case OcGo{s, +i, ts}:
          oc.loop(f, oc.step(ts, s, i))
        case OcHit{s}:
          (s, True{})
        case OcNo{s}:
          (s, False{})

# occurs
def occurs(s: S, +i: U32, +t: U32) -> S & Bool:
  oc.loop(big(), oc.step([t], s, i))

def ex.pair(ps: PS, s: S, rest: List<&2, U32>, acc: List<&2, U32>) -> ExN:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              ExGo{s, at <> (bt <> rest), acc}

def ex.k.k1(rest: List<&2, U32>, acc: List<&2, U32>, kr: S & PS) -> ExN:
  (s, ps) = kr
  ex.pair(ps, s, rest, acc)

def ex.k(k: K, s: S, +w: U32, rest: List<&2, U32>, acc: List<&2, U32>) -> ExN:
  match k:
    case KCode{}:
      ExGo{s, rest, ty.of(w) <> acc}
    case KPair{}:
      ex.k.k1(rest, acc, pair.get(s, w))
    case other:
      ExGo{s, rest, acc}

def ex.step.k1(acc: List<&2, U32>, rest: List<&2, U32>, kr: S & U32) -> ExN:
  (s, +w) = kr
  ex.k(kind(w), s, w, rest, acc)

def ex.step(ts: List<&2, U32>, s: S, acc: List<&2, U32>) -> ExN:
  match ts:
    case Nil{}:
      ExDone{s, List.reverse(&2, U32, acc)}
    case Con{+t, rest}:
      ex.step.k1(acc, rest, walk(s, t))

def ex.fin(n: ExN) -> S & List<&2, U32>:
  match n:
    case ExGo{s, ts, acc}:
      (s, List.reverse(&2, U32, acc))
    case ExDone{s, acc}:
      (s, acc)

def ex.loop(fuel: Nat, n: ExN) -> S & List<&2, U32>:
  match fuel:
    case 0n:
      ex.fin(n)
    case 1n+f:
      match n:
        case ExGo{s, ts, acc}:
          ex.loop(f, ex.step(ts, s, acc))
        case ExDone{s, acc}:
          (s, acc)

# exposedClasses: the code classes a type exposes through pairs, in order.
def exposed(s: S, +t: U32) -> S & List<&2, U32>:
  ex.loop(big(), ex.step([t], s, []))

def sr.if(+tag: U32, ifc: Maybe<&2, If>, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>) -> List<&2, SrI>:
  match ifc:
    case Some{x}:
      match x:
        case If{env, res, doors}:
          match env:
            case Sg{eb, +et}:
              match res:
                case Sg{rb, +rt}:
                  SrArg{vis, tag <> path, et} <> (SrTy{vis, tag <> path, rt} <> rest)
    case None{}:
      rest

# A class's starts: per tag with an interface, its argument and its result.
def sr.expand(es: List<&2, TE>, +vis: List<&2, U32>, +path: List<&2, U32>) -> List<&2, SrI>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      match e:
        case TE{+tag, cap, ifc}:
          sr.if(tag, ifc, vis, path, sr.expand(rest, vis, path))

# classIfaces
def sr.class.k1(+r0: U32, +r: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>, kr: S & List<&2, TE>) -> SrN:
  (s, es) = kr
  SrGo{s, r0, List.append(&2, SrI, sr.expand(es, r <> vis, path), rest)}

def sr.class(s: S, +r0: U32, +r: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>) -> SrN:
  sr.class.k1(r0, r, vis, path, rest, captures.of(s, r))

def sr.code(hit: Bool, seen: Bool, s: S, +r0: U32, +r: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>) -> SrN:
  match hit:
    case True{}:
      SrFound{s, List.reverse(&2, U32, path)}
    case False{}:
      match seen:
        case True{}:
          SrGo{s, r0, rest}
        case False{}:
          sr.class(s, r0, r, vis, path, rest)

def sr.pair(ps: PS, s: S, +r0: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>) -> SrN:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              SrGo{s, r0, SrTy{vis, path, at} <> (SrTy{vis, path, bt} <> rest)}

def sr.ty.k1(+r0: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>, kr: S & PS) -> SrN:
  (s, ps) = kr
  sr.pair(ps, s, r0, vis, path, rest)

def sr.ty.k2(+r0: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>, kr: S & U32) -> SrN:
  (s, +r) = kr
  sr.code(U32.is_eq(r, r0), u.has(vis, r), s, r0, r, vis, path, rest)

def sr.ty(k: K, s: S, +r0: U32, +vis: List<&2, U32>, +path: List<&2, U32>, +w: U32, rest: List<&2, SrI>) -> SrN:
  match k:
    case KPair{}:
      sr.ty.k1(r0, vis, path, rest, pair.get(s, w))
    case KCode{}:
      sr.ty.k2(r0, vis, path, rest, find.t(s, ty.of(w)))
    case other:
      SrGo{s, r0, rest}

def sr.argp(ps: PS, s: S, +r0: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>) -> SrN:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          SrGo{s, r0, SrTy{vis, path, at} <> rest}

# argumentOf: an env's argument half; data or unresolved holds nothing.
def sr.arg.k1(+r0: U32, +vis: List<&2, U32>, +path: List<&2, U32>, rest: List<&2, SrI>, kr: S & PS) -> SrN:
  (s, ps) = kr
  sr.argp(ps, s, r0, vis, path, rest)

def sr.arg(pair: Bool, s: S, +r0: U32, +vis: List<&2, U32>, +path: List<&2, U32>, +w: U32, rest: List<&2, SrI>) -> SrN:
  match pair:
    case True{}:
      sr.arg.k1(r0, vis, path, rest, pair.get(s, w))
    case False{}:
      SrGo{s, r0, rest}

def sr.step.k1(+r0: U32, rest: List<&2, SrI>, +vis: List<&2, U32>, +path: List<&2, U32>, kr: S & U32) -> SrN:
  (s, +w) = kr
  sr.ty(kind(w), s, r0, vis, path, w, rest)

def sr.step.k2(+r0: U32, rest: List<&2, SrI>, +vis: List<&2, U32>, +path: List<&2, U32>, kr: S & U32) -> SrN:
  (s, +w) = kr
  sr.arg(is.pair(w), s, r0, vis, path, w, rest)

def sr.step(st: List<&2, SrI>, s: S, +r0: U32) -> SrN:
  match st:
    case Nil{}:
      SrNo{s}
    case Con{it, rest}:
      match it:
        case SrTy{+vis, +path, +t}:
          sr.step.k1(r0, rest, vis, path, walk(s, t))
        case SrArg{+vis, +path, +t}:
          sr.step.k2(r0, rest, vis, path, walk(s, t))

def sr.fin(n: SrN) -> S & Maybe<&2, List<&2, U32>>:
  match n:
    case SrGo{s, r0, st}:
      (s, None{})
    case SrFound{s, path}:
      (s, Some{path})
    case SrNo{s}:
      (s, None{})

def sr.loop(fuel: Nat, n: SrN) -> S & Maybe<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      sr.fin(n)
    case 1n+f:
      match n:
        case SrGo{s, +r0, st}:
          sr.loop(f, sr.step(st, s, r0))
        case SrFound{s, path}:
          (s, Some{path})
        case SrNo{s}:
          (s, None{})

# selfReferential: the cycle, as the tags whose interfaces it threads.
def sr.run(s: S, +r0: U32) -> S & Maybe<&2, List<&2, U32>>:
  sr.loop(big(), sr.class(s, r0, r0, [], [], []))

def tag.name.code(r: S & Bd) -> S & String:
  (s, b) = r
  (s, Co.fi.show(bd.fi(b)))

def tag.name.at(gate: Bool, gatefn: Bool, s: S, +tag: U32) -> S & String:
  match gate:
    case True{}:
      (s, "TGate")
    case False{}:
      match gatefn:
        case True{}:
          (s, "TGateFn")
        case False{}:
          tag.name.code(bd.of(s, tag))

def tag.name.acc.k1(acc: List<&2, String>, kr: S & String) -> S & List<&2, String>:
  (s, +a) = kr
  (s, a <> acc)

def tag.name.acc(s: S, acc: List<&2, String>, +x: U32) -> S & List<&2, String>:
  tag.name.acc.k1(acc, tag.name.at(U32.is_eq(x, tag.gate()), U32.is_eq(x, tag.gatefn()), s, x))

def tag.names(xs: List<&2, U32>, r: S & List<&2, String>) -> S & List<&2, String>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, acc) = r
      tag.names(rest, tag.name.acc(s, acc, x))

def te.tag(e: TE) -> U32:
  match e:
    case TE{+tag, cap, ifc}:
      tag

def te.head.is(es: List<&2, TE>, +tag: U32) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, rest}:
      U32.is_eq(te.tag(e), tag)

def te.find.go(es: List<&2, TE>, +tag: U32, hit: Bool) -> Maybe<&2, TE>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, +rest}:
      match hit:
        case True{}:
          Some{e}
        case False{}:
          te.find.go(rest, tag, te.head.is(rest, tag))

# Map.lookup on a class's tags.
def te.find(+es: List<&2, TE>, +tag: U32) -> Maybe<&2, TE>:
  te.find.go(es, tag, te.head.is(es, tag))

def te.heads(xs: List<&2, TE>, ys: List<&2, TE>) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      match ys:
        case Nil{}:
          LT{}
        case Con{y, yr}:
          U32.cmp(te.tag(x), te.tag(y))

# mergeTagInfo: the gaps of one record filled from the other.
def te.merge(a: TE, b: TE) -> TE:
  match a:
    case TE{+tag, ca, ia}:
      match b:
        case TE{tb, cb, ib}:
          TE{tag, Maybe.or(&2, Sg, ca, cb), Maybe.or(&2, If, ia, ib)}

# Map.unionWith mergeTagInfo
def te.union.go(fuel: Nat, +xs: List<&2, TE>, +ys: List<&2, TE>, c: Cmp) -> List<&2, TE>:
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
                  x <> te.union.go(f, xr, Con{y, yr}, te.heads(xr, Con{y, yr}))
                case GT{}:
                  y <> te.union.go(f, Con{x, xr}, yr, te.heads(Con{x, xr}, yr))
                case EQ{}:
                  te.merge(x, y) <> te.union.go(f, xr, yr, te.heads(xr, yr))

def te.union(+xs: List<&2, TE>, +ys: List<&2, TE>) -> List<&2, TE>:
  te.union.go(big(), xs, ys, te.heads(xs, ys))

def te.pend.at(m: Maybe<&2, TE>, +loc: Lc.Loc, +x: TE, rest: List<&2, W>) -> List<&2, W>:
  match m:
    case Some{y}:
      WInfo{loc, x, y} <> rest
    case None{}:
      rest

# The records of the tags on both sides, in the first's order.
def te.pending(xs: List<&2, TE>, +ys: List<&2, TE>, +loc: Lc.Loc, +tail: List<&2, W>) -> List<&2, W>:
  match xs:
    case Nil{}:
      tail
    case Con{+x, rest}:
      te.pend.at(te.find(ys, te.tag(x)), loc, x, te.pending(rest, ys, loc, tail))

# unionTags
def ut.at.k2(+loc: Lc.Loc, +ra: U32, +rb: U32, rest: List<&2, W>, +ma: List<&2, TE>, kr: S & List<&2, TE>) -> UN:
  (s, +mb) = kr
  s2 = s.ts.set(s.ts.set(s.tp.set(s, ra, (rb + 1 : U32)), rb, te.union(ma, mb)), ra, [])
  UnGo{s2, te.pending(ma, mb, loc, WSelf{loc, rb} <> rest)}

def ut.at.k1(+loc: Lc.Loc, +ra: U32, +rb: U32, rest: List<&2, W>, kr: S & List<&2, TE>) -> UN:
  (s, +ma) = kr
  ut.at.k2(loc, ra, rb, rest, ma, s.ts(s, rb))

def ut.at(same: Bool, s: S, +loc: Lc.Loc, +ra: U32, +rb: U32, rest: List<&2, W>) -> UN:
  match same:
    case True{}:
      UnGo{s, rest}
    case False{}:
      ut.at.k1(loc, ra, rb, rest, s.ts(s, ra))

def ut.k2(+loc: Lc.Loc, rest: List<&2, W>, +ra: U32, kr: S & U32) -> UN:
  (s, +rb) = kr
  ut.at(U32.is_eq(ra, rb), s, loc, ra, rb, rest)

def ut.k1(+loc: Lc.Loc, +b: U32, rest: List<&2, W>, kr: S & U32) -> UN:
  (s, +ra) = kr
  ut.k2(loc, rest, ra, find.t(s, b))

def ut(s: S, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  ut.k1(loc, b, rest, find.t(s, a))

# The capture jobs of every capture a package holds, in tag order.
def rc.all(es: List<&2, TE>, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>) -> List<&2, W>:
  match es:
    case Nil{}:
      rest
    case Con{e, er}:
      match e:
        case TE{tag, cap, ifc}:
          match cap:
            case Some{c}:
              match c:
                case Sg{cb, +ct}:
                  WTau{vis, mode, loc, ct, t} <> rc.all(er, vis, mode, loc, t, rest)
            case None{}:
              rc.all(er, vis, mode, loc, t, rest)

def rc.sel(m: Maybe<&2, TE>, +es: List<&2, TE>, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>) -> List<&2, W>:
  match m:
    case Some{e}:
      match e:
        case TE{tag, cap, ifc}:
          match cap:
            case Some{c}:
              match c:
                case Sg{cb, +ct}:
                  WTau{vis, mode, loc, ct, t} <> rest
            case None{}:
              rc.all(es, vis, mode, loc, t, rest)
    case None{}:
      rc.all(es, vis, mode, loc, t, rest)

def rc.at.k1(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +r: U32, +t: U32, rest: List<&2, W>, kr: S & List<&2, TE>) -> UN:
  (s, +es) = kr
  UnGo{s, rc.sel(te.find(es, mode), es, r <> vis, mode, loc, t, rest)}

def rc.at(seen: Bool, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +r: U32, +t: U32, rest: List<&2, W>) -> UN:
  match seen:
    case True{}:
      UnGo{s, rest}
    case False{}:
      rc.at.k1(vis, mode, loc, r, t, rest, s.ts(s, r))

# resolveCapT
def rc.k1(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +t: U32, rest: List<&2, W>, kr: S & U32) -> UN:
  (s, +r) = kr
  rc.at(u.has(vis, r), s, vis, mode, loc, r, t, rest)

def rc(s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>) -> UN:
  rc.k1(vis, mode, loc, t, rest, find.t(s, i))

def self.jobs(cs: List<&2, U32>, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  match cs:
    case Nil{}:
      rest
    case Con{+c, cr}:
      WSelf{loc, c} <> self.jobs(cr, loc, rest)

def bind.at.k1(+loc: Lc.Loc, rest: List<&2, W>, kr: S & List<&2, U32>) -> UN:
  (s, cs) = kr
  UnGo{s, self.jobs(cs, loc, rest)}

def bind.at(cyclic: Bool, s: S, +loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>) -> UN:
  match cyclic:
    case True{}:
      UnGo{s.tb.set(s, i, ty.data()), WTau{[], none(), loc, t, ty.data()} <> rest}
    case False{}:
      bind.at.k1(loc, rest, exposed(s.tb.set(s, i, t), t))

# bindTVar
def bind.k1(+loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>, kr: S & Bool) -> UN:
  (s, +cyc) = kr
  bind.at(cyc, s, loc, i, t, rest)

def bind(s: S, +loc: Lc.Loc, +i: U32, +t: U32, rest: List<&2, W>) -> UN:
  bind.k1(loc, i, t, rest, occurs(s, i, t))

def mode.show.at.k1(+mode: U32, kr: S & String) -> S & String:
  (s, +t) = kr
  (s, "Just " ++ Bool.pick(String, U32.is_lt(mode, tag.gate()), "(" ++ t ++ ")", t))

def mode.show.at(nothing: Bool, s: S, +mode: U32) -> S & String:
  match nothing:
    case True{}:
      (s, "Nothing")
    case False{}:
      mode.show.at.k1(mode, tag.show(s, mode))

# The mismatch error.
def un.bad.k3(+loc: Lc.Loc, +a: U32, +b: U32, +da: String, +db: String, kr: S & String) -> UN:
  (s, +ms) = kr
  UnDone{fail(s, TypeMismatch{loc, describe(a) ++ " vs " ++ describe(b) ++ " [mode " ++ ms ++ "; " ++ da ++ " ||| " ++ db ++ "]"})}

def un.bad.k2(+mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, +da: String, kr: S & String) -> UN:
  (s, +db) = kr
  un.bad.k3(loc, a, b, da, db, mode.show.at(U32.is_eq(mode, none()), s, mode))

def un.bad.k1(+mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, kr: S & String) -> UN:
  (s, +da) = kr
  un.bad.k2(mode, loc, a, b, da, ds.five(s, b))

def un.bad(s: S, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32) -> UN:
  un.bad.k1(mode, loc, a, b, ds.five(s, a))

def un.collapse(ps: PS, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, rest: List<&2, W>) -> UN:
  match ps:
    case PS{a, b}:
      match a:
        case Sg{ab, +at}:
          match b:
            case Sg{bb, +bt}:
              UnGo{s, WTau{vis, mode, loc, at, ty.data()} <> (WTau{vis, mode, loc, bt, ty.data()} <> rest)}

def un.pairs(pa: PS, pb: PS, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, rest: List<&2, W>) -> UN:
  match pa:
    case PS{a1, a2}:
      match pb:
        case PS{b1, b2}:
          UnGo{s, WSig{vis, mode, loc, a1, b1} <> (WSig{vis, mode, loc, a2, b2} <> rest)}

def un.var.same(same: Bool, s: S, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  match same:
    case True{}:
      UnGo{s, rest}
    case False{}:
      bind(s, loc, ty.of(a), b, rest)

def un.var.l(kb: K, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  match kb:
    case KAbort{}:
      UnGo{s, rest}
    case KVar{}:
      un.var.same(U32.is_eq(a, b), s, loc, a, b, rest)
    case other:
      bind(s, loc, ty.of(a), b, rest)

def un.data.l.k1(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, rest: List<&2, W>, kr: S & PS) -> UN:
  (s, ps) = kr
  un.collapse(ps, s, vis, mode, loc, rest)

def un.data.l(kb: K, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  match kb:
    case KAbort{}:
      UnGo{s, rest}
    case KVar{}:
      bind(s, loc, ty.of(b), a, rest)
    case KData{}:
      UnGo{s, rest}
    case KCap{}:
      rc(s, vis, mode, loc, ty.of(b), a, rest)
    case KPair{}:
      un.data.l.k1(vis, mode, loc, rest, pair.get(s, b))
    case KCode{}:
      un.bad(s, mode, loc, a, b)

def un.code.l(kb: K, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  match kb:
    case KAbort{}:
      UnGo{s, rest}
    case KVar{}:
      bind(s, loc, ty.of(b), a, rest)
    case KCode{}:
      ut(s, loc, ty.of(a), ty.of(b), rest)
    case KCap{}:
      rc(s, vis, mode, loc, ty.of(b), a, rest)
    case other:
      un.bad(s, mode, loc, a, b)

def un.cap.l(kb: K, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  match kb:
    case KAbort{}:
      UnGo{s, rest}
    case KVar{}:
      bind(s, loc, ty.of(b), a, rest)
    case KCap{}:
      ut(s, loc, ty.of(a), ty.of(b), rest)
    case other:
      rc(s, vis, mode, loc, ty.of(a), b, rest)

def un.pair.l.k2(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, rest: List<&2, W>, pa: PS, kr: S & PS) -> UN:
  (s, pb) = kr
  un.pairs(pa, pb, s, vis, mode, loc, rest)

def un.pair.l.k1(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +b: U32, rest: List<&2, W>, kr: S & PS) -> UN:
  (s, pa) = kr
  un.pair.l.k2(vis, mode, loc, rest, pa, pair.get(s, b))

def un.pair.l.k3(+vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, rest: List<&2, W>, kr: S & PS) -> UN:
  (s, ps) = kr
  un.collapse(ps, s, vis, mode, loc, rest)

def un.pair.l(kb: K, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  match kb:
    case KAbort{}:
      UnGo{s, rest}
    case KVar{}:
      bind(s, loc, ty.of(b), a, rest)
    case KPair{}:
      un.pair.l.k1(vis, mode, loc, b, rest, pair.get(s, a))
    case KData{}:
      un.pair.l.k3(vis, mode, loc, rest, pair.get(s, a))
    case KCap{}:
      rc(s, vis, mode, loc, ty.of(b), a, rest)
    case KCode{}:
      un.bad(s, mode, loc, a, b)

# unifyTauAt, on two walked types.
def un.tau(ka: K, kb: K, s: S, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +a: U32, +b: U32, rest: List<&2, W>) -> UN:
  match ka:
    case KAbort{}:
      UnGo{s, rest}
    case KVar{}:
      un.var.l(kb, s, vis, mode, loc, a, b, rest)
    case KData{}:
      un.data.l(kb, s, vis, mode, loc, a, b, rest)
    case KCode{}:
      un.code.l(kb, s, vis, mode, loc, a, b, rest)
    case KCap{}:
      un.cap.l(kb, s, vis, mode, loc, a, b, rest)
    case KPair{}:
      un.pair.l(kb, s, vis, mode, loc, a, b, rest)

def info.cap(ca: Maybe<&2, Sg>, cb: Maybe<&2, Sg>, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  match ca:
    case Some{x}:
      match cb:
        case Some{y}:
          WSig{[], none(), loc, x, y} <> rest
        case None{}:
          rest
    case None{}:
      rest

def info.if(ia: Maybe<&2, If>, ib: Maybe<&2, If>, +loc: Lc.Loc, rest: List<&2, W>) -> List<&2, W>:
  match ia:
    case Some{x}:
      match x:
        case If{ea, ra, da}:
          match ib:
            case Some{y}:
              match y:
                case If{eb, rb, db}:
                  WSig{[], none(), loc, ea, eb} <> (WSig{[], none(), loc, ra, rb} <> (WBangs{da, db} <> rest))
            case None{}:
              rest
    case None{}:
      rest

# unifyTagInfo: captures, then interfaces (env, result, doors).
def un.info(a: TE, b: TE, s: S, +loc: Lc.Loc, rest: List<&2, W>) -> UN:
  match a:
    case TE{ta, ca, ia}:
      match b:
        case TE{tb, cb, ib}:
          UnGo{s, info.cap(ca, cb, loc, info.if(ia, ib, loc, rest))}

def un.self.k1(+loc: Lc.Loc, kr: S & List<&2, String>) -> UN:
  (s, names) = kr
  UnDone{fail(s, TypeMismatch{loc, "self-application: a function is applied to a value that contains the"
    ++ " function itself, so its argument would have to contain its own interface (cycle through "
    ++ String.join(List.reverse(&2, String, names), " ") ++ ")"})}

def un.self(m: Maybe<&2, List<&2, U32>>, s: S, +loc: Lc.Loc, rest: List<&2, W>) -> UN:
  match m:
    case None{}:
      UnGo{s, rest}
    case Some{path}:
      un.self.k1(loc, tag.names(path, (s, [])))

def un.job.k2(rest: List<&2, W>, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +wa: U32, kr: S & U32) -> UN:
  (s, +wb) = kr
  un.tau(kind(wa), kind(wb), s, vis, mode, loc, wa, wb, rest)

def un.job.k1(rest: List<&2, W>, +vis: List<&2, U32>, +mode: U32, +loc: Lc.Loc, +b: U32, kr: S & U32) -> UN:
  (s, +wa) = kr
  un.job.k2(rest, vis, mode, loc, wa, walk(s, b))

def un.job.k3(rest: List<&2, W>, +loc: Lc.Loc, kr: S & Maybe<&2, List<&2, U32>>) -> UN:
  (s, m) = kr
  un.self(m, s, loc, rest)

def un.job(j: W, s: S, rest: List<&2, W>) -> UN:
  match j:
    case WSig{+vis, +mode, +loc, a, b}:
      match a:
        case Sg{+ab, +at}:
          match b:
            case Sg{+bb, +bt}:
              UnGo{union.b(s, ab, bb), WTau{vis, mode, loc, at, bt} <> rest}
    case WTau{+vis, +mode, +loc, +a, +b}:
      un.job.k1(rest, vis, mode, loc, b, walk(s, a))
    case WInfo{+loc, a, b}:
      un.info(a, b, s, loc, rest)
    case WBangs{xs, ys}:
      UnGo{union.bs(xs, ys, s), rest}
    case WSelf{+loc, +c}:
      un.job.k3(rest, loc, sr.run(s, c))

def un.step.at(bad: Bool, s: S, js: List<&2, W>) -> UN:
  match bad:
    case True{}:
      UnDone{s}
    case False{}:
      match js:
        case Nil{}:
          UnDone{s}
        case Con{j, rest}:
          un.job(j, s, rest)

def un.step.k1(js: List<&2, W>, kr: S & Bool) -> UN:
  (s, +bad) = kr
  un.step.at(bad, s, js)

def un.step(s: S, js: List<&2, W>) -> UN:
  un.step.k1(js, failed(s))

def un.fin(n: UN) -> S:
  match n:
    case UnGo{s, js}:
      fail(s, Internal{"the unifier ran out of fuel"})
    case UnDone{s}:
      s

def un.loop(fuel: Nat, n: UN) -> S:
  match fuel:
    case 0n:
      un.fin(n)
    case 1n+f:
      match n:
        case UnGo{s, js}:
          un.loop(f, un.step(s, js))
        case UnDone{s}:
          s

def un.run(s: S, js: List<&2, W>) -> S:
  un.loop(big(), un.step(s, js))

# unifySigmaAt with a dispatch's tag (none() for none).
def unify.sig.at(s: S, +mode: U32, +loc: Lc.Loc, +a: Sg, +b: Sg) -> S:
  un.run(s, [WSig{[], mode, loc, a, b}])

# unifySigma
def unify.sig(s: S, +loc: Lc.Loc, +a: Sg, +b: Sg) -> S:
  un.run(s, [WSig{[], none(), loc, a, b}])

# unifyTau
def unify.tau(s: S, +loc: Lc.Loc, +a: U32, +b: U32) -> S:
  un.run(s, [WTau{[], none(), loc, a, b}])

# unifyTagInfo
def unify.info(s: S, +loc: Lc.Loc, +a: TE, +b: TE) -> S:
  un.run(s, [WInfo{loc, a, b}])

def use.path(u: Use) -> List<&2, U32>:
  match u:
    case Use{+path, n, loc}:
      path

def us.bump(u: Use) -> Use:
  match u:
    case Use{+up, +un, +ul}:
      Use{up, (un + 1 : U32), ul}

def us.cmp(+p: List<&2, U32>, xs: List<&2, Use>) -> Cmp:
  match xs:
    case Nil{}:
      LT{}
    case Con{u, rest}:
      steps.cmp(p, use.path(u))

# One more use at a path (the first use's place stays).
def us.add(xs: List<&2, Use>, +p: List<&2, U32>, +loc: Lc.Loc, c: Cmp) -> List<&2, Use>:
  match xs:
    case Nil{}:
      [Use{p, 1, loc}]
    case Con{+u, +rest}:
      match c:
        case LT{}:
          Use{p, 1, loc} <> Con{u, rest}
        case EQ{}:
          us.bump(u) <> rest
        case GT{}:
          u <> us.add(rest, p, loc, us.cmp(p, rest))

def use.at(+p: List<&2, U32>, +loc: Lc.Loc, +acc: List<&2, Use>) -> List<&2, Use>:
  us.add(acc, p, loc, us.cmp(p, acc))

# envUsageL: the body's env uses by projection path. A reference is closed;
# an abort's message is not counted.
def usage(t: A, +proj: List<&2, U32>, +acc: List<&2, Use>) -> List<&2, Use>:
  match t:
    case ALeft{loc, x}:
      usage(x, 0 <> proj, acc)
    case ARight{loc, x}:
      usage(x, 1 <> proj, acc)
    case AEnv{+loc}:
      use.at(proj, loc, acc)
    case AUns{+loc}:
      use.at(proj, loc, acc)
    case ACheck{loc, c}:
      usage(c, proj, acc)
    case APair{loc, a, b}:
      usage(b, [], usage(a, [], acc))
    case ASetEnv{loc, x}:
      usage(x, [], acc)
    case other:
      acc

def steps.eq.at(c: Cmp) -> Bool:
  match c:
    case EQ{}:
      True{}
    case other:
      False{}

def steps.eq(+p: List<&2, U32>, +q: List<&2, U32>) -> Bool:
  steps.eq.at(steps.cmp(p, q))

def sub.used(us: List<&2, Use>, +p: List<&2, U32>) -> Bool:
  match us:
    case Nil{}:
      False{}
    case Con{u, rest}:
      match u:
        case Use{+q, n, loc}:
          Bool.or(Bool.and(steps.prefix(p, q), Bool.not(steps.eq(p, q))), sub.used(rest, p))

def site.at(bad: Bool, +p: List<&2, U32>, +loc: Lc.Loc, rest: List<&2, Site>) -> List<&2, Site>:
  match bad:
    case True{}:
      Site{p, loc} <> rest
    case False{}:
      rest

# contractionSites
def sites(us: List<&2, Use>, +all: List<&2, Use>) -> List<&2, Site>:
  match us:
    case Nil{}:
      []
    case Con{u, rest}:
      match u:
        case Use{+p, +n, +loc}:
          site.at(Bool.or(U32.is_ge(n, 2), Bool.and(U32.is_ge(n, 1), sub.used(all, p))), p, loc, sites(rest, all))

def sg.b(x: Sg) -> U32:
  match x:
    case Sg{+b, t}:
      b

def sg.t(x: Sg) -> U32:
  match x:
    case Sg{b, +t}:
      t

def ctx.unit(c: Ctx) -> U32:
  match c:
    case Ctx{bang, tau, +unit, doorl, idx, doors}:
      unit

def ctx.idx(c: Ctx) -> U32:
  match c:
    case Ctx{bang, tau, unit, doorl, +idx, doors}:
      idx

def ctx.doorl(c: Ctx) -> List<&2, U32>:
  match c:
    case Ctx{bang, tau, unit, +doorl, idx, doors}:
      doorl

def pa.d(p: Pa) -> U32:
  match p:
    case Pa{+par, base}:
      (par - 1 : U32)

def pa.base(p: Pa) -> U32:
  match p:
    case Pa{par, +base}:
      base

def ec.step.k3(+loc: Lc.Loc, +st: U32, +bangs: List<&2, U32>, +ct: U32, +sl: Sg, +sr: Sg, kr: S & U32) -> S & EC:
  (s, +pt) = kr
  +nx: Sg = Bool.pick(Sg, U32.is_eq(st, 0), sl, sr)
  (unify.tau(s, loc, ct, pt), EC{sg.b(nx) <> bangs, nx})

def ec.step.k2(+loc: Lc.Loc, +st: U32, +bangs: List<&2, U32>, +ct: U32, +sl: Sg, kr: S & Sg) -> S & EC:
  (s, +sr) = kr
  ec.step.k3(loc, st, bangs, ct, sl, sr, pair.new(s, sl, sr))

def ec.step.k1(+loc: Lc.Loc, +st: U32, +bangs: List<&2, U32>, +ct: U32, kr: S & Sg) -> S & EC:
  (s, +sl) = kr
  ec.step.k2(loc, st, bangs, ct, sl, fresh.sig(s))

def ec.step(s: S, +loc: Lc.Loc, +st: U32, acc: EC) -> S & EC:
  match acc:
    case EC{+bangs, cur}:
      match cur:
        case Sg{cb, +ct}:
          ec.step.k1(loc, st, bangs, ct, fresh.sig(s))

def ec.go(steps: List<&2, U32>, r: S & EC, +loc: Lc.Loc) -> S & EC:
  match steps:
    case Nil{}:
      r
    case Con{+st, rest}:
      (s, acc) = r
      ec.go(rest, ec.step(s, loc, st, acc), loc)

# envComponent: the env refined into pairs along a path.
def env.component(s: S, +loc: Lc.Loc, c: Ctx, +steps: List<&2, U32>) -> S & EC:
  match c:
    case Ctx{+bang, +tau, unit, doorl, idx, doors}:
      ec.go(steps, (s, EC{[], Sg{bang, tau}}), loc)

def starts.r(p: List<&2, U32>) -> Bool:
  match p:
    case Nil{}:
      False{}
    case Con{+x, rest}:
      U32.is_eq(x, 1)

def fc.door.k3(+unit: U32, +path: List<&2, U32>, +uloc: Lc.Loc, +bq: U32, +acc: List<&2, Door>, +door: U32, +inner: U32, kr: S & U32) -> S & List<&2, Door>:
  (s, +rest) = kr
  (add.eq(add.eq(s, blame(uloc, "a duplicated capture's bang = door + what the body opens"), [door, inner], bq),
    blame(uloc, "at most one door per duplicated capture"), [door, rest], unit), Door{path, door, inner} <> acc)

def fc.door.k2(+unit: U32, +path: List<&2, U32>, +uloc: Lc.Loc, +bq: U32, +acc: List<&2, Door>, +door: U32, kr: S & U32) -> S & List<&2, Door>:
  (s, +inner) = kr
  fc.door.k3(unit, path, uloc, bq, acc, door, inner, fresh(s))

def fc.door.k1(+unit: U32, +path: List<&2, U32>, +uloc: Lc.Loc, +bq: U32, +acc: List<&2, Door>, kr: S & U32) -> S & List<&2, Door>:
  (s, +door) = kr
  fc.door.k2(unit, path, uloc, bq, acc, door, fresh(s))

def fc.door(isr: Bool, s: S, +unit: U32, +path: List<&2, U32>, +uloc: Lc.Loc, +bq: U32, +acc: List<&2, Door>) -> S & List<&2, Door>:
  match isr:
    case False{}:
      (s, acc)
    case True{}:
      fc.door.k1(unit, path, uloc, bq, acc, fresh(s))

def fc.k(ec: EC, s: S, +unit: U32, +what: String, +path: List<&2, U32>, +uloc: Lc.Loc, +acc: List<&2, Door>) -> S & List<&2, Door>:
  match ec:
    case EC{bangs, cur}:
      match cur:
        case Sg{+bq, ct}:
          fc.door(starts.r(path), constrain_(s, bq, CLevel{1, blame(uloc, what ++ " path " ++ steps.show(path) ++ " duplicated")}),
            unit, path, uloc, bq, acc)

def fc.step.k1(+unit: U32, +what: String, +acc: List<&2, Door>, +path: List<&2, U32>, +uloc: Lc.Loc, kr: S & EC) -> S & List<&2, Door>:
  (s, ec) = kr
  fc.k(ec, s, unit, what, path, uloc, acc)

def fc.step(s: S, +unit: U32, +what: String, +c0: Ctx, site: Site, +acc: List<&2, Door>) -> S & List<&2, Door>:
  match site:
    case Site{+path, +uloc}:
      fc.step.k1(unit, what, acc, path, uloc, env.component(s, uloc, c0, path))

def fc.go(ss: List<&2, Site>, r: S & List<&2, Door>, +unit: U32, +what: String, +c0: Ctx) -> S & List<&2, Door>:
  match ss:
    case Nil{}:
      r
    case Con{site, rest}:
      (s, +acc) = r
      fc.go(rest, fc.step(s, unit, what, c0, site, acc), unit, what, c0)

def doors.list(ds: List<&2, Door>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      []
    case Con{d, rest}:
      match d:
        case Door{path, +door, inner}:
          door <> doors.list(rest)

def doors.kd(ds: List<&2, Door>) -> List<&2, KD>:
  match ds:
    case Nil{}:
      []
    case Con{d, rest}:
      match d:
        case Door{+path, door, +inner}:
          KD{path, inner} <> doors.kd(rest)

# frameContext
def frame.context.k1(+unit: U32, +idx: U32, +benv: U32, +tenv: U32, kr: S & List<&2, Door>) -> S & Ctx:
  (s, +ds) = kr
  (s, Ctx{benv, tenv, unit, doors.list(List.reverse(&2, Door, ds)), idx, doors.kd(List.reverse(&2, Door, ds))})

def frame.context(s: S, +unit: U32, +idx: U32, +what: String, +benv: U32, +tenv: U32, body: A) -> S & Ctx:
  +us: List<&2, Use> = usage(body, [], [])
  frame.context.k1(unit, idx, benv, tenv, fc.go(sites(us, us), (s, []), unit, what, Ctx{benv, tenv, unit, [], idx, []}))

# Occurrences
# -----------

def leaf(s: S, +c: Ctx, +p: Pa) -> S:
  rec.leaf(s, ctx.idx(c), pa.base(p), pa.d(p))

def kd.pick(hit: Bool, +inner: U32, m: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match hit:
    case True{}:
      Some{inner}
    case False{}:
      m

def kd.find(ks: List<&2, KD>, +p: List<&2, U32>) -> Maybe<&2, U32>:
  match ks:
    case Nil{}:
      None{}
    case Con{k, rest}:
      match k:
        case KD{+q, +inner}:
          kd.pick(steps.eq(p, q), inner, kd.find(rest, p))

def init.at(xs: List<&2, U32>, +x: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+y, rest}:
      x <> init.at(rest, y)

def init(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      init.at(rest, x)

def opened.at(m: Maybe<&2, U32>, +bang: U32, +bangs: List<&2, U32>) -> List<&2, U32>:
  match m:
    case Some{+inner}:
      bang <> List.append(&2, U32, init(bangs), [inner])
    case None{}:
      bang <> bangs

# The bangs an occurrence opens: an argument's all; a duplicated
# capture's all but the one door consumed outside the closure's box.
def opened(c: Ctx, +steps: List<&2, U32>, +bangs: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Ctx{+bang, tau, unit, doorl, idx, +doors}:
      opened.at(Bool.pick(Maybe<&2, U32>, starts.r(steps), kd.find(doors, steps), None{}), bang, bangs)

def eo.k.k1(+ct: U32, kr: S & U32) -> S & Sg:
  (s, +b) = kr
  (s, Sg{b, ct})

def eo.k(ec: EC, s: S, +c: Ctx, +p: Pa, +loc: Lc.Loc, +steps: List<&2, U32>) -> S & Sg:
  match ec:
    case EC{+rb, cur}:
      match cur:
        case Sg{cb, +ct}:
          eo.k.k1(ct, forced.zero(add.eq(s, blame(loc, "env occurrence depth = the bangs this body opens"), opened(c, steps, List.reverse(&2, U32, rb)), pa.d(p)), blame(loc, "variable occurrence is locally unboxed")))

# envOccurrence
def env.occ.k1(+c: Ctx, +p: Pa, +loc: Lc.Loc, +steps: List<&2, U32>, kr: S & EC) -> S & Sg:
  (s, ec) = kr
  eo.k(ec, s, c, p, loc, steps)

def env.occ(s: S, +c: Ctx, +p: Pa, +loc: Lc.Loc, +steps: List<&2, U32>) -> S & Sg:
  env.occ.k1(c, p, loc, steps, env.component(leaf(s, c, p), loc, c, steps))

def te.doors(es: List<&2, TE>) -> List<&2, U32>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      match e:
        case TE{tag, cap, ifc}:
          match ifc:
            case Some{x}:
              match x:
                case If{env, res, +doors}:
                  List.append(&2, U32, doors, te.doors(rest))
            case None{}:
              te.doors(rest)

def po.door.k1(+loc: Lc.Loc, +bpkg: U32, +d: U32, kr: S & U32) -> S:
  (s, +slack) = kr
  add.eq(s, blame(loc, "a door needs the closure's own box"), [d, slack], bpkg)

def po.door(s: S, +loc: Lc.Loc, +bpkg: U32, +d: U32) -> S:
  po.door.k1(loc, bpkg, d, fresh(s))

def po.doors(ds: List<&2, U32>, s: S, +loc: Lc.Loc, +bpkg: U32) -> S:
  match ds:
    case Nil{}:
      s
    case Con{+d, rest}:
      po.doors(rest, po.door(s, loc, bpkg, d), loc, bpkg)

def is.code(+t: U32) -> Bool:
  U32.is_eq((t .&. 7 : U32), 2)

def po.at.k1(+loc: Lc.Loc, kr: S & U32) -> S & Sg:
  (s, +pt) = kr
  plain(s, loc, "pair constructor is locally unboxed", pt)

def po.at.k5(+bpkg: U32, kr: S & U32) -> S & Sg:
  (s, +pt) = kr
  (s, Sg{bpkg, pt})

def po.at.k4(+loc: Lc.Loc, +sa: Sg, +sb: Sg, +p: U32, infos: List<&2, TE>, kr: S & U32) -> S & Sg:
  (s, +bpkg) = kr
  po.at.k5(bpkg, pair.new(po.doors(te.doors(infos), s, loc, bpkg), sa, Sg{sg.b(sb), ty.cap(p)}))

def po.at.k3(+loc: Lc.Loc, +sa: Sg, +sb: Sg, +p: U32, kr: S & List<&2, TE>) -> S & Sg:
  (s, infos) = kr
  po.at.k4(loc, sa, sb, p, infos, fresh(s))

def po.at.k2(+loc: Lc.Loc, +sa: Sg, +sb: Sg, +w: U32, kr: S & U32) -> S & Sg:
  (s, +p) = kr
  po.at.k3(loc, sa, sb, p, captures.of(s, ty.of(w)))

def po.at(code: Bool, s: S, +loc: Lc.Loc, +sa: Sg, +sb: Sg, +w: U32) -> S & Sg:
  match code:
    case False{}:
      po.at.k1(loc, pair.new(s, sa, sb))
    case True{}:
      po.at.k2(loc, sa, sb, w, package.class(s, ty.of(w), sb))

# pairOf: a code-headed pair is a closure package.
def pair.of.k1(+loc: Lc.Loc, +sa: Sg, +sb: Sg, kr: S & U32) -> S & Sg:
  (s, +w) = kr
  po.at(is.code(w), s, loc, sa, sb, w)

def pair.of(s: S, +loc: Lc.Loc, +sa: Sg, +sb: Sg) -> S & Sg:
  pair.of.k1(loc, sa, sb, walk(s, sg.t(sa)))

# An application's sigma (intrinsic's SetEnv), from the applied pair's.
def set.env.k10(+loc: Lc.Loc, +si: Sg, +fnt: U32, +k: U32, +ceb: U32, +so: Sg, kr: S & U32) -> S & Sg:
  (s, +outb) = kr
  (ap.new(add.eq(s, blame(loc, "result boxes = boxes entered + the callee's result boxes"), [k, sg.b(so)], outb),
    Ap{fnt, Sg{ceb, sg.t(si)}, so, loc, []}), Sg{outb, sg.t(so)})

def set.env.k9(+loc: Lc.Loc, +si: Sg, +fnt: U32, +k: U32, +ceb: U32, kr: S & Sg) -> S & Sg:
  (s, +so) = kr
  set.env.k10(loc, si, fnt, k, ceb, so, fresh(s))

def set.env.k8(+loc: Lc.Loc, +si: Sg, +fnt: U32, +k: U32, +opb: U32, kr: S & U32) -> S & Sg:
  (s, +ceb) = kr
  set.env.k9(loc, si, fnt, k, ceb, fresh.sig(add.eq(s, blame(loc, "operand boxes = boxes entered + boxes the callee sees"), [k, ceb], opb)))

def set.env.k7(+loc: Lc.Loc, +si: Sg, +fnt: U32, +pairb: U32, +k: U32, kr: S & U32) -> S & Sg:
  (s, +opb) = kr
  set.env.k8(loc, si, fnt, k, opb, fresh(add.eq(s, blame(loc, "operand boxes = applied pair boxes + its own"), [pairb, sg.b(si)], opb)))

def set.env.k6(+loc: Lc.Loc, +sx: Sg, +si: Sg, +fnt: U32, +pairb: U32, +k: U32, kr: S & U32) -> S & Sg:
  (s, +pt) = kr
  set.env.k7(loc, si, fnt, pairb, k, fresh(unify.sig(s, loc, sx, Sg{pairb, pt})))

def set.env.k5(+loc: Lc.Loc, +sx: Sg, +si: Sg, +fnt: U32, +fnb: U32, +pairb: U32, kr: S & U32) -> S & Sg:
  (s, +k) = kr
  set.env.k6(loc, sx, si, fnt, pairb, k, pair.new(add.eq(s, blame(loc, "boxes entered = boxes on the applied pair + on the function"), [pairb, fnb], k), Sg{fnb, fnt}, si))

def set.env.k4(+loc: Lc.Loc, +sx: Sg, +si: Sg, +fnt: U32, +fnb: U32, kr: S & U32) -> S & Sg:
  (s, +pairb) = kr
  set.env.k5(loc, sx, si, fnt, fnb, pairb, fresh(s))

def set.env.k3(+loc: Lc.Loc, +sx: Sg, +si: Sg, +fnt: U32, kr: S & U32) -> S & Sg:
  (s, +fnb) = kr
  set.env.k4(loc, sx, si, fnt, fnb, fresh(s))

def set.env.k2(+loc: Lc.Loc, +sx: Sg, +si: Sg, kr: S & U32) -> S & Sg:
  (s, +fnt) = kr
  set.env.k3(loc, sx, si, fnt, fresh(s))

def set.env.k1(+loc: Lc.Loc, +sx: Sg, kr: S & Sg) -> S & Sg:
  (s, +si) = kr
  set.env.k2(loc, sx, si, fresh.tau(s))

def set.env(s: S, +loc: Lc.Loc, +sx: Sg) -> S & Sg:
  set.env.k1(loc, sx, fresh.sig(s))

# projection, from the projected value's sigma.
def proj.k5(+loc: Lc.Loc, +pb: U32, +c: Sg, kr: S & U32) -> S & Sg:
  (s, +out) = kr
  (add.eq(s, blame(loc, "projected component boxes = pair boxes + its own"), [pb, sg.b(c)], out), Sg{out, sg.t(c)})

def proj.k4(+loc: Lc.Loc, +left: Bool, +sx: Sg, +sl: Sg, +sr: Sg, +pb: U32, kr: S & U32) -> S & Sg:
  (s, +pt) = kr
  +c: Sg = Bool.pick(Sg, left, sl, sr)
  proj.k5(loc, pb, c, fresh(unify.sig(s, loc, sx, Sg{pb, pt})))

def proj.k3(+loc: Lc.Loc, +left: Bool, +sx: Sg, +sl: Sg, +sr: Sg, kr: S & U32) -> S & Sg:
  (s, +pb) = kr
  proj.k4(loc, left, sx, sl, sr, pb, pair.new(s, sl, sr))

def proj.k2(+loc: Lc.Loc, +left: Bool, +sx: Sg, +sl: Sg, kr: S & Sg) -> S & Sg:
  (s, +sr) = kr
  proj.k3(loc, left, sx, sl, sr, fresh(s))

def proj.k1(+loc: Lc.Loc, +left: Bool, +sx: Sg, kr: S & Sg) -> S & Sg:
  (s, +sl) = kr
  proj.k2(loc, left, sx, sl, fresh.sig(s))

def proj(s: S, +loc: Lc.Loc, +left: Bool, +sx: Sg) -> S & Sg:
  proj.k1(loc, left, sx, fresh.sig(s))

def data.leaf.k1(kr: S & U32) -> S & Sg:
  (s, +b) = kr
  (s, Sg{b, ty.data()})

def data.leaf(s: S) -> S & Sg:
  data.leaf.k1(fresh(s))

# bottomSigma
def bottom.k1(kr: S & U32) -> S & Sg:
  (s, +b) = kr
  (s, Sg{b, ty.abort()})

def bottom(s: S) -> S & Sg:
  bottom.k1(fresh(s))

def snap.k6(+v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, kr: S & U32) -> S & Snap:
  (s, +df0) = kr
  (s, Snap{v0, p0, a0, eq0, lf0, df0})

def snap.k5(+v0: U32, +p0: U32, +a0: U32, +eq0: U32, kr: S & U32) -> S & Snap:
  (s, +lf0) = kr
  snap.k6(v0, p0, a0, eq0, lf0, s.ndf(s))

def snap.k4(+v0: U32, +p0: U32, +a0: U32, kr: S & U32) -> S & Snap:
  (s, +eq0) = kr
  snap.k5(v0, p0, a0, eq0, s.nlf(s))

def snap.k3(+v0: U32, +p0: U32, kr: S & U32) -> S & Snap:
  (s, +a0) = kr
  snap.k4(v0, p0, a0, s.neq(s))

def snap.k2(+v0: U32, kr: S & U32) -> S & Snap:
  (s, +p0) = kr
  snap.k3(v0, p0, s.na(s))

def snap.k1(kr: S & U32) -> S & Snap:
  (s, +v0) = kr
  snap.k2(v0, s.np(s))

def snap(s: S) -> S & Snap:
  snap.k1(s.nv(s))

def keep.kv(nz: Bool, +k: U32, +v: U32, +acc: List<&2, KV>) -> List<&2, KV>:
  match nz:
    case True{}:
      KV{k, v} <> acc
    case False{}:
      acc

def keep.kc(c: CI, +k: U32, +acc: List<&2, KC>) -> List<&2, KC>:
  match c:
    case CUnr{}:
      acc
    case other:
      KC{k, other} <> acc

def keep.kt(es: List<&2, TE>, +k: U32, +acc: List<&2, KT>) -> List<&2, KT>:
  match es:
    case Nil{}:
      acc
    case Con{e, rest}:
      KT{k, Con{e, rest}} <> acc

def nxt(+i: U32, +last: U32) -> U32:
  Bool.pick(U32, U32.is_ge(i, last), i, (i + 1 : U32))

def rd.tb(n: Nat, r: S & U32, +i: U32, +last: U32, +acc: List<&2, KV>) -> S & List<&2, KV>:
  match n:
    case 0n:
      (s, x) = r
      (s, acc)
    case 1n+k:
      (s, +x) = r
      rd.tb(k, s.tb(s, nxt(i, last)), nxt(i, last), last, keep.kv(U32.is_ne(x, 0), i, x, acc))

def rd.bp(n: Nat, r: S & U32, +i: U32, +last: U32, +acc: List<&2, KV>) -> S & List<&2, KV>:
  match n:
    case 0n:
      (s, x) = r
      (s, acc)
    case 1n+k:
      (s, +x) = r
      rd.bp(k, s.bp(s, nxt(i, last)), nxt(i, last), last, keep.kv(U32.is_ne(x, 0), i, x, acc))

def rd.tp(n: Nat, r: S & U32, +i: U32, +last: U32, +acc: List<&2, KV>) -> S & List<&2, KV>:
  match n:
    case 0n:
      (s, x) = r
      (s, acc)
    case 1n+k:
      (s, +x) = r
      rd.tp(k, s.tp(s, nxt(i, last)), nxt(i, last), last, keep.kv(U32.is_ne(x, 0), i, x, acc))

def rd.ci(n: Nat, r: S & CI, +i: U32, +last: U32, +acc: List<&2, KC>) -> S & List<&2, KC>:
  match n:
    case 0n:
      (s, x) = r
      (s, acc)
    case 1n+k:
      (s, x) = r
      rd.ci(k, s.ci(s, nxt(i, last)), nxt(i, last), last, keep.kc(x, i, acc))

def rd.ts(n: Nat, r: S & List<&2, TE>, +i: U32, +last: U32, +acc: List<&2, KT>) -> S & List<&2, KT>:
  match n:
    case 0n:
      (s, x) = r
      (s, acc)
    case 1n+k:
      (s, x) = r
      rd.ts(k, s.ts(s, nxt(i, last)), nxt(i, last), last, keep.kt(x, i, acc))

def rd.pr(n: Nat, r: S & U32, +i: U32, +last: U32, +acc: List<&2, KV>) -> S & List<&2, KV>:
  match n:
    case 0n:
      (s, x) = r
      (s, acc)
    case 1n+k:
      (s, +x) = r
      rd.pr(k, s.pr(s, nxt(i, last)), nxt(i, last), last, KV{i, x} <> acc)

def rd.ap(n: Nat, r: S & Ap, +i: U32, +last: U32, +acc: List<&2, Ap>) -> S & List<&2, Ap>:
  match n:
    case 0n:
      (s, x) = r
      (s, List.reverse(&2, Ap, acc))
    case 1n+k:
      (s, +x) = r
      rd.ap(k, s.ap(s, nxt(i, last)), nxt(i, last), last, x <> acc)

def take.eq(n: Nat, xs: List<&2, SumEq>) -> List<&2, SumEq>:
  match n:
    case 0n:
      []
    case 1n+k:
      match xs:
        case Nil{}:
          []
        case Con{x, rest}:
          x <> take.eq(k, rest)

def take.df(n: Nat, xs: List<&2, Df>) -> List<&2, Df>:
  match n:
    case 0n:
      []
    case 1n+k:
      match xs:
        case Nil{}:
          []
        case Con{x, rest}:
          x <> take.df(k, rest)

# Leaves without their base, as (body, depth).
def take.lf(n: Nat, xs: List<&2, Lp>) -> List<&2, KV>:
  match n:
    case 0n:
      []
    case 1n+k:
      match xs:
        case Nil{}:
          []
        case Con{x, rest}:
          match x:
            case Lp{+fr, base, +d}:
              KV{fr, d} <> take.lf(k, rest)

def span(+a: U32, +b: U32) -> Nat:
  U32.to_nat(Bool.pick(U32, U32.is_gt(b, a), (b - a : U32), 0))

def at.or0(+i: U32, +n: U32) -> U32:
  Bool.pick(U32, U32.is_lt(i, n), i, 0)

# captureTemplate's end: the walk's deltas as the body's template.
def cap.finish.k16(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, +dfs: List<&2, Df>, +bp: List<&2, KV>, +ci: List<&2, KC>, +tb: List<&2, KV>, +tp: List<&2, KV>, +ts: List<&2, KT>, +pr: List<&2, KV>, kr: S & List<&2, Ap>) -> S & If:
  (s, +aps) = kr
  (s.tm.set(s, r, MtSome{Tm{fi, v0, (nv - v0 : U32), p0, (np - p0 : U32), bp, ci, tb, tp, ts, pr, take.eq(span(eq0, neq), eqs),
    take.lf(span(lf0, nlf), lfs), aps, take.df(span(df0, ndf), dfs), benv, tenv, sbody, doorl}}), If{Sg{benv, tenv}, sbody, doorl})

def cap.finish.k15(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, +dfs: List<&2, Df>, +bp: List<&2, KV>, +ci: List<&2, KC>, +tb: List<&2, KV>, +tp: List<&2, KV>, +ts: List<&2, KT>, kr: S & List<&2, KV>) -> S & If:
  (s, +pr) = kr
  cap.finish.k16(r, fi, benv, tenv, doorl, sbody, v0, p0, eq0, lf0, df0, nv, np, neq, nlf, ndf, eqs, lfs, dfs, bp, ci, tb, tp, ts, pr, rd.ap(span(a0, na), s.ap(s, at.or0(a0, na)), a0, (na - 1 : U32), []))

def cap.finish.k14(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, +dfs: List<&2, Df>, +bp: List<&2, KV>, +ci: List<&2, KC>, +tb: List<&2, KV>, +tp: List<&2, KV>, kr: S & List<&2, KT>) -> S & If:
  (s, +ts) = kr
  cap.finish.k15(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, lfs, dfs, bp, ci, tb, tp, ts, rd.pr(span((p0 * 4 : U32), (np * 4 : U32)), s.pr(s, at.or0((p0 * 4 : U32), (np * 4 : U32))), (p0 * 4 : U32), ((np * 4 : U32) - 1 : U32), []))

def cap.finish.k13(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, +dfs: List<&2, Df>, +bp: List<&2, KV>, +ci: List<&2, KC>, +tb: List<&2, KV>, kr: S & List<&2, KV>) -> S & If:
  (s, +tp) = kr
  cap.finish.k14(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, lfs, dfs, bp, ci, tb, tp, rd.ts(span(v0, nv), s.ts(s, at.or0(v0, nv)), v0, (nv - 1 : U32), []))

def cap.finish.k12(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, +dfs: List<&2, Df>, +bp: List<&2, KV>, +ci: List<&2, KC>, kr: S & List<&2, KV>) -> S & If:
  (s, +tb) = kr
  cap.finish.k13(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, lfs, dfs, bp, ci, tb, rd.tp(span(v0, nv), s.tp(s, at.or0(v0, nv)), v0, (nv - 1 : U32), []))

def cap.finish.k11(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, +dfs: List<&2, Df>, +bp: List<&2, KV>, kr: S & List<&2, KC>) -> S & If:
  (s, +ci) = kr
  cap.finish.k12(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, lfs, dfs, bp, ci, rd.tb(span(v0, nv), s.tb(s, at.or0(v0, nv)), v0, (nv - 1 : U32), []))

def cap.finish.k10(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, +dfs: List<&2, Df>, kr: S & List<&2, KV>) -> S & If:
  (s, +bp) = kr
  cap.finish.k11(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, lfs, dfs, bp, rd.ci(span(v0, nv), s.ci(s, at.or0(v0, nv)), v0, (nv - 1 : U32), []))

def cap.finish.k9(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, Lp>, kr: S & List<&2, Df>) -> S & If:
  (s, +dfs) = kr
  cap.finish.k10(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, lfs, dfs, rd.bp(span(v0, nv), s.bp(s, at.or0(v0, nv)), v0, (nv - 1 : U32), []))

def cap.finish.k8(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, +eqs: List<&2, SumEq>, kr: S & List<&2, Lp>) -> S & If:
  (s, +lfs) = kr
  cap.finish.k9(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, lfs, s.dfs(s))

def cap.finish.k7(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, +ndf: U32, kr: S & List<&2, SumEq>) -> S & If:
  (s, +eqs) = kr
  cap.finish.k8(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, eqs, s.lfs(s))

def cap.finish.k6(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, +nlf: U32, kr: S & U32) -> S & If:
  (s, +ndf) = kr
  cap.finish.k7(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, ndf, s.eqs(s))

def cap.finish.k5(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, +neq: U32, kr: S & U32) -> S & If:
  (s, +nlf) = kr
  cap.finish.k6(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, nlf, s.ndf(s))

def cap.finish.k4(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, +na: U32, kr: S & U32) -> S & If:
  (s, +neq) = kr
  cap.finish.k5(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, neq, s.nlf(s))

def cap.finish.k3(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, +np: U32, kr: S & U32) -> S & If:
  (s, +na) = kr
  cap.finish.k4(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, na, s.neq(s))

def cap.finish.k2(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, +nv: U32, kr: S & U32) -> S & If:
  (s, +np) = kr
  cap.finish.k3(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, np, s.na(s))

def cap.finish.k1(+r: U32, +fi: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg, +v0: U32, +p0: U32, +a0: U32, +eq0: U32, +lf0: U32, +df0: U32, kr: S & U32) -> S & If:
  (s, +nv) = kr
  cap.finish.k2(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, nv, s.np(s))

def cap.finish(s: S, +r: U32, +fi: U32, +z: Snap, +frame0: U32, +benv: U32, +tenv: U32, +doorl: List<&2, U32>, +sbody: Sg) -> S & If:
  match z:
    case Snap{+v0, +p0, +a0, +eq0, +lf0, +df0}:
      cap.finish.k1(r, fi, benv, tenv, doorl, sbody, v0, p0, a0, eq0, lf0, df0, s.nv(s.frame.set(s, frame0)))

def sh.v(+i: U32, z: Sh) -> U32:
  match z:
    case Sh{+v0, +sh, p0, psh}:
      Bool.pick(U32, U32.is_ge(i, v0), (i + sh : U32), i)

def sh.p(+p: U32, z: Sh) -> U32:
  match z:
    case Sh{v0, sh, +p0, +psh}:
      Bool.pick(U32, U32.is_ge(p, p0), (p + psh : U32), p)

def sh.psh(z: Sh) -> U32:
  match z:
    case Sh{v0, sh, p0, +psh}:
      psh

def sh.t(+t: U32, +z: Sh) -> U32:
  +k: U32 = (t .&. 7 : U32)
  +pay: U32 = (t >> 3n : U32)
  ((Bool.pick(U32, Bool.and(U32.is_ge(k, 1), U32.is_le(k, 3)), sh.v(pay, z),
    Bool.pick(U32, U32.is_eq(k, 4), sh.p(pay, z), pay)) << 3n : U32) + k : U32)

def sh.par(+w: U32, +z: Sh) -> U32:
  Bool.pick(U32, U32.is_eq(w, 0), 0, (sh.v((w - 1 : U32), z) + 1 : U32))

def sh.sg(x: Sg, +z: Sh) -> Sg:
  match x:
    case Sg{+b, +t}:
      Sg{sh.v(b, z), sh.t(t, z)}

def sh.vs(xs: List<&2, U32>, +z: Sh) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      sh.v(x, z) <> sh.vs(rest, z)

def sh.if(x: If, +z: Sh) -> If:
  match x:
    case If{env, res, doors}:
      If{sh.sg(env, z), sh.sg(res, z), sh.vs(doors, z)}

def sh.mcap(m: Maybe<&2, Sg>, +z: Sh) -> Maybe<&2, Sg>:
  match m:
    case Some{x}:
      Some{sh.sg(x, z)}
    case None{}:
      None{}

def sh.mif(m: Maybe<&2, If>, +z: Sh) -> Maybe<&2, If>:
  match m:
    case Some{x}:
      Some{sh.if(x, z)}
    case None{}:
      None{}

def sh.tes(xs: List<&2, TE>, +z: Sh) -> List<&2, TE>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case TE{+tag, cap, ifc}:
          TE{tag, sh.mcap(cap, z), sh.mif(ifc, z)} <> sh.tes(rest, z)

def sh.eqs(xs: List<&2, SumEq>, +z: Sh, +tail: List<&2, SumEq>) -> List<&2, SumEq>:
  match xs:
    case Nil{}:
      tail
    case Con{x, rest}:
      match x:
        case SumEq{lhs, +rhs, +bl}:
          SumEq{sh.vs(lhs, z), sh.v(rhs, z), bl} <> sh.eqs(rest, z, tail)

def sh.lfs(xs: List<&2, KV>, +nb: U32, +z: Sh, +tail: List<&2, Lp>) -> List<&2, Lp>:
  match xs:
    case Nil{}:
      tail
    case Con{x, rest}:
      match x:
        case KV{+fr, +d}:
          Lp{fr, nb, sh.v(d, z)} <> sh.lfs(rest, nb, z, tail)

def sh.dfs(xs: List<&2, Df>, +z: Sh, +tail: List<&2, Df>) -> List<&2, Df>:
  match xs:
    case Nil{}:
      tail
    case Con{x, rest}:
      match x:
        case Df{+fi, +b}:
          Df{fi, sh.v(b, z)} <> sh.dfs(rest, z, tail)

def w.bp(xs: List<&2, KV>, s: S, +z: Sh) -> S:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      match x:
        case KV{+k, +v}:
          w.bp(rest, s.bp.set(s, sh.v(k, z), sh.par(v, z)), z)

def w.tp(xs: List<&2, KV>, s: S, +z: Sh) -> S:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      match x:
        case KV{+k, +v}:
          w.tp(rest, s.tp.set(s, sh.v(k, z), sh.par(v, z)), z)

def w.tb(xs: List<&2, KV>, s: S, +z: Sh) -> S:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      match x:
        case KV{+k, +v}:
          w.tb(rest, s.tb.set(s, sh.v(k, z), sh.t(v, z)), z)

def w.ci(xs: List<&2, KC>, s: S, +z: Sh) -> S:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      match x:
        case KC{+k, +c}:
          w.ci(rest, s.ci.set(s, sh.v(k, z), c), z)

def w.ts(xs: List<&2, KT>, s: S, +z: Sh) -> S:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      match x:
        case KT{+k, es}:
          w.ts(rest, s.ts.set(s, sh.v(k, z), sh.tes(es, z)), z)

def w.pr(xs: List<&2, KV>, s: S, +z: Sh) -> S:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      match x:
        case KV{+k, +v}:
          w.pr(rest, s.pr.set(s, (k + (sh.psh(z) * 4 : U32) : U32),
            Bool.pick(U32, U32.is_eq((k .&. 1 : U32), 0), sh.v(v, z), sh.t(v, z))), z)

def sh.ap(a: Ap, +z: Sh) -> Ap:
  match a:
    case Ap{+fn, env, res, +loc, done}:
      Ap{sh.t(fn, z), sh.sg(env, z), sh.sg(res, z), loc, []}

def w.aps(xs: List<&2, Ap>, s: S, +z: Sh) -> S:
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      w.aps(rest, ap.new(s, sh.ap(x, z)), z)

def grow.n(n: Nat, s: S) -> S:
  match n:
    case 0n:
      s
    case 1n+k:
      grow.n(k, grow(s))

def pr.grow.n(n: Nat, s: S) -> S:
  match n:
    case 0n:
      s
    case 1n+k:
      pr.grow.n(k, pr.grow(s))

# The doublings an array of depth d needs to hold n.
def doublings(+d: Nat, +n: U32) -> Nat:
  +t: U32 = U32.from_nat(Ln.depth.of(n))
  +v: U32 = U32.from_nat(d)
  U32.to_nat(Bool.pick(U32, U32.is_gt(t, v), (t - v : U32), 0))

def room.v.k1(+need: U32, kr: S & Nat) -> S:
  (s, +vd) = kr
  grow.n(doublings(vd, need), s)

def room.v(s: S, +need: U32) -> S:
  room.v.k1(need, s.vd(s))

def room.p.k1(+need: U32, kr: S & Nat) -> S:
  (s, +pd) = kr
  pr.grow.n(doublings(pd, need), s)

def room.p(s: S, +need: U32) -> S:
  room.p.k1(need, s.pd(s))

def u.count(xs: List<&2, SumEq>) -> U32:
  U32.from_nat(List.length(&2, SumEq, xs))

# instantiateTemplate: an offset copy of the template's block, its deltas
# appended, the occurrence's base spliced into its leaves.
def tm.inst.k8(+dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, +z: Sh, kr: S & U32) -> S & If:
  (s, +nd) = kr
  (s.ndf.set(s, (nd + U32.from_nat(List.length(&2, Df, dfs)) : U32)), If{Sg{sh.v(eb, z), sh.t(et, z)}, sh.sg(res, z), sh.vs(doors, z)})

def tm.inst.k7(+dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, +z: Sh, kr: S & List<&2, Df>) -> S & If:
  (s, od) = kr
  tm.inst.k8(dfs, eb, et, res, doors, z, s.ndf(s.dfs.set(s, sh.dfs(dfs, z, od))))

def tm.inst.k6(+lfs: List<&2, KV>, +dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, +z: Sh, kr: S & U32) -> S & If:
  (s, +nl) = kr
  tm.inst.k7(dfs, eb, et, res, doors, z, s.dfs.swap(s.nlf.set(s, (nl + U32.from_nat(List.length(&2, KV, lfs)) : U32)), []))

def tm.inst.k5(+nb: U32, +lfs: List<&2, KV>, +dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, +z: Sh, kr: S & List<&2, Lp>) -> S & If:
  (s, ol) = kr
  tm.inst.k6(lfs, dfs, eb, et, res, doors, z, s.nlf(s.lfs.set(s, sh.lfs(lfs, nb, z, ol))))

def tm.inst.k4(+nb: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, KV>, +dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, +z: Sh, kr: S & U32) -> S & If:
  (s, +ne) = kr
  tm.inst.k5(nb, lfs, dfs, eb, et, res, doors, z, s.lfs.swap(s.neq.set(s, (ne + u.count(eqs) : U32)), []))

def tm.inst.k3(+nb: U32, +eqs: List<&2, SumEq>, +lfs: List<&2, KV>, +dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, +z: Sh, kr: S & List<&2, SumEq>) -> S & If:
  (s, oe) = kr
  tm.inst.k4(nb, eqs, lfs, dfs, eb, et, res, doors, z, s.neq(s.eqs.set(s, sh.eqs(eqs, z, oe))))

def tm.inst.k2(+nb: U32, +v0: U32, +size: U32, +p0: U32, +psz: U32, bp: List<&2, KV>, ci: List<&2, KC>, tb: List<&2, KV>, tp: List<&2, KV>, ts: List<&2, KT>, pr: List<&2, KV>, +eqs: List<&2, SumEq>, +lfs: List<&2, KV>, aps: List<&2, Ap>, +dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, +base: U32, kr: S & U32) -> S & If:
  (s, +np0) = kr
  +z: Sh = Sh{v0, (base - v0 : U32), p0, (np0 - p0 : U32)}
  s1 = room.p(room.v(s, (base + size : U32)), ((np0 + psz : U32) * 4 : U32))
  s2 = s.np.set(s.nv.set(s1, (base + size : U32)), (np0 + psz : U32))
  s3 = w.aps(aps, w.pr(pr, w.ts(ts, w.tp(tp, w.tb(tb, w.ci(ci, w.bp(bp, s2, z), z), z), z), z), z), z)
  tm.inst.k3(nb, eqs, lfs, dfs, eb, et, res, doors, z, s.eqs.swap(s3, []))

def tm.inst.k1(+nb: U32, +v0: U32, +size: U32, +p0: U32, +psz: U32, bp: List<&2, KV>, ci: List<&2, KC>, tb: List<&2, KV>, tp: List<&2, KV>, ts: List<&2, KT>, pr: List<&2, KV>, +eqs: List<&2, SumEq>, +lfs: List<&2, KV>, aps: List<&2, Ap>, +dfs: List<&2, Df>, +eb: U32, +et: U32, +res: Sg, +doors: List<&2, U32>, kr: S & U32) -> S & If:
  (s, +base) = kr
  tm.inst.k2(nb, v0, size, p0, psz, bp, ci, tb, tp, ts, pr, eqs, lfs, aps, dfs, eb, et, res, doors, base, s.np(s))

def tm.inst(s: S, +nb: U32, t: Tm) -> S & If:
  match t:
    case Tm{fi, +v0, +size, +p0, +psz, bp, ci, tb, tp, ts, pr, +eqs, +lfs, aps, +dfs, +eb, +et, +res, +doors}:
      tm.inst.k1(nb, v0, size, p0, psz, bp, ci, tb, tp, ts, pr, eqs, lfs, aps, dfs, eb, et, res, doors, s.nv(s))

# walkTop
# -------

def r.sg(r: R) -> Sg:
  match r:
    case RSg{+sg}:
      sg
    case RView{+sg, +d}:
      sg
    case RIf{+ifc}:
      Sg{0, ty.data()}

def r.d(v: R) -> U32:
  match v:
    case RView{sg, +d}:
      d
    case other:
      0

def r.if(v: R) -> If:
  match v:
    case RIf{+ifc}:
      ifc
    case other:
      If{Sg{0, ty.data()}, Sg{0, ty.data()}, []}

def ret(s: S, +sg: Sg, st: List<&2, Fr>) -> WM:
  WmGo{s, TRet{RSg{sg}}, st}

def ret.k(r: S & Sg, st: List<&2, Fr>) -> WM:
  (s, +sg) = r
  WmGo{s, TRet{RSg{sg}}, st}

def vw.d.at.k1(+par: U32, +w: U32, +loc: Lc.Loc, kr: S & U32) -> S & U32:
  (s, +d) = kr
  (add.eq(s, blame(loc, "box depth = the parent's depth + this edge's boxes"), [(par - 1 : U32), w], d), d)

def vw.d.at(root: Bool, s: S, +par: U32, +w: U32, +loc: Lc.Loc) -> S & U32:
  match root:
    case True{}:
      (s, w)
    case False{}:
      vw.d.at.k1(par, w, loc, fresh(s))

# viewNodeWith's first half: the edge's boxes and the node's depth.
def vw.depth(s: S, p: Pa, +w: U32, +loc: Lc.Loc) -> S & U32:
  match p:
    case Pa{+par, base}:
      vw.d.at(U32.is_eq(par, 0), s, par, w, loc)

def bd.link(b: Bd) -> Bool:
  match b:
    case Bd{h, fi, +link, t}:
      link

def link.code.k1(kr: S & Bd) -> S & Bool:
  (s, b) = kr
  (s, bd.link(b))

def link.code(s: S, a: A) -> S & Bool:
  match a:
    case ARef{loc, +r}:
      link.code.k1(s.bd(s, r))
    case other:
      (s, False{})

# Whether a chain's previous approximant is itself a link.
def prev.link(s: S, prev: A) -> S & Bool:
  match prev:
    case APair{l, pa, pb}:
      match pb:
        case APair{l2, x, y}:
          link.code(s, pa)
        case other:
          (s, False{})
    case other:
      (s, False{})

def wm.chain.b.k1(+c: Ctx, +p: Pa, +loc: Lc.Loc, +a: A, st: List<&2, Fr>, +bloc: Lc.Loc, +prev: A, +trb: A, kr: S & Bool) -> WM:
  (s, +pl) = kr
  WmGo{s, TChild{c, p, a}, FChA{c, p, loc, bloc, prev, trb, pl, pa.d(p)} <> st}

def wm.chain.b(b: A, s: S, +c: Ctx, +p: Pa, +loc: Lc.Loc, +a: A, st: List<&2, Fr>) -> WM:
  match b:
    case APair{+bloc, +prev, +trb}:
      wm.chain.b.k1(c, p, loc, a, st, bloc, prev, trb, prev.link(s, prev))
    case other:
      WmGo{s, TChild{c, p, a}, FPairA{c, p, loc, other} <> st}

def wm.chain(islink: Bool, s: S, +c: Ctx, +p: Pa, +loc: Lc.Loc, +a: A, +b: A, st: List<&2, Fr>) -> WM:
  match islink:
    case False{}:
      WmGo{s, TChild{c, p, a}, FPairA{c, p, loc, b} <> st}
    case True{}:
      wm.chain.b(b, s, c, p, loc, a, st)

def wm.pair.b(b: A) -> Bool:
  match b:
    case APair{l, x, y}:
      True{}
    case other:
      False{}

def wm.pair.u.k1(+c: Ctx, +p: Pa, +loc: Lc.Loc, +a: A, +b: A, st: List<&2, Fr>, kr: S & Bool) -> WM:
  (s, +isl) = kr
  wm.chain(Bool.and(isl, wm.pair.b(b)), s, c, p, loc, a, b, st)

def wm.pair.u(uni: Bool, s: S, +c: Ctx, +p: Pa, +loc: Lc.Loc, +a: A, +b: A, st: List<&2, Fr>) -> WM:
  match uni:
    case False{}:
      WmGo{s, TChild{c, p, a}, FPairA{c, p, loc, b} <> st}
    case True{}:
      wm.pair.u.k1(c, p, loc, a, b, st, link.code(s, a))

def wm.lr(m: Maybe<&2, List<&2, U32>>, +left: Bool, s: S, +c: Ctx, +p: Pa, +loc: Lc.Loc, +x: A, st: List<&2, Fr>) -> WM:
  match m:
    case Some{+steps}:
      ret.k(env.occ(s, c, p, loc, List.append(&2, U32, steps, [Bool.pick(U32, left, 0, 1)])), st)
    case None{}:
      WmGo{s, TView{c, p, x}, FProj{loc, left} <> st}

# intrinsic
def wm.intr.k1(+c: Ctx, +p: Pa, st: List<&2, Fr>, +loc: Lc.Loc, +a: A, +b: A, kr: S & Bool) -> WM:
  (s, +u) = kr
  wm.pair.u(u, s, c, p, loc, a, b, st)

def wm.intr.k2(st: List<&2, Fr>, +loc: Lc.Loc, kr: S & U32) -> WM:
  (s, +ct) = kr
  ret.k(plain(s, loc, "gate is an unboxed value", ct), st)

def wm.intr(t: A, s: S, +c: Ctx, +p: Pa, st: List<&2, Fr>) -> WM:
  match t:
    case AZero{+loc}:
      ret.k(plain(leaf(s, c, p), loc, "Zero is an unboxed value", ty.data()), st)
    case APair{+loc, +a, +b}:
      wm.intr.k1(c, p, st, loc, a, b, s.uni(s))
    case AEnv{+loc}:
      ret.k(env.occ(s, c, p, loc, []), st)
    case AUns{+loc}:
      ret.k(env.occ(s, c, p, loc, []), st)
    case ARef{+loc, +r}:
      WmGo{leaf(s, c, p), TInst{ctx.unit(c), p, r}, FRef{loc, r} <> st}
    case ASetEnv{+loc, +x}:
      WmGo{s, TView{c, p, x}, FSetEnv{loc} <> st}
    case AGate{+loc}:
      wm.intr.k2(st, loc, builtin.code(leaf(s, c, p), tag.gate()))
    case ALeft{+loc, +x}:
      wm.lr(env.path(x), True{}, s, c, p, loc, x, st)
    case ARight{+loc, +x}:
      wm.lr(env.path(x), False{}, s, c, p, loc, x, st)
    case AAbort{+loc, +m}:
      WmGo{s, TView{c, p, m}, FAbort{} <> st}
    case ABot{+loc}:
      ret.k(bottom(s), st)
    case ACheck{+loc, +x}:
      WmGo{s, TIntr{c, p, x}, st}

# viewNode's first half
def wm.view.k2(+c: Ctx, +p: Pa, +t: A, st: List<&2, Fr>, +w: U32, kr: S & U32) -> WM:
  (s, +d) = kr
  WmGo{s, TIntr{c, Pa{(d + 1 : U32), pa.base(p)}, t}, FView{a.loc(t), w, d} <> st}

def wm.view.k1(+c: Ctx, +p: Pa, +t: A, st: List<&2, Fr>, kr: S & U32) -> WM:
  (s, +w) = kr
  wm.view.k2(c, p, t, st, w, vw.depth(s, p, w, a.loc(t)))

def wm.view(s: S, +c: Ctx, +p: Pa, +t: A, st: List<&2, Fr>) -> WM:
  wm.view.k1(c, p, t, st, fresh(s))

def wm.lit.k4(st: List<&2, Fr>, +pt: U32, kr: S & U32) -> WM:
  (s, +b2) = kr
  ret(s, Sg{b2, pt}, st)

def wm.lit.k3(st: List<&2, Fr>, kr: S & U32) -> WM:
  (s, +pt) = kr
  wm.lit.k4(st, pt, fresh(s))

def wm.lit.k2(st: List<&2, Fr>, +l: Sg, kr: S & Sg) -> WM:
  (s, +rr) = kr
  wm.lit.k3(st, pair.new(s, l, rr))

def wm.lit.k1(st: List<&2, Fr>, kr: S & Sg) -> WM:
  (s, +l) = kr
  wm.lit.k2(st, l, data.leaf(s))

def wm.lit(t: A, s: S, st: List<&2, Fr>) -> WM:
  match t:
    case APair{loc, a, b}:
      wm.lit.k1(st, data.leaf(s))
    case other:
      ret.k(data.leaf(s), st)

# pairChild: a closed data tree is one leaf.
def wm.child(lit: Bool, s: S, +c: Ctx, +p: Pa, +t: A, st: List<&2, Fr>) -> WM:
  match lit:
    case False{}:
      WmGo{s, TView{c, p, t}, st}
    case True{}:
      wm.lit(t, leaf(s, c, p), st)

def wm.cap.k5(+base: U32, +r: U32, st: List<&2, Fr>, +fi: U32, +body: A, +z: Snap, +benv: U32, +tenv: U32, +frame0: U32, kr: S & Ctx) -> WM:
  (s, +c) = kr
  WmGo{rec.defer(s, fi, benv), TView{c, Pa{0, base}, body}, FCap{r, fi, z, frame0, benv, tenv, ctx.doorl(c)} <> st}

def wm.cap.k4(+unit: U32, +base: U32, +r: U32, st: List<&2, Fr>, +fi: U32, +body: A, +z: Snap, +benv: U32, +tenv: U32, kr: S & U32) -> WM:
  (s, +frame0) = kr
  wm.cap.k5(base, r, st, fi, body, z, benv, tenv, frame0, frame.context(s.frame.set(s, (fi + 1 : U32)), unit, (fi + 1 : U32), "env of " ++ Co.fi.show(fi), benv, tenv, body))

def wm.cap.k3(+unit: U32, +base: U32, +r: U32, st: List<&2, Fr>, +fi: U32, +body: A, +z: Snap, +benv: U32, kr: S & U32) -> WM:
  (s, +tenv) = kr
  wm.cap.k4(unit, base, r, st, fi, body, z, benv, tenv, s.frame(s))

def wm.cap.k2(+unit: U32, +base: U32, +r: U32, st: List<&2, Fr>, +fi: U32, +body: A, +z: Snap, kr: S & U32) -> WM:
  (s, +benv) = kr
  wm.cap.k3(unit, base, r, st, fi, body, z, benv, fresh.tau(s))

def wm.cap.k1(+unit: U32, +base: U32, +r: U32, st: List<&2, Fr>, +fi: U32, +body: A, kr: S & Snap) -> WM:
  (s, +z) = kr
  wm.cap.k2(unit, base, r, st, fi, body, z, fresh(s))

def wm.cap(b: Bd, s: S, +unit: U32, +base: U32, +r: U32, st: List<&2, Fr>) -> WM:
  match b:
    case Bd{h, +fi, link, +body}:
      wm.cap.k1(unit, base, r, st, fi, body, snap(s))

def wm.inst.at.k1(st: List<&2, Fr>, kr: S & If) -> WM:
  (s, +ifc) = kr
  WmGo{s, TRet{RIf{ifc}}, st}

def wm.inst.at.k2(+unit: U32, +base: U32, +r: U32, st: List<&2, Fr>, kr: S & Bd) -> WM:
  (s, b) = kr
  wm.cap(b, s, unit, base, r, st)

def wm.inst.at(m: Mt, s: S, +unit: U32, +base: U32, +r: U32, st: List<&2, Fr>) -> WM:
  match m:
    case MtSome{t}:
      wm.inst.at.k1(st, tm.inst(s, base, t))
    case MtNone{}:
      wm.inst.at.k2(unit, base, r, st, s.bd(s, r))

# instantiateBody
def wm.inst.k2(+unit: U32, +r: U32, st: List<&2, Fr>, +base: U32, kr: S & Mt) -> WM:
  (s, m) = kr
  wm.inst.at(m, s, unit, base, r, st)

def wm.inst.k1(+unit: U32, +p: Pa, +r: U32, st: List<&2, Fr>, kr: S & U32) -> WM:
  (s, +base) = kr
  wm.inst.k2(unit, r, st, base, s.tm(add.eq(s, Blame{gen("instance base"), "an occurrence's global depth = its frame's base + its depth", 0}, [pa.base(p), pa.d(p)], base), r))

def wm.inst(s: S, +unit: U32, +p: Pa, +r: U32, st: List<&2, Fr>) -> WM:
  wm.inst.k1(unit, p, r, st, fresh(s))

def wm.chp(plink: Bool, s: S, +dprev: U32, +dlink: U32) -> S:
  match plink:
    case True{}:
      union.b(s, dprev, dlink)
    case False{}:
      s

def wm.cht(plink: Bool, s: S, +loc: Lc.Loc, +a: Sg, +b: Sg) -> S:
  match plink:
    case True{}:
      unify.sig(s, loc, a, b)
    case False{}:
      s

# A frame meeting the value of the task below it.
def wm.frame.k1(+v: R, st: List<&2, Fr>, +loc: Lc.Loc, +w: U32, +d: U32, kr: S & U32) -> WM:
  (s, +vv) = kr
  WmGo{add.eq(s, blame(loc, "view bangs = edge boxes + intrinsic bangs"), [w, sg.b(r.sg(v))], vv),
    TRet{RView{Sg{vv, sg.t(r.sg(v))}, d}}, st}

def wm.frame.k2(st: List<&2, Fr>, +loc: Lc.Loc, kr: S & U32) -> WM:
  (s, +ct) = kr
  ret.k(plain(s, loc, "code constant is an unboxed value", ct), st)

def wm.frame.k3(st: List<&2, Fr>, kr: S & If) -> WM:
  (s, +ifc) = kr
  WmGo{s, TRet{RIf{ifc}}, st}

def wm.frame.k5(+v: R, st: List<&2, Fr>, +c: Ctx, +p: Pa, +loc: Lc.Loc, +bloc: Lc.Loc, +prev: A, +trb: A, +plink: Bool, +dlink: U32, +w2: U32, kr: S & U32) -> WM:
  (s, +d2) = kr
  WmGo{s, TView{c, Pa{(d2 + 1 : U32), pa.base(p)}, prev},
    FChP{c, Pa{(d2 + 1 : U32), pa.base(p)}, loc, bloc, trb, plink, dlink, r.sg(v), w2, d2} <> st}

def wm.frame.k4(+v: R, st: List<&2, Fr>, +c: Ctx, +p: Pa, +loc: Lc.Loc, +bloc: Lc.Loc, +prev: A, +trb: A, +plink: Bool, +dlink: U32, kr: S & U32) -> WM:
  (s, +w2) = kr
  wm.frame.k5(v, st, c, p, loc, bloc, prev, trb, plink, dlink, w2, vw.depth(s, p, w2, bloc))

def wm.frame.k8(st: List<&2, Fr>, +loc: Lc.Loc, +sprev: Sg, +plink: Bool, kr: S & Sg) -> WM:
  (s, +s2) = kr
  ret(wm.cht(plink, s, loc, s2, sprev), s2, st)

def wm.frame.k7(st: List<&2, Fr>, +loc: Lc.Loc, +bloc: Lc.Loc, +sa: Sg, +w2: U32, +sprev: Sg, +plink: Bool, +s1: Sg, kr: S & U32) -> WM:
  (s, +vv) = kr
  wm.frame.k8(st, loc, sprev, plink, pair.of(add.eq(s, blame(bloc, "view bangs = edge boxes + intrinsic bangs"), [w2, sg.b(s1)], vv), loc, sa, Sg{vv, sg.t(s1)}))

def wm.frame.k6(st: List<&2, Fr>, +loc: Lc.Loc, +bloc: Lc.Loc, +sa: Sg, +w2: U32, +sprev: Sg, +plink: Bool, kr: S & Sg) -> WM:
  (s, +s1) = kr
  wm.frame.k7(st, loc, bloc, sa, w2, sprev, plink, s1, fresh(s))

def wm.frame(fr: Fr, s: S, +v: R, st: List<&2, Fr>) -> WM:
  match fr:
    case FView{+loc, +w, +d}:
      wm.frame.k1(v, st, loc, w, d, fresh(s))
    case FPairA{+c, +p, +loc, +b}:
      WmGo{s, TChild{c, p, b}, FPairB{loc, r.sg(v)} <> st}
    case FPairB{+loc, +sa}:
      ret.k(pair.of(s, loc, sa, r.sg(v)), st)
    case FSetEnv{+loc}:
      ret.k(set.env(s, loc, r.sg(v)), st)
    case FProj{+loc, +left}:
      ret.k(proj(s, loc, left, r.sg(v)), st)
    case FAbort{}:
      ret.k(bottom(s), st)
    case FRef{+loc, +r}:
      wm.frame.k2(st, loc, fresh.code(s, [TE{r, None{}, Some{r.if(v)}}]))
    case FCap{+r, +fi, +z, +frame0, +benv, +tenv, +doorl}:
      wm.frame.k3(st, cap.finish(s, r, fi, z, frame0, benv, tenv, doorl, r.sg(v)))
    case FChA{+c, +p, +loc, +bloc, +prev, +trb, +plink, +dlink}:
      wm.frame.k4(v, st, c, p, loc, bloc, prev, trb, plink, dlink, fresh(s))
    case FChP{+c, +ip, +loc, +bloc, +trb, +plink, +dlink, +sa, +w2, +d2}:
      WmGo{wm.chp(plink, s, r.d(v), dlink), TChild{c, ip, trb}, FChT{loc, bloc, sa, w2, d2, r.sg(v), plink} <> st}
    case FChT{+loc, +bloc, +sa, +w2, +d2, +sprev, +plink}:
      wm.frame.k6(st, loc, bloc, sa, w2, sprev, plink, pair.of(s, bloc, sprev, r.sg(v)))

def wm.ret(st: List<&2, Fr>, s: S, +v: R) -> WM:
  match st:
    case Nil{}:
      WmEnd{s, v}
    case Con{fr, rest}:
      wm.frame(fr, s, v, rest)

def wm.task(task: Task, s: S, st: List<&2, Fr>) -> WM:
  match task:
    case TRet{+v}:
      wm.ret(st, s, v)
    case TView{+c, +p, +t}:
      wm.view(s, c, p, t, st)
    case TIntr{+c, +p, +t}:
      wm.intr(t, s, c, p, st)
    case TChild{+c, +p, +t}:
      wm.child(data.lit(t), s, c, p, t, st)
    case TInst{+unit, +p, +r}:
      wm.inst(s, unit, p, r, st)

def wm.step.at(bad: Bool, s: S, task: Task, st: List<&2, Fr>) -> WM:
  match bad:
    case True{}:
      WmEnd{s, RSg{Sg{0, ty.data()}}}
    case False{}:
      wm.task(task, s, st)

def wm.step.k1(task: Task, st: List<&2, Fr>, kr: S & Bool) -> WM:
  (s, +bad) = kr
  wm.step.at(bad, s, task, st)

def wm.step(s: S, task: Task, st: List<&2, Fr>) -> WM:
  wm.step.k1(task, st, failed(s))

def wm.fin(n: WM) -> S & R:
  match n:
    case WmGo{s, task, st}:
      (fail(s, Internal{"the walk ran out of fuel"}), RSg{Sg{0, ty.data()}})
    case WmEnd{s, v}:
      (s, v)

def wm.loop(fuel: Nat, n: WM) -> S & R:
  match fuel:
    case 0n:
      wm.fin(n)
    case 1n+f:
      match n:
        case WmGo{s, task, st}:
          wm.loop(f, wm.step(s, task, st))
        case WmEnd{s, v}:
          (s, v)

# viewNode at a frame root, to the end of the walk: the node's sigma.
def walk.view(s: S, +c: Ctx, +base: U32, +t: A) -> S & R:
  wm.loop(big(), wm.step(s, TView{c, Pa{0, base}, t}, []))

# Application dispatch (resolveApplies)
# --------------------

def te.head.done(es: List<&2, TE>, +done: List<&2, U32>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, rest}:
      u.has(done, te.tag(e))

def te.new.go(es: List<&2, TE>, +done: List<&2, U32>, hit: Bool) -> List<&2, TE>:
  match es:
    case Nil{}:
      []
    case Con{+e, +rest}:
      match hit:
        case True{}:
          te.new.go(rest, done, te.head.done(rest, done))
        case False{}:
          e <> te.new.go(rest, done, te.head.done(rest, done))

# Map.withoutKeys
def te.keys.has(+es: List<&2, TE>, +done: List<&2, U32>) -> List<&2, TE>:
  te.new.go(es, done, te.head.done(es, done))

def te.mark(es: List<&2, TE>, +done: List<&2, U32>) -> List<&2, U32>:
  match es:
    case Nil{}:
      done
    case Con{e, rest}:
      te.mark(rest, Ln.u.ins(done, te.tag(e)))

# Map.intersectionWith (,): the pairs of records of the tags on both sides.
def te.both(xs: List<&2, TE>, +ys: List<&2, TE>, +loc: Lc.Loc) -> List<&2, W>:
  te.pending(xs, ys, loc, [])

# codeInfosOfCaptures' merge: same-tag records unify, then the maps union.
def ci.merge(s: S, +loc: Lc.Loc, +acc: List<&2, TE>, +m: List<&2, TE>) -> S & List<&2, TE>:
  (un.run(s, te.both(acc, m, loc)), te.union(acc, m))

def ck.kind.k1(+loc: Lc.Loc, +vis: List<&2, U32>, +rest: List<&2, TE>, +acc: List<&2, TE>, st: List<&2, CF>, kr: S & List<&2, TE>) -> CM:
  (s, +m) = kr
  CmGo{s, loc, CkRet{m}, CfFold{vis, rest, acc} <> st}

def ck.kind(k: K, s: S, +loc: Lc.Loc, +w: U32, +vis: List<&2, U32>, +rest: List<&2, TE>, +acc: List<&2, TE>, st: List<&2, CF>) -> CM:
  match k:
    case KCode{}:
      ck.kind.k1(loc, vis, rest, acc, st, captures.of(s, ty.of(w)))
    case KCap{}:
      CmGo{s, loc, CkGo{vis, ty.of(w)}, CfFold{vis, rest, acc} <> st}
    case other:
      CmGo{s, loc, CkRet{[]}, CfFold{vis, rest, acc} <> st}

# The fold over a package's captures: the next capture's code records.
def ck.next.k1(+loc: Lc.Loc, +vis: List<&2, U32>, +acc: List<&2, TE>, st: List<&2, CF>, rest: List<&2, TE>, kr: S & U32) -> CM:
  (s, +w) = kr
  ck.kind(kind(w), s, loc, w, vis, rest, acc, st)

def ck.next(es: List<&2, TE>, s: S, +loc: Lc.Loc, +vis: List<&2, U32>, +acc: List<&2, TE>, st: List<&2, CF>) -> CM:
  match es:
    case Nil{}:
      CmGo{s, loc, CkRet{acc}, st}
    case Con{e, rest}:
      match e:
        case TE{tag, cap, ifc}:
          match cap:
            case Some{c}:
              match c:
                case Sg{cb, +ct}:
                  ck.next.k1(loc, vis, acc, st, rest, walk(s, ct))
            case None{}:
              CmGo{s, loc, CkRet{[]}, CfFold{vis, rest, acc} <> st}

def ck.go.at.k1(+loc: Lc.Loc, +vis: List<&2, U32>, +r: U32, st: List<&2, CF>, kr: S & List<&2, TE>) -> CM:
  (s, es) = kr
  ck.next(es, s, loc, r <> vis, [], st)

def ck.go.at(seen: Bool, s: S, +loc: Lc.Loc, +vis: List<&2, U32>, +r: U32, st: List<&2, CF>) -> CM:
  match seen:
    case True{}:
      CmGo{s, loc, CkRet{[]}, st}
    case False{}:
      ck.go.at.k1(loc, vis, r, st, s.ts(s, r))

def ck.frame.k1(+loc: Lc.Loc, st: List<&2, CF>, +vis: List<&2, U32>, rest: List<&2, TE>, kr: S & List<&2, TE>) -> CM:
  (s, +acc2) = kr
  ck.next(rest, s, loc, vis, acc2, st)

def ck.frame(fr: CF, s: S, +loc: Lc.Loc, +m: List<&2, TE>, st: List<&2, CF>) -> CM:
  match fr:
    case CfFold{+vis, rest, +acc}:
      ck.frame.k1(loc, st, vis, rest, ci.merge(s, loc, acc, m))

def ck.ret(st: List<&2, CF>, s: S, +loc: Lc.Loc, +m: List<&2, TE>) -> CM:
  match st:
    case Nil{}:
      CmEnd{s, m}
    case Con{fr, rest}:
      ck.frame(fr, s, loc, m, rest)

def ck.task.k1(+loc: Lc.Loc, st: List<&2, CF>, +vis: List<&2, U32>, kr: S & U32) -> CM:
  (s, +r) = kr
  ck.go.at(u.has(vis, r), s, loc, vis, r, st)

def ck.task(task: CK, s: S, +loc: Lc.Loc, st: List<&2, CF>) -> CM:
  match task:
    case CkGo{+vis, +i}:
      ck.task.k1(loc, st, vis, find.t(s, i))
    case CkRet{+m}:
      ck.ret(st, s, loc, m)

def ck.fin(n: CM) -> S & List<&2, TE>:
  match n:
    case CmGo{s, loc, task, st}:
      (s, [])
    case CmEnd{s, m}:
      (s, m)

def ck.loop(fuel: Nat, n: CM) -> S & List<&2, TE>:
  match fuel:
    case 0n:
      ck.fin(n)
    case 1n+f:
      match n:
        case CmGo{s, +loc, task, st}:
          ck.loop(f, ck.task(task, s, loc, st))
        case CmEnd{s, m}:
          (s, m)

# codeInfosOfCaptures
def code.infos(s: S, +loc: Lc.Loc, +i: U32) -> S & List<&2, TE>:
  ck.loop(big(), CmGo{s, loc, CkGo{[], i}, []})

def ifc.or(m: Maybe<&2, If>) -> If:
  match m:
    case Some{+x}:
      x
    case None{}:
      If{Sg{0, ty.data()}, Sg{0, ty.data()}, []}

def dt.gatefn.k6(+res: Sg, +loc: Lc.Loc, +sbt: Sg, +brb: U32, kr: S & U32) -> S:
  (s, +rt) = kr
  unify.sig(add.eq(s, blame(loc, "taken branch boxes = branch pair boxes + its own"), [brb, sg.b(sbt)], rt), loc, res, Sg{rt, sg.t(sbt)})

def dt.gatefn.k5(+res: Sg, +loc: Lc.Loc, +sbe: Sg, +sbt: Sg, +brb: U32, kr: S & U32) -> S:
  (s, +re) = kr
  dt.gatefn.k6(res, loc, sbt, brb, fresh(unify.sig(add.eq(s, blame(loc, "taken branch boxes = branch pair boxes + its own"), [brb, sg.b(sbe)], re), loc, res, Sg{re, sg.t(sbe)})))

def dt.gatefn.k4(+env: Sg, +res: Sg, +loc: Lc.Loc, +sbe: Sg, +sbt: Sg, +brb: U32, kr: S & U32) -> S:
  (s, +pt) = kr
  dt.gatefn.k5(res, loc, sbe, sbt, brb, fresh(unify.sig(s, loc, env, Sg{brb, pt})))

def dt.gatefn.k3(+env: Sg, +res: Sg, +loc: Lc.Loc, +sbe: Sg, +sbt: Sg, kr: S & U32) -> S:
  (s, +brb) = kr
  dt.gatefn.k4(env, res, loc, sbe, sbt, brb, pair.new(s, sbe, sbt))

def dt.gatefn.k2(+env: Sg, +res: Sg, +loc: Lc.Loc, +sbe: Sg, kr: S & Sg) -> S:
  (s, +sbt) = kr
  dt.gatefn.k3(env, res, loc, sbe, sbt, fresh(s))

def dt.gatefn.k1(+env: Sg, +res: Sg, +loc: Lc.Loc, kr: S & Sg) -> S:
  (s, +sbe) = kr
  dt.gatefn.k2(env, res, loc, sbe, fresh.sig(s))

def dt.gatefn(s: S, +env: Sg, +res: Sg, +loc: Lc.Loc) -> S:
  dt.gatefn.k1(env, res, loc, fresh.sig(s))

def dt.gate.k3(+res: Sg, +loc: Lc.Loc, kr: S & Sg) -> S:
  (s, +gfn) = kr
  unify.sig(s, loc, res, gfn)

def dt.gate.k2(+res: Sg, +loc: Lc.Loc, kr: S & U32) -> S:
  (s, +gt) = kr
  dt.gate.k3(res, loc, plain(s, loc, "gate switch function is locally unboxed", gt))

def dt.gate.k1(+env: Sg, +res: Sg, +loc: Lc.Loc, kr: S & U32) -> S:
  (s, +scrb) = kr
  dt.gate.k2(res, loc, builtin.code(unify.sig(s, loc, env, Sg{scrb, ty.data()}), tag.gatefn()))

def dt.gate(s: S, +env: Sg, +res: Sg, +loc: Lc.Loc) -> S:
  dt.gate.k1(env, res, loc, fresh(s))

def dt.code(x: If, s: S, +tag: U32, +env: Sg, +res: Sg, +loc: Lc.Loc) -> S:
  match x:
    case If{+ie, +ir, doors}:
      unify.sig(unify.sig.at(s, tag, loc, env, ie), loc, res, ir)

def dt.at(gate: Bool, gatefn: Bool, s: S, e: TE, +env: Sg, +res: Sg, +loc: Lc.Loc) -> S:
  match gate:
    case True{}:
      dt.gate(s, env, res, loc)
    case False{}:
      match gatefn:
        case True{}:
          dt.gatefn(s, env, res, loc)
        case False{}:
          match e:
            case TE{+tag, cap, ifc}:
              dt.code(ifc.or(ifc), s, tag, env, res, loc)

# dispatchTag: the constraints of applying one tag at one site.
def dispatch.tag(s: S, +e: TE, +env: Sg, +res: Sg, +loc: Lc.Loc) -> S:
  dt.at(U32.is_eq(te.tag(e), tag.gate()), U32.is_eq(te.tag(e), tag.gatefn()), s, e, env, res, loc)

def dispatch.all(es: List<&2, TE>, s: S, +env: Sg, +res: Sg, +loc: Lc.Loc) -> S:
  match es:
    case Nil{}:
      s
    case Con{+e, rest}:
      dispatch.all(rest, dispatch.tag(s, e, env, res, loc), env, res, loc)

def ap.done.set(a: Ap, +done: List<&2, U32>) -> Ap:
  match a:
    case Ap{+fn, +env, +res, +loc, old}:
      Ap{fn, env, res, loc, done}

def dn.at(new: List<&2, TE>, s: S, +k: U32, +fn: U32, +env: Sg, +res: Sg, +loc: Lc.Loc, +done: List<&2, U32>) -> S & Bool:
  match new:
    case Nil{}:
      (s, False{})
    case Con{+e, +rest}:
      (dispatch.all(Con{e, rest}, s.ap.set(s, k, Ap{fn, env, res, loc, te.mark(Con{e, rest}, done)}), env, res, loc), True{})

# dispatchNew: dispatch the tags not dispatched at this site yet.
def dispatch.new(s: S, +k: U32, a: Ap, +infos: List<&2, TE>) -> S & Bool:
  match a:
    case Ap{+fn, +env, +res, +loc, +done}:
      dn.at(te.keys.has(infos, done), s, k, fn, env, res, loc, done)

def site.kind.k1(+k: U32, +a: Ap, kr: S & List<&2, TE>) -> S & Bool:
  (s, +es) = kr
  dispatch.new(s, k, a, es)

def site.kind.k2(+k: U32, +a: Ap, kr: S & List<&2, TE>) -> S & Bool:
  (s, +es) = kr
  dispatch.new(s, k, a, es)

def ap.loc(a: Ap) -> Lc.Loc:
  match a:
    case Ap{fn, env, res, +loc, done}:
      loc

def ap.res(a: Ap) -> Sg:
  match a:
    case Ap{fn, env, +res, loc, done}:
      res

def site.kind.k3(+a: Ap, kr: S & Sg) -> S & Bool:
  (s, +bt) = kr
  (unify.sig(s, ap.loc(a), ap.res(a), bt), False{})

def site.kind.k5(+a: Ap, +w: U32, +fs: String, kr: S & String) -> S & Bool:
  (s, +es) = kr
  (fail(s, TypeMismatch{ap.loc(a), "applied value is " ++ describe(w) ++ ", not code: " ++ fs ++ " applied to " ++ es}), False{})

def ap.env(a: Ap) -> Sg:
  match a:
    case Ap{fn, +env, res, loc, done}:
      env

def site.kind.k4(+a: Ap, +w: U32, kr: S & String) -> S & Bool:
  (s, +fs) = kr
  site.kind.k5(a, w, fs, ds.four(s, sg.t(ap.env(a))))

def site.kind(kd: K, s: S, +k: U32, +a: Ap, +w: U32) -> S & Bool:
  match kd:
    case KVar{}:
      (s, False{})
    case KData{}:
      (s, False{})
    case KCode{}:
      site.kind.k1(k, a, captures.of(s, ty.of(w)))
    case KCap{}:
      site.kind.k2(k, a, code.infos(s, ap.loc(a), ty.of(w)))
    case KAbort{}:
      site.kind.k3(a, bottom(s))
    case KPair{}:
      site.kind.k4(a, w, ds.four(s, w))

def ap.fn(a: Ap) -> U32:
  match a:
    case Ap{+fn, env, res, loc, done}:
      fn

# resolveSite
def site.resolve.k2(+k: U32, +a: Ap, kr: S & U32) -> S & Bool:
  (s, +w) = kr
  site.kind(kind(w), s, k, a, w)

def site.resolve.k1(+k: U32, kr: S & Ap) -> S & Bool:
  (s, +a) = kr
  site.resolve.k2(k, a, walk(s, ap.fn(a)))

def site.resolve(s: S, +k: U32) -> S & Bool:
  site.resolve.k1(k, s.ap(s, k))

def round.or(+acc: Bool, r: S & Bool) -> S & Bool:
  (s, +c) = r
  (s, Bool.or(acc, c))

def round.go(n: Nat, r: S & Bool, +k: U32) -> S & Bool:
  match n:
    case 0n:
      r
    case 1n+m:
      (s, +acc) = r
      round.go(m, round.or(acc, site.resolve(s, k)), (k + 1 : U32))

# dispatchRound: every site, in key order.
def round.k1(kr: S & U32) -> S & Bool:
  (s, +na) = kr
  round.go(U32.to_nat(na), (s, False{}), 0)

def round(s: S) -> S & Bool:
  round.k1(s.na(s))

def ra.at(more: Bool, bad: Bool, s: S) -> RA:
  match more:
    case True{}:
      match bad:
        case True{}:
          RaDone{s}
        case False{}:
          RaGo{s}
    case False{}:
      RaDone{s}

def ra.k.k1(+more: Bool, kr: S & Bool) -> RA:
  (s, +bad) = kr
  ra.at(more, bad, s)

def ra.k(r: S & Bool) -> RA:
  (s, +more) = r
  ra.k.k1(more, failed(s))

def ra.fin(n: RA) -> S:
  match n:
    case RaGo{s}:
      s
    case RaDone{s}:
      s

def ra.loop(fuel: Nat, n: RA) -> S:
  match fuel:
    case 0n:
      ra.fin(n)
    case 1n+f:
      match n:
        case RaGo{s}:
          ra.loop(f, ra.k(round(s)))
        case RaDone{s}:
          s

# resolveApplies: rounds to a fixpoint.
def resolve.applies(s: S) -> S:
  ra.loop(big(), RaGo{s})

# show :: [Int] -> String
def ints.go(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "]"
    case Con{+x, rest}:
      "," ++ U32.show(x) ++ ints.go(rest)

def ints.show(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "[]"
    case Con{+x, rest}:
      "[" ++ U32.show(x) ++ ints.go(rest)

# derivedBlame
def bl.derive(+what: String, b: Blame) -> Blame:
  match b:
    case Blame{+loc, +why, +fr}:
      Blame{loc, what ++ ": " ++ why, fr}

def bl.why(b: Blame) -> String:
  match b:
    case Blame{+loc, +why, +fr}:
      why

def eq.note(lhs: List<&2, U32>, +rhs: U32) -> String:
  " [eq " ++ ints.show(lhs) ++ " = " ++ U32.show(rhs) ++ "]"

# Roots of a list, read-only (resolveEqs) or compressing (mapM findB).
def ro.push.k1(+acc: List<&2, U32>, kr: S & U32) -> S & List<&2, U32>:
  (s, +y) = kr
  (s, y <> acc)

def ro.push(s: S, +acc: List<&2, U32>, +x: U32) -> S & List<&2, U32>:
  ro.push.k1(acc, root.b(s, x))

def ro.go(xs: List<&2, U32>, r: S & List<&2, U32>) -> S & List<&2, U32>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, acc) = r
      ro.go(rest, ro.push(s, acc, x))

def ro.list.k1(kr: S & List<&2, U32>) -> S & List<&2, U32>:
  (s, +ys) = kr
  (s, List.reverse(&2, U32, ys))

def ro.list(s: S, +xs: List<&2, U32>) -> S & List<&2, U32>:
  ro.list.k1(ro.go(xs, (s, [])))

def fb.push.k1(+acc: List<&2, U32>, kr: S & U32) -> S & List<&2, U32>:
  (s, +y) = kr
  (s, y <> acc)

def fb.push(s: S, +acc: List<&2, U32>, +x: U32) -> S & List<&2, U32>:
  fb.push.k1(acc, find.b(s, x))

def fb.go(xs: List<&2, U32>, r: S & List<&2, U32>) -> S & List<&2, U32>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, acc) = r
      fb.go(rest, fb.push(s, acc, x))

def fb.list.k1(kr: S & List<&2, U32>) -> S & List<&2, U32>:
  (s, +ys) = kr
  (s, List.reverse(&2, U32, ys))

def fb.list(s: S, +xs: List<&2, U32>) -> S & List<&2, U32>:
  fb.list.k1(fb.go(xs, (s, [])))

# resolveEqs: every equation over the roots, newest first.
def er.push.k2(+acc: List<&2, ER>, +bl: Blame, +ls: List<&2, U32>, kr: S & U32) -> S & List<&2, ER>:
  (s, +rr) = kr
  (s, ER{ls, rr, bl} <> acc)

def er.push.k1(+acc: List<&2, ER>, +rhs: U32, +bl: Blame, kr: S & List<&2, U32>) -> S & List<&2, ER>:
  (s, +ls) = kr
  er.push.k2(acc, bl, ls, root.b(s, rhs))

def er.push(s: S, +acc: List<&2, ER>, e: SumEq) -> S & List<&2, ER>:
  match e:
    case SumEq{+lhs, +rhs, +bl}:
      er.push.k1(acc, rhs, bl, ro.list(s, lhs))

def er.go(xs: List<&2, SumEq>, r: S & List<&2, ER>) -> S & List<&2, ER>:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (s, acc) = r
      er.go(rest, er.push(s, acc, e))

def resolve.eqs.k2(kr: S & List<&2, ER>) -> S & List<&2, ER>:
  (s, +rs) = kr
  (s, List.reverse(&2, ER, rs))

def resolve.eqs.k1(kr: S & List<&2, SumEq>) -> S & List<&2, ER>:
  (s, +eqs) = kr
  resolve.eqs.k2(er.go(eqs, (s, [])))

def resolve.eqs(s: S) -> S & List<&2, ER>:
  resolve.eqs.k1(s.eqs(s))

# classInfo of a number as it stands (a merged-away root reads as
# unrestricted, as its entry is deleted).
def zero.at.k1(kr: S & CI) -> S & Bool:
  (s, +c) = kr
  (s, ci.zero(c))

def zero.at(s: S, +r: U32) -> S & Bool:
  zero.at.k1(s.ci(s, r))

def lb.at.k1(kr: S & CI) -> S & U32:
  (s, +c) = kr
  (s, ci.lb(c))

def lb.at(s: S, +r: U32) -> S & U32:
  lb.at.k1(s.ci(s, r))

def za.push.k1(+b: Bool, kr: S & Bool) -> S & Bool:
  (s, +z) = kr
  (s, Bool.and(b, z))

def za.push(s: S, +b: Bool, +x: U32) -> S & Bool:
  za.push.k1(b, zero.at(s, x))

def za.go(xs: List<&2, U32>, r: S & Bool) -> S & Bool:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, b) = r
      za.go(rest, za.push(s, b, x))

# Force every number of a list to zero, with one blame: whether any class
# changed.
def cz.push.k1(+a: Bool, kr: S & Bool) -> S & Bool:
  (s, +c) = kr
  (s, Bool.or(a, c))

def cz.push(s: S, +a: Bool, +x: U32, +bl: Blame) -> S & Bool:
  cz.push.k1(a, constrain(s, x, CZero{bl}))

def cz.go(xs: List<&2, U32>, +bl: Blame, r: S & Bool) -> S & Bool:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, a) = r
      cz.go(rest, bl, cz.push(s, a, x, bl))

# The non-zero members of a list, in order.
def nz.push.k1(+acc: List<&2, U32>, +x: U32, kr: S & Bool) -> S & List<&2, U32>:
  (s, +z) = kr
  (s, Bool.pick(List<&2, U32>, z, acc, x <> acc))

def nz.push(s: S, +acc: List<&2, U32>, +x: U32) -> S & List<&2, U32>:
  nz.push.k1(acc, x, zero.at(s, x))

def nz.go(xs: List<&2, U32>, r: S & List<&2, U32>) -> S & List<&2, U32>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, acc) = r
      nz.go(rest, nz.push(s, acc, x))

def nz.list.k1(kr: S & List<&2, U32>) -> S & List<&2, U32>:
  (s, +ys) = kr
  (s, List.reverse(&2, U32, ys))

def nz.list(s: S, +xs: List<&2, U32>) -> S & List<&2, U32>:
  nz.list.k1(nz.go(xs, (s, [])))

# zeroStep
# --------

def zs.c1(z: Bool, s: S, +xs: List<&2, U32>, +bl: Blame) -> S & Bool:
  match z:
    case True{}:
      cz.go(xs, bl, (s, False{}))
    case False{}:
      (s, False{})

def zs.c2(z: Bool, s: S, +r: U32, +bl: Blame) -> S & Bool:
  match z:
    case True{}:
      constrain(s, r, CZero{bl})
    case False{}:
      (s, False{})

def zs.eq.k4(+acc: Bool, +c1: Bool, kr: S & Bool) -> S & Bool:
  (s, +c2) = kr
  (s, Bool.or(acc, Bool.or(c1, c2)))

def zs.eq.k3(+acc: Bool, +rhs: U32, +bl: Blame, +lz: Bool, +note: String, kr: S & Bool) -> S & Bool:
  (s, +c1) = kr
  zs.eq.k4(acc, c1, zs.c2(lz, s, rhs, bl.derive("all summands unboxed" ++ note, bl)))

def zs.eq.k2(+acc: Bool, +lhs: List<&2, U32>, +rhs: U32, +bl: Blame, +rz: Bool, kr: S & Bool) -> S & Bool:
  (s, +lz) = kr
  +note: String = eq.note(lhs, rhs)
  zs.eq.k3(acc, rhs, bl, lz, note, zs.c1(rz, s, lhs, bl.derive("summand of an unboxed total" ++ note, bl)))

def zs.eq.k1(+acc: Bool, +lhs: List<&2, U32>, +rhs: U32, +bl: Blame, kr: S & Bool) -> S & Bool:
  (s, +rz) = kr
  zs.eq.k2(acc, lhs, rhs, bl, rz, za.go(lhs, (s, True{})))

def zs.eq(s: S, +acc: Bool, e: ER) -> S & Bool:
  match e:
    case ER{+lhs, +rhs, +bl}:
      zs.eq.k1(acc, lhs, rhs, bl, zero.at(s, rhs))

def zs.go(xs: List<&2, ER>, r: S & Bool) -> S & Bool:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (s, a) = r
      zs.go(rest, zs.eq(s, a, e))

# equalityStep
# ------------

def es.merge(same: Bool, s: S, +acc: Bool, +l: U32, +r: U32) -> S & Bool:
  match same:
    case True{}:
      (s, acc)
    case False{}:
      (union.b(s, l, r), True{})

def es.lone(bx: List<&2, U32>, s: S, +acc: Bool, +r: U32) -> S & Bool:
  match bx:
    case Nil{}:
      (s, acc)
    case Con{+l, rest}:
      match rest:
        case Nil{}:
          es.merge(U32.is_eq(l, r), s, acc, l, r)
        case Con{+y, t}:
          (s, acc)

def es.eq.k3(+acc: Bool, +r2: U32, kr: S & List<&2, U32>) -> S & Bool:
  (s, +bx) = kr
  es.lone(bx, s, acc, r2)

def es.eq.k2(+acc: Bool, +r2: U32, kr: S & List<&2, U32>) -> S & Bool:
  (s, +ls) = kr
  es.eq.k3(acc, r2, nz.list(s, ls))

def es.eq.k1(+acc: Bool, +lhs: List<&2, U32>, kr: S & U32) -> S & Bool:
  (s, +r2) = kr
  es.eq.k2(acc, r2, fb.list(s, lhs))

def es.eq(s: S, +acc: Bool, e: ER) -> S & Bool:
  match e:
    case ER{+lhs, +rhs, +bl}:
      es.eq.k1(acc, lhs, find.b(s, rhs))

def es.go(xs: List<&2, ER>, r: S & Bool) -> S & Bool:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (s, a) = r
      es.go(rest, es.eq(s, a, e))

# boundStep
# ---------

def lbs.push.k1(+a: U32, kr: S & U32) -> S & U32:
  (s, +b) = kr
  (s, (a + b : U32))

def lbs.push(s: S, +a: U32, +x: U32) -> S & U32:
  lbs.push.k1(a, lb.at(s, x))

def lbs.go(xs: List<&2, U32>, r: S & U32) -> S & U32:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, a) = r
      lbs.go(rest, lbs.push(s, a, x))

def bs.at.k1(+acc: Bool, kr: S & Bool) -> S & Bool:
  (s, +c) = kr
  (s, Bool.or(acc, c))

def bs.at(pos: Bool, s: S, +acc: Bool, +r: U32, +n: U32, +bl: Blame) -> S & Bool:
  match pos:
    case True{}:
      bs.at.k1(acc, constrain(s, r, CLevel{n, bl}))
    case False{}:
      (s, acc)

def bs.eq.k1(+acc: Bool, +lhs: List<&2, U32>, +rhs: U32, +bl: Blame, kr: S & U32) -> S & Bool:
  (s, +n) = kr
  bs.at(U32.is_lt(0, n), s, acc, rhs, n, bl.derive("sum of summand lower bounds" ++ eq.note(lhs, rhs), bl))

def bs.eq(s: S, +acc: Bool, e: ER) -> S & Bool:
  match e:
    case ER{+lhs, +rhs, +bl}:
      bs.eq.k1(acc, lhs, rhs, bl, lbs.go(lhs, (s, 0)))

def bs.go(xs: List<&2, ER>, r: S & Bool) -> S & Bool:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (s, a) = r
      bs.go(rest, bs.eq(s, a, e))

# The live equations: unboxed totals dropped, unboxed summands filtered.
def lv.keep.k1(+acc: List<&2, ER>, +rhs: U32, +bl: Blame, kr: S & List<&2, U32>) -> S & List<&2, ER>:
  (s, +ls) = kr
  (s, ER{ls, rhs, bl} <> acc)

def lv.keep(z: Bool, s: S, +acc: List<&2, ER>, +lhs: List<&2, U32>, +rhs: U32, +bl: Blame) -> S & List<&2, ER>:
  match z:
    case True{}:
      (s, acc)
    case False{}:
      lv.keep.k1(acc, rhs, bl, nz.list(s, lhs))

def lv.push.k1(+acc: List<&2, ER>, +lhs: List<&2, U32>, +rhs: U32, +bl: Blame, kr: S & Bool) -> S & List<&2, ER>:
  (s, +z) = kr
  lv.keep(z, s, acc, lhs, rhs, bl)

def lv.push(s: S, +acc: List<&2, ER>, e: ER) -> S & List<&2, ER>:
  match e:
    case ER{+lhs, +rhs, +bl}:
      lv.push.k1(acc, lhs, rhs, bl, zero.at(s, rhs))

def lv.go(xs: List<&2, ER>, r: S & List<&2, ER>) -> S & List<&2, ER>:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (s, acc) = r
      lv.go(rest, lv.push(s, acc, e))

def live.of.k1(kr: S & List<&2, ER>) -> S & List<&2, ER>:
  (s, +ys) = kr
  (s, List.reverse(&2, ER, ys))

def live.of(s: S, +xs: List<&2, ER>) -> S & List<&2, ER>:
  live.of.k1(lv.go(xs, (s, [])))

def gr.new(+nv: U32) -> GR:
  +d: Nat = Ln.depth.of(nv)
  GR{Array.new(U32, d, 0), Array.new(U32, d, 0), Array.new(List<&2, U32>, d, []), Array.new(List<&2, U32>, d, []), Array.new(U32, d, 0), Array.new(U32, d, 0), 0, [], [], [], 0, [], [], 1, Array.new(List<&2, String>, d, [])}

def mk.one(g: GR, +x: U32) -> GR:
  gr.vx.set(g, x, 1)

def mk.list(xs: List<&2, U32>, g: GR) -> GR:
  match xs:
    case Nil{}:
      g
    case Con{+x, rest}:
      mk.list(rest, mk.one(g, x))

def mk.eq(e: ER, g: GR) -> GR:
  match e:
    case ER{+lhs, +rhs, +bl}:
      mk.list(lhs, mk.one(g, rhs))

def mk.eqs(xs: List<&2, ER>, g: GR) -> GR:
  match xs:
    case Nil{}:
      g
    case Con{e, rest}:
      mk.eqs(rest, mk.eq(e, g))

# Number the marked numbers in ascending order.
def nb.at.k1(+i: U32, kr: GR & U32) -> GR:
  (g, +k) = kr
  gr.n.set(gr.nd.set(gr.vx.set(g, i, (k + 1 : U32)), k, i), (k + 1 : U32))

def nb.at(m: Bool, g: GR, +i: U32) -> GR:
  match m:
    case True{}:
      nb.at.k1(i, gr.n(g))
    case False{}:
      g

def nb.one.k1(+i: U32, kr: GR & U32) -> GR:
  (g, +m) = kr
  nb.at(U32.is_eq(m, 1), g, i)

def nb.one(g: GR, +i: U32) -> GR:
  nb.one.k1(i, gr.vx(g, i))

def nb.go(n: Nat, +i: U32, g: GR) -> GR:
  match n:
    case 0n:
      g
    case 1n+m:
      nb.go(m, (i + 1 : U32), nb.one(g, i))

def nb.all(+nv: U32, g: GR) -> GR:
  nb.go(U32.to_nat(nv), 0, g)

# Edges, summand to total: IntMap.fromListWith (<>) keeps the last first.
def ed.one.k3(+vl: U32, +vr: U32, kr: GR & List<&2, U32>) -> GR:
  (g, +ks) = kr
  gr.g.set(g, (vl - 1 : U32), (vr - 1 : U32) <> ks)

def ed.one.k2(+vl: U32, kr: GR & U32) -> GR:
  (g, +vr) = kr
  ed.one.k3(vl, vr, gr.g(g, (vl - 1 : U32)))

def ed.one.k1(+r: U32, kr: GR & U32) -> GR:
  (g, +vl) = kr
  ed.one.k2(vl, gr.vx(g, r))

def ed.one(g: GR, +r: U32, +l: U32) -> GR:
  ed.one.k1(r, gr.vx(g, l))

def ed.list(xs: List<&2, U32>, +r: U32, g: GR) -> GR:
  match xs:
    case Nil{}:
      g
    case Con{+l, rest}:
      ed.list(rest, r, ed.one(g, r, l))

def ed.eq(e: ER, g: GR) -> GR:
  match e:
    case ER{+lhs, +rhs, +bl}:
      ed.list(lhs, rhs, g)

def ed.eqs(xs: List<&2, ER>, g: GR) -> GR:
  match xs:
    case Nil{}:
      g
    case Con{e, rest}:
      ed.eqs(rest, ed.eq(e, g))

# transposeG: buildG (accumArray (flip (:))) over reverseE.
def tr.one.k1(+v: U32, +x: U32, kr: GR & List<&2, U32>) -> GR:
  (g, +ks) = kr
  gr.gt.set(g, x, v <> ks)

def tr.one(+v: U32, g: GR, +x: U32) -> GR:
  tr.one.k1(v, x, gr.gt(g, x))

def tr.list(xs: List<&2, U32>, +v: U32, g: GR) -> GR:
  match xs:
    case Nil{}:
      g
    case Con{+x, rest}:
      tr.list(rest, v, tr.one(v, g, x))

def tr.v.k1(+v: U32, kr: GR & List<&2, U32>) -> GR:
  (g, +ks) = kr
  tr.list(ks, v, g)

def tr.v(g: GR, +v: U32) -> GR:
  tr.v.k1(v, gr.g(g, v))

def tr.go(n: Nat, +v: U32, g: GR) -> GR:
  match n:
    case 0n:
      g
    case 1n+m:
      tr.go(m, (v + 1 : U32), tr.v(g, v))

def tr.all.k1(kr: GR & U32) -> GR:
  (g, +n) = kr
  tr.go(U32.to_nat(n), 0, g)

def tr.all(g: GR) -> GR:
  tr.all.k1(gr.n(g))

def df.adj(first: Bool, g: GR, +w: U32) -> GR & List<&2, U32>:
  match first:
    case True{}:
      gr.gt(g, w)
    case False{}:
      gr.g(g, w)

def df.enter.k4(+w: U32, +ks: List<&2, U32>, +cur: List<&2, U32>, kr: GR & List<&2, DFr>) -> GR:
  (g, +st) = kr
  gr.st.set(gr.cur.set(g, w <> cur), DFr{w, ks} <> st)

def df.enter.k3(+w: U32, +ks: List<&2, U32>, kr: GR & List<&2, U32>) -> GR:
  (g, +cur) = kr
  df.enter.k4(w, ks, cur, gr.st(g))

def df.enter.k2(+w: U32, kr: GR & List<&2, U32>) -> GR:
  (g, +ks) = kr
  df.enter.k3(w, ks, gr.cur(g))

def df.enter.k1(+w: U32, kr: GR & U32) -> GR:
  (g, +p) = kr
  df.enter.k2(w, df.adj(U32.is_eq(p, 1), gr.vis.set(g, w, p), w))

def df.enter(g: GR, +w: U32) -> GR:
  df.enter.k1(w, gr.pass(g))

def df.visit(seen: Bool, g: GR, +w: U32) -> DN:
  match seen:
    case True{}:
      DnMore{g}
    case False{}:
      DnMore{df.enter(g, w)}

def df.try.k2(+w: U32, +p: U32, kr: GR & U32) -> DN:
  (g, +m) = kr
  df.visit(U32.is_eq(m, p), g, w)

def df.try.k1(+w: U32, kr: GR & U32) -> DN:
  (g, +p) = kr
  df.try.k2(w, p, gr.vis(g, w))

def df.try(g: GR, +w: U32) -> DN:
  df.try.k1(w, gr.pass(g))

def df.post.k1(+v: U32, kr: GR & List<&2, U32>) -> GR:
  (g, +po) = kr
  gr.po.set(g, v <> po)

def df.post(first: Bool, g: GR, +v: U32) -> GR:
  match first:
    case True{}:
      df.post.k1(v, gr.po(g))
    case False{}:
      g

def df.pop.k1(+v: U32, kr: GR & U32) -> DN:
  (g, +p) = kr
  DnMore{df.post(U32.is_eq(p, 1), g, v)}

def df.pop(g: GR, +v: U32) -> DN:
  df.pop.k1(v, gr.pass(g))

def df.frame(fr: DFr, g: GR, +rest: List<&2, DFr>) -> DN:
  match fr:
    case DFr{+v, +ks}:
      match ks:
        case Nil{}:
          df.pop(gr.st.set(g, rest), v)
        case Con{+w, +ws}:
          df.try(gr.st.set(g, DFr{v, ws} <> rest), w)

# A finished tree of the second pass: a cyclic component if it has two
# members or one with an edge to itself (decode, mentions_itself).
def tf.id.k1(+acc: List<&2, U32>, kr: GR & U32) -> GR & List<&2, U32>:
  (g, +i) = kr
  (g, i <> acc)

def tf.id(g: GR, +acc: List<&2, U32>, +x: U32) -> GR & List<&2, U32>:
  tf.id.k1(acc, gr.nd(g, x))

def tf.ids(xs: List<&2, U32>, r: GR & List<&2, U32>) -> GR & List<&2, U32>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (g, acc) = r
      tf.ids(rest, tf.id(g, acc, x))

def tf.mark(xs: List<&2, U32>, +i: U32, g: GR) -> GR:
  match xs:
    case Nil{}:
      g
    case Con{+x, rest}:
      tf.mark(rest, i, gr.sc.set(g, x, i))

def tf.keep.k3(+cur: List<&2, U32>, +k: U32, +ids: List<&2, U32>, kr: GR & List<&2, List<&2, U32>>) -> GR:
  (g, +trs) = kr
  gr.ntr.set(gr.trs.set(tf.mark(cur, (k + 1 : U32), g), ids <> trs), (k + 1 : U32))

def tf.keep.k2(+cur: List<&2, U32>, +k: U32, kr: GR & List<&2, U32>) -> GR:
  (g, +ids) = kr
  tf.keep.k3(cur, k, ids, gr.trs(g))

def tf.keep.k1(+cur: List<&2, U32>, kr: GR & U32) -> GR:
  (g, +k) = kr
  tf.keep.k2(cur, k, tf.ids(cur, (g, [])))

def tf.keep(cyc: Bool, g: GR, +cur: List<&2, U32>) -> GR:
  match cyc:
    case True{}:
      tf.keep.k1(cur, gr.ntr(g))
    case False{}:
      g

def tf.self.k1(+v: U32, kr: GR & List<&2, U32>) -> GR & Bool:
  (g, +ks) = kr
  (g, u.has(ks, v))

def tf.self(g: GR, +v: U32) -> GR & Bool:
  tf.self.k1(v, gr.g(g, v))

def tf.cyc(cur: List<&2, U32>, g: GR) -> GR & Bool:
  match cur:
    case Nil{}:
      (g, False{})
    case Con{+v, rest}:
      match rest:
        case Nil{}:
          tf.self(g, v)
        case Con{+y, t}:
          (g, True{})

def tf.two.k1(+cur: List<&2, U32>, kr: GR & Bool) -> GR:
  (g, +c) = kr
  tf.keep(c, g, cur)

def tf.two(g: GR, +cur: List<&2, U32>) -> GR:
  tf.two.k1(cur, tf.cyc(cur, g))

def tf.end(first: Bool, g: GR, +cur: List<&2, U32>) -> GR:
  match first:
    case True{}:
      g
    case False{}:
      tf.two(g, cur)

def df.finish.k2(+cur: List<&2, U32>, kr: GR & U32) -> GR:
  (g, +p) = kr
  tf.end(U32.is_eq(p, 1), g, cur)

def df.finish.k1(kr: GR & List<&2, U32>) -> GR:
  (g, +cur) = kr
  df.finish.k2(cur, gr.pass(g))

def df.finish(g: GR) -> GR:
  df.finish.k1(gr.cur.swap(g, []))

def df.top(top: List<&2, U32>, g: GR) -> DN:
  match top:
    case Nil{}:
      DnStop{g}
    case Con{+v, rest}:
      df.try(gr.top.set(g, rest), v)

def df.st.k1(kr: GR & List<&2, U32>) -> DN:
  (g, +top) = kr
  df.top(top, g)

def df.st(st: List<&2, DFr>, g: GR) -> DN:
  match st:
    case Nil{}:
      df.st.k1(gr.top.swap(df.finish(g), []))
    case Con{fr, rest}:
      df.frame(fr, g, rest)

def df.step.k1(kr: GR & List<&2, DFr>) -> DN:
  (g, +st) = kr
  df.st(st, g)

def df.step(g: GR) -> DN:
  df.step.k1(gr.st.swap(g, []))

def df.fin(n: DN) -> GR:
  match n:
    case DnMore{g}:
      g
    case DnStop{g}:
      g

def df.loop(fuel: Nat, n: DN) -> GR:
  match fuel:
    case 0n:
      df.fin(n)
    case 1n+f:
      match n:
        case DnMore{g}:
          df.loop(f, df.step(g))
        case DnStop{g}:
          g

def upto(n: Nat, +k: U32, +acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+m:
      upto(m, (k - 1 : U32), (k - 1 : U32) <> acc)

# scc g = dfs g (reverse (postOrd (transposeG g)))
def scc.two.k1(kr: GR & List<&2, U32>) -> GR:
  (g, +po) = kr
  df.loop(big(), DnMore{gr.pass.set(gr.top.set(g, po), 2)})

def scc.two(g: GR) -> GR:
  scc.two.k1(gr.po.swap(g, []))

def scc.run.k1(kr: GR & U32) -> GR:
  (g, +n) = kr
  scc.two(df.loop(big(), DnMore{gr.top.set(g, upto(U32.to_nat(n), n, []))}))

def scc.run(g: GR) -> GR:
  scc.run.k1(gr.n(g))

def sc.of.k1(kr: GR & U32) -> GR & U32:
  (g, +v) = kr
  gr.sc(g, (v - 1 : U32))

def sc.of(g: GR, +x: U32) -> GR & U32:
  sc.of.k1(gr.vx(g, x))

def pt.add(m: Bool, p: PT, +x: U32) -> PT:
  match m:
    case True{}:
      match p:
        case PT{+mem, +oth}:
          PT{(mem + 1 : U32), oth}
    case False{}:
      match p:
        case PT{+mem, +oth}:
          PT{mem, x <> oth}

def pt.push.k1(+i: U32, +p: PT, +x: U32, kr: GR & U32) -> GR & PT:
  (g, +j) = kr
  (g, pt.add(U32.is_eq(i, j), p, x))

def pt.push(g: GR, +i: U32, +p: PT, +x: U32) -> GR & PT:
  pt.push.k1(i, p, x, sc.of(g, x))

def pt.go(xs: List<&2, U32>, +i: U32, r: GR & PT) -> GR & PT:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (g, p) = r
      pt.go(rest, i, pt.push(g, i, p, x))

# The equations touching each cycle, shown (the note's "through" part),
# in one pass: each live equation's tuple goes to every cycle one of its
# numbers is on, once.
def th.str(lhs: List<&2, U32>, +rhs: U32, bl: Blame) -> String:
  "(" ++ ints.show(lhs) ++ "," ++ U32.show(rhs) ++ "," ++ Sh.string(String.take(bl.why(bl), 24n)) ++ ")"

def th.idx.k1(+acc: List<&2, U32>, kr: GR & U32) -> GR & List<&2, U32>:
  (g, +j) = kr
  (g, Bool.pick(List<&2, U32>, U32.is_eq(j, 0), acc, Ln.u.ins(acc, j)))

def th.idx(g: GR, +acc: List<&2, U32>, +x: U32) -> GR & List<&2, U32>:
  th.idx.k1(acc, sc.of(g, x))

def th.idxs(xs: List<&2, U32>, r: GR & List<&2, U32>) -> GR & List<&2, U32>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (g, acc) = r
      th.idxs(rest, th.idx(g, acc, x))

def th.put.k1(+s: String, +i: U32, kr: GR & List<&2, String>) -> GR:
  (g, +old) = kr
  gr.tl.set(g, i, s <> old)

def th.put(g: GR, +s: String, +i: U32) -> GR:
  th.put.k1(s, i, gr.tl(g, i))

def th.puts(ix: List<&2, U32>, +s: String, g: GR) -> GR:
  match ix:
    case Nil{}:
      g
    case Con{+i, rest}:
      th.puts(rest, s, th.put(g, s, i))

def th.eq.k1(+lhs: List<&2, U32>, +rhs: U32, +bl: Blame, kr: GR & List<&2, U32>) -> GR:
  (g, +ix) = kr
  th.puts(ix, th.str(lhs, rhs, bl), g)

def th.eq(g: GR, e: ER) -> GR:
  match e:
    case ER{+lhs, +rhs, +bl}:
      th.eq.k1(lhs, rhs, bl, th.idxs(rhs <> lhs, (g, [])))

def th.all(xs: List<&2, ER>, g: GR) -> GR:
  match xs:
    case Nil{}:
      g
    case Con{e, rest}:
      th.all(rest, th.eq(g, e))

# A cycle note's placeholder, and the notes themselves.
def cn.ph(+id: U32) -> String:
  SCon{Chr{1}, U32.show(id) ++ SCon{Chr{2}, SNil{}}}

def cn.text(c: CN) -> String:
  match c:
    case CN{+id, +ms, +tl}:
      " [cycle " ++ ints.show(ms) ++ " through " ++ "[" ++ String.join(tl, ",") ++ "]" ++ "]"

def cn.id(c: CN) -> U32:
  match c:
    case CN{+id, +ms, +tl}:
      id

def cn.find(cs: List<&2, CN>, +k: String) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+c, rest}:
      Bool.pick(String, String.eq(U32.show(cn.id(c)), k), cn.text(c), cn.find(rest, k))

def cn.part.at(ps: List<&2, String>, +cs: List<&2, CN>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+k, rest}:
      cn.find(cs, k) ++ String.join(rest, SCon{Chr{2}, SNil{}})

def cn.part(+p: String, +cs: List<&2, CN>) -> String:
  cn.part.at(String.split(p, Chr{2}), cs)

def cn.parts(ps: List<&2, String>, +cs: List<&2, CN>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, rest}:
      cn.part(p, cs) ++ cn.parts(rest, cs)

def cn.first(ps: List<&2, String>, +cs: List<&2, CN>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, rest}:
      p ++ cn.parts(rest, cs)

# A string with its placeholders expanded.
def cn.expand(+s: String, +cs: List<&2, CN>) -> String:
  cn.first(String.split(s, Chr{1}), cs)

def bl.expand(b: Blame, +cs: List<&2, CN>) -> Blame:
  match b:
    case Blame{+loc, +why, +fr}:
      Blame{loc, cn.expand(why, cs), fr}

def bls.expand(bs: List<&2, Blame>, +cs: List<&2, CN>) -> List<&2, Blame>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      bl.expand(b, cs) <> bls.expand(rest, cs)

def err.expand(e: Err, +cs: List<&2, CN>) -> Err:
  match e:
    case BoxConflict{+need, +forbid}:
      BoxConflict{bl.expand(need, cs), bl.expand(forbid, cs)}
    case Unsat{+bs}:
      Unsat{bls.expand(bs, cs)}
    case other:
      other

def pl.pick(two: Bool, g: GR, +acc: List<&2, ZP>, +rhs: U32, +oth: List<&2, U32>, +bl: Blame, +note: String) -> GR & List<&2, ZP>:
  match two:
    case True{}:
      (g, ZP{[rhs], bl.derive("total equal to two of its own summands" ++ note, bl)} <> acc)
    case False{}:
      (g, ZP{List.reverse(&2, U32, oth), bl.derive("summand beside one equal to the total" ++ note, bl)} <> acc)

def pl.k(none: Bool, g: GR, +acc: List<&2, ZP>, +base: U32, +i: U32, +rhs: U32, +oth: List<&2, U32>, +bl: Blame, +two: Bool) -> GR & List<&2, ZP>:
  match none:
    case True{}:
      (g, acc)
    case False{}:
      pl.pick(two, g, acc, rhs, oth, bl, cn.ph(((base + i : U32) - 1 : U32)))

def pl.mem(p: PT, g: GR, +acc: List<&2, ZP>, +base: U32, +i: U32, +rhs: U32, +bl: Blame) -> GR & List<&2, ZP>:
  match p:
    case PT{+mem, +oth}:
      pl.k(U32.is_eq(mem, 0), g, acc, base, i, rhs, oth, bl, U32.is_lt(1, mem))

def pl.at.k1(+acc: List<&2, ZP>, +base: U32, +i: U32, +rhs: U32, +bl: Blame, kr: GR & PT) -> GR & List<&2, ZP>:
  (g, +p) = kr
  pl.mem(p, g, acc, base, i, rhs, bl)

def pl.at(off: Bool, g: GR, +acc: List<&2, ZP>, +base: U32, +i: U32, +lhs: List<&2, U32>, +rhs: U32, +bl: Blame) -> GR & List<&2, ZP>:
  match off:
    case True{}:
      (g, acc)
    case False{}:
      pl.at.k1(acc, base, i, rhs, bl, pt.go(lhs, i, (g, PT{0, []})))

def pl.push.k1(+acc: List<&2, ZP>, +base: U32, +lhs: List<&2, U32>, +rhs: U32, +bl: Blame, kr: GR & U32) -> GR & List<&2, ZP>:
  (g, +i) = kr
  pl.at(U32.is_eq(i, 0), g, acc, base, i, lhs, rhs, bl)

def pl.push(g: GR, +acc: List<&2, ZP>, +base: U32, e: ER) -> GR & List<&2, ZP>:
  match e:
    case ER{+lhs, +rhs, +bl}:
      pl.push.k1(acc, base, lhs, rhs, bl, sc.of(g, rhs))

def pl.go(xs: List<&2, ER>, +base: U32, r: GR & List<&2, ZP>) -> GR & List<&2, ZP>:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (g, acc) = r
      pl.go(rest, base, pl.push(g, acc, base, e))

# The notes of a round's cycles, numbered from base.
def cn.of.k1(+acc: List<&2, CN>, +base: U32, +i: U32, +ms: List<&2, U32>, kr: GR & List<&2, String>) -> GR & List<&2, CN>:
  (g, +tl) = kr
  (g, CN{((base + i : U32) - 1 : U32), ms, List.reverse(&2, String, tl)} <> acc)

def cn.of(g: GR, +acc: List<&2, CN>, +base: U32, +i: U32, +ms: List<&2, U32>) -> GR & List<&2, CN>:
  cn.of.k1(acc, base, i, ms, gr.tl(g, i))

def cn.go(xs: List<&2, List<&2, U32>>, +base: U32, +i: U32, r: GR & List<&2, CN>) -> GR & List<&2, CN>:
  match xs:
    case Nil{}:
      r
    case Con{+ms, rest}:
      (g, acc) = r
      cn.go(rest, base, (i + 1 : U32), cn.of(g, acc, base, i, ms))

# The first half: merge every cyclic component (each member into the
# first's class, in order).
def ub.at(same: Bool, s: S, +a: Bool, +m: U32, +x: U32) -> S & Bool:
  match same:
    case True{}:
      (s, a)
    case False{}:
      (union.b(s, m, x), True{})

def ub.push.k2(+a: Bool, +m: U32, +x: U32, +ra: U32, kr: S & U32) -> S & Bool:
  (s, +rb) = kr
  ub.at(U32.is_eq(ra, rb), s, a, m, x)

def ub.push.k1(+a: Bool, +m: U32, +x: U32, kr: S & U32) -> S & Bool:
  (s, +ra) = kr
  ub.push.k2(a, m, x, ra, find.b(s, x))

def ub.push(s: S, +a: Bool, +m: U32, +x: U32) -> S & Bool:
  ub.push.k1(a, m, x, find.b(s, m))

def ub.go(xs: List<&2, U32>, +m: U32, r: S & Bool) -> S & Bool:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (s, a) = r
      ub.go(rest, m, ub.push(s, a, m, x))

def ub.ms(ms: List<&2, U32>, r: S & Bool) -> S & Bool:
  match ms:
    case Nil{}:
      r
    case Con{+m, rest}:
      ub.go(rest, m, r)

def ub.all(xss: List<&2, List<&2, U32>>, r: S & Bool) -> S & Bool:
  match xss:
    case Nil{}:
      r
    case Con{ms, rest}:
      ub.all(rest, ub.ms(ms, r))

def zp.one(p: ZP, r: S & Bool) -> S & Bool:
  match p:
    case ZP{+xs, +bl}:
      cz.go(xs, bl, r)

def zp.go(xs: List<&2, ZP>, r: S & Bool) -> S & Bool:
  match xs:
    case Nil{}:
      r
    case Con{p, rest}:
      zp.go(rest, zp.one(p, r))

def cy.graph(+nv: U32, +live: List<&2, ER>) -> GR:
  scc.run(tr.all(ed.eqs(live, nb.all(nv, mk.eqs(live, gr.new(nv))))))

def cy.apply.k2(+c1: Bool, kr: S & Bool) -> S & Bool:
  (s, +c2) = kr
  (s, Bool.or(c1, c2))

def cy.apply.k1(+zs: List<&2, ZP>, kr: S & Bool) -> S & Bool:
  (s, +c1) = kr
  cy.apply.k2(c1, zp.go(zs, (s, False{})))

def cy.apply(s: S, +trs: List<&2, List<&2, U32>>, +zs: List<&2, ZP>) -> S & Bool:
  cy.apply.k1(zs, ub.all(trs, (s, False{})))

def cy.notes.k1(+base: U32, +n: U32, +cs: List<&2, CN>, kr: S & List<&2, CN>) -> S:
  (s, +old) = kr
  s.ncn.set(s.cn.set(s, List.append(&2, CN, cs, old)), (base + n : U32))

def cy.notes(s: S, +base: U32, +n: U32, +cs: List<&2, CN>) -> S:
  cy.notes.k1(base, n, cs, s.cn(s))

def u.len.ll(xs: List<&2, List<&2, U32>>) -> U32:
  U32.from_nat(List.length(&2, List<&2, U32>, xs))

def cy.plan.k4(s: S, +base: U32, +trs: List<&2, List<&2, U32>>, +zs: List<&2, ZP>, kr: GR & List<&2, CN>) -> S & Bool:
  (g, +cs) = kr
  cy.apply(cy.notes(s, base, u.len.ll(trs), cs), trs, List.reverse(&2, ZP, zs))

def cy.plan.k3(s: S, +base: U32, +trs: List<&2, List<&2, U32>>, kr: GR & List<&2, ZP>) -> S & Bool:
  (g, +zs) = kr
  cy.plan.k4(s, base, trs, zs, cn.go(trs, base, 1, (g, [])))

def cy.plan.k2(+live: List<&2, ER>, s: S, +base: U32, kr: GR & List<&2, List<&2, U32>>) -> S & Bool:
  (g, +trs0) = kr
  +trs: List<&2, List<&2, U32>> = List.reverse(&2, List<&2, U32>, trs0)
  cy.plan.k3(s, base, trs, pl.go(live, base, (g, [])))

def cy.plan.k1(g: GR, +live: List<&2, ER>, kr: S & U32) -> S & Bool:
  (s, +base) = kr
  cy.plan.k2(live, s, base, gr.trs(th.all(live, g)))

def cy.plan(g: GR, +live: List<&2, ER>, s: S) -> S & Bool:
  cy.plan.k1(g, live, s.ncn(s))

def cycle.step.k2(+live: List<&2, ER>, kr: S & U32) -> S & Bool:
  (s, +nv) = kr
  cy.plan(cy.graph(nv, live), live, s)

def cycle.step.k1(kr: S & List<&2, ER>) -> S & Bool:
  (s, +live) = kr
  cycle.step.k2(live, s.nv(s))

def cycle.step(s: S, +eqs: List<&2, ER>) -> S & Bool:
  cycle.step.k1(live.of(s, eqs))

def ps.next(c: Bool, s: S) -> PSt:
  match c:
    case True{}:
      PsMore{s}
    case False{}:
      PsStop{s}

def ps.round.k6(+c1: Bool, +c2: Bool, +c3: Bool, +c4: Bool, kr: S & Bool) -> PSt:
  (s, +f) = kr
  ps.next(Bool.and(Bool.not(f), Bool.or(Bool.or(c1, c2), Bool.or(c3, c4))), s)

def ps.round.k5(+c1: Bool, +c2: Bool, +c3: Bool, kr: S & Bool) -> PSt:
  (s, +c4) = kr
  ps.round.k6(c1, c2, c3, c4, failed(s))

def ps.round.k4(+eqs: List<&2, ER>, +c1: Bool, +c2: Bool, kr: S & Bool) -> PSt:
  (s, +c3) = kr
  ps.round.k5(c1, c2, c3, bs.go(eqs, (s, False{})))

def ps.round.k3(+eqs: List<&2, ER>, +c1: Bool, kr: S & Bool) -> PSt:
  (s, +c2) = kr
  ps.round.k4(eqs, c1, c2, cycle.step(s, eqs))

def ps.round.k2(+eqs: List<&2, ER>, kr: S & Bool) -> PSt:
  (s, +c1) = kr
  ps.round.k3(eqs, c1, es.go(eqs, (s, False{})))

def ps.round.k1(kr: S & List<&2, ER>) -> PSt:
  (s, +eqs) = kr
  ps.round.k2(eqs, zs.go(eqs, (s, False{})))

def ps.round(s: S) -> PSt:
  ps.round.k1(resolve.eqs(s))

def ps.fin(n: PSt) -> S:
  match n:
    case PsMore{s}:
      fail(s, Internal{"presolve ran out of fuel"})
    case PsStop{s}:
      s

def ps.loop(fuel: Nat, n: PSt) -> S:
  match fuel:
    case 0n:
      ps.fin(n)
    case 1n+f:
      match n:
        case PsMore{s}:
          ps.loop(f, ps.round(s))
        case PsStop{s}:
          s

def presolve.k1(kr: S & Bool) -> S:
  (s, +f) = kr
  ps.loop(big(), ps.next(Bool.not(f), s))

def presolve(s: S) -> S:
  presolve.k1(failed(s))

# solveConstraints
# ----------------

# Leaf multiplicities: how many leaf paths run through each root.
def lc.inc(s: S, p: Array<U32> & U32, +r: U32) -> S & Array<U32>:
  (a, +c) = p
  (s, Array.set(U32, a, r, (c + 1 : U32)))

def lc.add.k1(a: Array<U32>, kr: S & U32) -> S & Array<U32>:
  (s, +r) = kr
  lc.inc(s, Array.get(U32, a, r), r)

def lc.add(s: S, a: Array<U32>, +x: U32) -> S & Array<U32>:
  lc.add.k1(a, find.b(s, x))

def lc.lp.k1(+d: U32, kr: S & Array<U32>) -> S & Array<U32>:
  (s, a) = kr
  lc.add(s, a, d)

def lc.lp(s: S, a: Array<U32>, l: Lp) -> S & Array<U32>:
  match l:
    case Lp{+fr, +base, +d}:
      lc.lp.k1(d, lc.add(s, a, base))

def lc.go(xs: List<&2, Lp>, r: S & Array<U32>) -> S & Array<U32>:
  match xs:
    case Nil{}:
      r
    case Con{l, rest}:
      (s, a) = r
      lc.go(rest, lc.lp(s, a, l))

def sv.w(s: S, g: GR, p: Array<U32> & U32, lb: Array<U32>, w: Array<U32>, +k: U32) -> SV:
  (cnt, +c) = p
  SV{s, g, cnt, lb, Array.set(U32, w, k, (c + 1 : U32))}

def sv.k.k2(+k: U32, cnt: Array<U32>, lb: Array<U32>, w: Array<U32>, g: GR, +id: U32, kr: S & CI) -> SV:
  (s, +c) = kr
  sv.w(s, g, Array.get(U32, cnt, id), Array.set(U32, lb, k, ci.lb(c)), w, k)

def sv.k.k1(+k: U32, s: S, cnt: Array<U32>, lb: Array<U32>, w: Array<U32>, kr: GR & U32) -> SV:
  (g, +id) = kr
  sv.k.k2(k, cnt, lb, w, g, id, s.ci(s, id))

def sv.k(v: SV, +k: U32) -> SV:
  match v:
    case SV{s, g, cnt, lb, w}:
      sv.k.k1(k, s, cnt, lb, w, gr.nd(g, k))

def sv.go(n: Nat, +k: U32, v: SV) -> SV:
  match n:
    case 0n:
      v
    case 1n+m:
      sv.go(m, (k + 1 : U32), sv.k(v, k))

def dn.x.k1(+acc: List<&2, U32>, kr: GR & U32) -> GR & List<&2, U32>:
  (g, +v) = kr
  (g, (v - 1 : U32) <> acc)

def dn.x(g: GR, +acc: List<&2, U32>, +x: U32) -> GR & List<&2, U32>:
  dn.x.k1(acc, gr.vx(g, x))

def dn.go(xs: List<&2, U32>, r: GR & List<&2, U32>) -> GR & List<&2, U32>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (g, acc) = r
      dn.go(rest, dn.x(g, acc, x))

def dn.list.k1(kr: GR & List<&2, U32>) -> GR & List<&2, U32>:
  (g, +ys) = kr
  (g, List.reverse(&2, U32, ys))

def dn.list(g: GR, +xs: List<&2, U32>) -> GR & List<&2, U32>:
  dn.list.k1(dn.go(xs, (g, [])))

def dn.eq.k2(+acc: List<&2, Ln.Eq>, +ls: List<&2, U32>, kr: GR & U32) -> GR & List<&2, Ln.Eq>:
  (g, +v) = kr
  (g, Ln.Eq{ls, (v - 1 : U32)} <> acc)

def dn.eq.k1(+acc: List<&2, Ln.Eq>, +rhs: U32, kr: GR & List<&2, U32>) -> GR & List<&2, Ln.Eq>:
  (g, +ls) = kr
  dn.eq.k2(acc, ls, gr.vx(g, rhs))

def dn.eq(g: GR, +acc: List<&2, Ln.Eq>, e: ER) -> GR & List<&2, Ln.Eq>:
  match e:
    case ER{+lhs, +rhs, +bl}:
      dn.eq.k1(acc, rhs, dn.list(g, lhs))

def dn.go.eqs(xs: List<&2, ER>, r: GR & List<&2, Ln.Eq>) -> GR & List<&2, Ln.Eq>:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (g, acc) = r
      dn.go.eqs(rest, dn.eq(g, acc, e))

def dn.eqs.k1(kr: GR & List<&2, Ln.Eq>) -> GR & List<&2, Ln.Eq>:
  (g, +ys) = kr
  (g, List.reverse(&2, Ln.Eq, ys))

def dn.eqs(g: GR, +xs: List<&2, ER>) -> GR & List<&2, Ln.Eq>:
  dn.eqs.k1(dn.go.eqs(xs, (g, [])))

# The blames of the equations a failed solve names.
def us.got(m: Maybe<&2, ER>) -> Blame:
  match m:
    case Some{e}:
      match e:
        case ER{+lhs, +rhs, +bl}:
          bl.derive("[eq " ++ ints.show(lhs) ++ " = " ++ U32.show(rhs) ++ "]", bl)
    case None{}:
      blame(gen("EAL"), "an equation the solver named is missing")

def us.blames(xs: List<&2, U32>, +live: List<&2, ER>) -> List<&2, Blame>:
  match xs:
    case Nil{}:
      []
    case Con{+i, rest}:
      us.got(List.get(&2, ER, live, U32.to_nat(i))) <> us.blames(rest, live)

# Every root's value: zero if unboxed, else its lower bound, or the
# solver's value for a live one.
def vl.one.k1(a: Array<U32>, +i: U32, kr: S & CI) -> S & Array<U32>:
  (s, +c) = kr
  (s, Array.set(U32, a, i, Bool.pick(U32, ci.zero(c), 0, ci.lb(c))))

def vl.one(s: S, a: Array<U32>, +i: U32) -> S & Array<U32>:
  vl.one.k1(a, i, s.ci(s, i))

def vl.base(n: Nat, +i: U32, r: S & Array<U32>) -> S & Array<U32>:
  match n:
    case 0n:
      r
    case 1n+m:
      (s, a) = r
      vl.base(m, (i + 1 : U32), vl.one(s, a, i))

def vl.put.k1(a: Array<U32>, +x: Nat, kr: GR & U32) -> GR & Array<U32>:
  (g, +id) = kr
  (g, Array.set(U32, a, id, U32.from_nat(x)))

def vl.put(g: GR, a: Array<U32>, +k: U32, +x: Nat) -> GR & Array<U32>:
  vl.put.k1(a, x, gr.nd(g, k))

def vl.dense(xs: List<&2, Nat>, +k: U32, r: GR & Array<U32>) -> GR & Array<U32>:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (g, a) = r
      vl.dense(rest, (k + 1 : U32), vl.put(g, a, k, x))

# The check that the assignment satisfies every equation.
def vf.add.k1(+t: U32, kr: Array<U32> & U32) -> Array<U32> & U32:
  (a, +v) = kr
  (a, (t + v : U32))

def vf.add(a: Array<U32>, +t: U32, +x: U32) -> Array<U32> & U32:
  vf.add.k1(t, Array.get(U32, a, x))

def vf.sum(xs: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & U32:
  match xs:
    case Nil{}:
      r
    case Con{+x, rest}:
      (a, t) = r
      vf.sum(rest, vf.add(a, t, x))

def vf.pick(ok: Bool, +bad: Maybe<&2, Blame>, +bl: Blame) -> Maybe<&2, Blame>:
  match ok:
    case True{}:
      bad
    case False{}:
      match bad:
        case Some{+b}:
          Some{b}
        case None{}:
          Some{bl}

def vf.chk.k2(+bad: Maybe<&2, Blame>, +bl: Blame, +t: U32, kr: Array<U32> & U32) -> Array<U32> & Maybe<&2, Blame>:
  (a, +v) = kr
  (a, vf.pick(U32.is_eq(t, v), bad, bl))

def vf.chk.k1(+bad: Maybe<&2, Blame>, +rhs: U32, +bl: Blame, kr: Array<U32> & U32) -> Array<U32> & Maybe<&2, Blame>:
  (a, +t) = kr
  vf.chk.k2(bad, bl, t, Array.get(U32, a, rhs))

def vf.chk(a: Array<U32>, +bad: Maybe<&2, Blame>, e: ER) -> Array<U32> & Maybe<&2, Blame>:
  match e:
    case ER{+lhs, +rhs, +bl}:
      vf.chk.k1(bad, rhs, bl, vf.sum(lhs, (a, 0)))

def vf.go(xs: List<&2, ER>, r: Array<U32> & Maybe<&2, Blame>) -> Array<U32> & Maybe<&2, Blame>:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (a, bad) = r
      vf.go(rest, vf.chk(a, bad, e))

def vf.fail(m: Maybe<&2, Blame>, s: S) -> S:
  match m:
    case None{}:
      s
    case Some{+b}:
      fail(s, Internal{"solver assignment violates an equation: " ++ blame.render(b)})

def sc.done.k3(s: S, kr: Array<U32> & Maybe<&2, Blame>) -> S & Array<U32>:
  (a, +bad) = kr
  (vf.fail(bad, s), a)

def sc.done.k2(+eqs: List<&2, ER>, s: S, kr: GR & Array<U32>) -> S & Array<U32>:
  (g, a) = kr
  sc.done.k3(s, vf.go(eqs, (a, None{})))

def sc.done.k1(g: GR, +eqs: List<&2, ER>, +xs: List<&2, Nat>, kr: S & Array<U32>) -> S & Array<U32>:
  (s, a) = kr
  sc.done.k2(eqs, s, vl.dense(xs, 0, (g, a)))

def sc.done(s: S, g: GR, +nv: U32, +eqs: List<&2, ER>, +xs: List<&2, Nat>) -> S & Array<U32>:
  sc.done.k1(g, eqs, xs, vl.base(U32.to_nat(nv), 0, (s, Array.new(U32, Ln.depth.of(nv), 0))))

def sc.res(r: Result<&2, &2, List<&2, U32>, List<&2, Nat>>, s: S, g: GR, +nv: U32, +eqs: List<&2, ER>, +live: List<&2, ER>) -> S & Array<U32>:
  match r:
    case Fail{+from}:
      (fail(s, Unsat{us.blames(from, live)}), Array.new(U32, 1n, 0))
    case Done{+xs}:
      sc.done(s, g, nv, eqs, xs)

def sc.solve.k1(+n: U32, +nv: U32, +eqs: List<&2, ER>, +live: List<&2, ER>, s: S, lb: Array<U32>, w: Array<U32>, kr: GR & List<&2, Ln.Eq>) -> S & Array<U32>:
  (g, +des) = kr
  sc.res(Ln.solve(n, lb, w, des), s, g, nv, eqs, live)

def sc.solve(v: SV, +n: U32, +nv: U32, +eqs: List<&2, ER>, +live: List<&2, ER>) -> S & Array<U32>:
  match v:
    case SV{s, g, cnt, lb, w}:
      sc.solve.k1(n, nv, eqs, live, s, lb, w, dn.eqs(g, live))

def sc.prep.k1(s: S, cnt: Array<U32>, +nv: U32, +eqs: List<&2, ER>, +live: List<&2, ER>, kr: GR & U32) -> S & Array<U32>:
  (g, +n) = kr
  +d: Nat = Ln.depth.of(n)
  sc.solve(sv.go(U32.to_nat(n), 0, SV{s, g, cnt, Array.new(U32, d, 0), Array.new(U32, d, 0)}), n, nv, eqs, live)

def sc.prep(s: S, g: GR, cnt: Array<U32>, +nv: U32, +eqs: List<&2, ER>, +live: List<&2, ER>) -> S & Array<U32>:
  sc.prep.k1(s, cnt, nv, eqs, live, gr.n(g))

# solveConstraints (presolve has run): every root's value, by number.
def solve.cs.k5(+eqs: List<&2, ER>, +live: List<&2, ER>, +nv: U32, kr: S & Array<U32>) -> S & Array<U32>:
  (s, cnt) = kr
  sc.prep(s, nb.all(nv, mk.eqs(live, gr.new(nv))), cnt, nv, eqs, live)

def solve.cs.k4(+eqs: List<&2, ER>, +live: List<&2, ER>, +nv: U32, kr: S & List<&2, Lp>) -> S & Array<U32>:
  (s, +lfs) = kr
  solve.cs.k5(eqs, live, nv, lc.go(lfs, (s, Array.new(U32, Ln.depth.of(nv), 0))))

def solve.cs.k3(+eqs: List<&2, ER>, +live: List<&2, ER>, kr: S & U32) -> S & Array<U32>:
  (s, +nv) = kr
  solve.cs.k4(eqs, live, nv, s.lfs(s))

def solve.cs.k2(+eqs: List<&2, ER>, kr: S & List<&2, ER>) -> S & Array<U32>:
  (s, +live) = kr
  solve.cs.k3(eqs, live, s.nv(s))

def solve.cs.k1(kr: S & List<&2, ER>) -> S & Array<U32>:
  (s, +eqs) = kr
  solve.cs.k2(eqs, live.of(s, eqs))

def solve.cs(s: S) -> S & Array<U32>:
  solve.cs.k1(resolve.eqs(s))

def ms.got(m: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case Some{+x}:
      x
    case None{}:
      []

# The program
# -----------

def rk.go(ks: List<&2, String>, +i: U32, acc: Map<&2, U32>) -> Map<&2, U32>:
  match ks:
    case Nil{}:
      acc
    case Con{k, rest}:
      rk.go(rest, (i + 1 : U32), Map.set(&2, U32, acc, k, i))

# Each body's rank: its place in hash order.
def ranks(+bodies: Map<&2, Lf.Body>) -> Map<&2, U32>:
  rk.go(Map.keys(&2, Lf.Body, bodies), 0, Map.new(&2, U32))

def bd.dummy() -> Bd:
  Bd{"", 0, False{}, AZero{Lc.Unknown{}}}

# A chain link: the body Telomare.Machine numbers unsizedStepMrfb (-8).
def bd.put(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>, +rk: Map<&2, U32>, +i: U32, a: Array<Bd>) -> Array<Bd>:
  match kvs:
    case Nil{}:
      a
    case Con{kv, rest}:
      match kv:
        case (+h, b):
          match b:
            case Lf.Body{+fi, +body}:
              bd.put(rest, rk, (i + 1 : U32), Array.set(Bd, a, i, Bd{h, fi, U32.is_eq(fi, 4294967288), to.a(body, rk)}))

# The state over a lifted program's bodies, and its main term.
def prog.state(t: Lf.Lifted, +uni: Bool) -> S & A:
  match t:
    case Lf.Lifted{+bodies, +main}:
      +rk: Map<&2, U32> = ranks(bodies)
      +n: U32 = U32.from_nat(Map.size(&2, Lf.Body, bodies))
      (st.new(bd.put(Map.to_list(&2, Lf.Body, bodies), rk, 0, Array.new(Bd, Ln.depth.of(n), bd.dummy())), n, uni), to.a(main, rk))

def vm.reg.k1(+w: U32, +env: Sg, kr: S & Sg) -> S:
  (s, +so) = kr
  ap.new(s, Ap{w, env, so, gen("virtual application of main to input"), []})

def vm.reg(s: S, +w: U32, +env: Sg) -> S:
  vm.reg.k1(w, env, fresh.sig(s))

def vm.bare.k1(+w: U32, kr: S & U32) -> S:
  (s, +ib) = kr
  vm.reg(s, w, Sg{ib, ty.data()})

def vm.bare(s: S, +w: U32) -> S:
  vm.bare.k1(w, fresh(s))

def vm.wrap.k3(+w: U32, +eb: U32, kr: S & U32) -> S:
  (s, +pt) = kr
  vm.reg(s, w, Sg{eb, pt})

def vm.wrap.k2(+w: U32, +cap: Sg, +ib: U32, kr: S & U32) -> S:
  (s, +eb) = kr
  vm.wrap.k3(w, eb, pair.new(s, Sg{ib, ty.data()}, cap))

def vm.wrap.k1(+w: U32, +cap: Sg, kr: S & U32) -> S:
  (s, +ib) = kr
  vm.wrap.k2(w, cap, ib, fresh(s))

def vm.wrap(s: S, +w: U32, +cap: Sg) -> S:
  vm.wrap.k1(w, cap, fresh(s))

def vm.code(k: K, s: S, +w: U32, +cap: Sg) -> S:
  match k:
    case KCode{}:
      vm.wrap(s, w, cap)
    case KCap{}:
      vm.wrap(s, w, cap)
    case other:
      s

def vm.walk.k1(+cap: Sg, kr: S & U32) -> S:
  (s, +w) = kr
  vm.code(kind(w), s, w, cap)

def vm.walk(s: S, +at: U32, +cap: Sg) -> S:
  vm.walk.k1(cap, walk(s, at))

def vm.pair(ps: PS, s: S) -> S:
  match ps:
    case PS{+a, +cap}:
      vm.walk(s, sg.t(a), cap)

def vm.kind.k1(kr: S & PS) -> S:
  (s, +ps) = kr
  vm.pair(ps, s)

def vm.kind(k: K, s: S, +w: U32) -> S:
  match k:
    case KPair{}:
      vm.kind.k1(pair.get(s, w))
    case KCode{}:
      vm.bare(s, w)
    case KCap{}:
      vm.bare(s, w)
    case other:
      s

# virtualMainApply: one application of the program's value to its input,
# registered against its resolved shape.
def virtual.main.k1(kr: S & U32) -> S:
  (s, +w) = kr
  vm.kind(kind(w), s, w)

def virtual.main(s: S, +sg: Sg) -> S:
  match sg:
    case Sg{+b, +t}:
      virtual.main.k1(walk(s, t))

def vm.at(go: Bool, s: S, +sg: Sg) -> S:
  match go:
    case True{}:
      resolve.applies(virtual.main(s, sg))
    case False{}:
      s

def wt.res(w: WT) -> Sg:
  match w:
    case WT{+benv, +tenv, +res}:
      res

def wt.benv(w: WT) -> U32:
  match w:
    case WT{+benv, +tenv, +res}:
      benv

# walkTop: walk, dispatch, (the virtual application,) presolve.
def walk.top.k7(+vmain: Bool, +benv: U32, +tenv: U32, kr: S & R) -> S & WT:
  (s, +r) = kr
  +res: Sg = r.sg(r)
  (presolve(vm.at(vmain, resolve.applies(s), res)), WT{benv, tenv, res})

def walk.top.k6(+vmain: Bool, +term: A, +benv: U32, +tenv: U32, +ctx: Ctx, kr: S & U32) -> S & WT:
  (s, +rb) = kr
  walk.top.k7(vmain, benv, tenv, walk.view(s, ctx, rb, term))

def walk.top.k5(+vmain: Bool, +term: A, +benv: U32, +tenv: U32, kr: S & Ctx) -> S & WT:
  (s, +ctx) = kr
  walk.top.k6(vmain, term, benv, tenv, ctx, forced.zero(s, blame(gen("EAL root"), "the program's root sits at depth zero")))

def walk.top.k4(+vmain: Bool, +what: String, +term: A, +unit: U32, +benv: U32, kr: S & U32) -> S & WT:
  (s, +tenv) = kr
  walk.top.k5(vmain, term, benv, tenv, frame.context(s, unit, 0, what, benv, tenv, term))

def walk.top.k3(+vmain: Bool, +what: String, +term: A, +unit: U32, kr: S & U32) -> S & WT:
  (s, +benv) = kr
  walk.top.k4(vmain, what, term, unit, benv, fresh.tau(s))

def walk.top.k2(+vmain: Bool, +what: String, +term: A, +unit: U32, kr: S & Bool) -> S & WT:
  (s, +c0) = kr
  walk.top.k3(vmain, what, term, unit, fresh(s))

def walk.top.k1(+vmain: Bool, +what: String, +term: A, kr: S & U32) -> S & WT:
  (s, +unit) = kr
  walk.top.k2(vmain, what, term, unit, constrain(s, unit, CLevel{1, blame(gen("EAL unit"), "the unit box count")}))

def walk.top(s: S, +vmain: Bool, +what: String, +term: A) -> S & WT:
  walk.top.k1(vmain, what, term, fresh(s))

def vs.got(s: S, p: Array<U32> & U32) -> VS & U32:
  (a, +x) = p
  (VS{s, a}, x)

def vs.val.k1(a: Array<U32>, kr: S & U32) -> VS & U32:
  (s, +r) = kr
  vs.got(s, Array.get(U32, a, r))

def vs.val(v: VS, +b: U32) -> VS & U32:
  match v:
    case VS{s, a}:
      vs.val.k1(a, find.b(s, b))

def u.max(+a: U32, +b: U32) -> U32:
  Bool.pick(U32, U32.is_lt(a, b), b, a)

# A map keyed by FunctionIndex in its (signed) order: the key is the index
# offset by 2^31, in ten decimal digits.
def fi.key(+fi: U32) -> String:
  +d: String = U32.show((fi + 2147483648 : U32))
  String.drop("0000000000" ++ d, String.length(d))

def fm.got(r: Map<&2, KV> & KV, +k: String, +fi: U32, +x: U32) -> Map<&2, KV>:
  (m, +old) = r
  match old:
    case KV{+ok, +ov}:
      Map.set(&2, KV, m, k, KV{fi, u.max(ov, x)})

def fm.at(known: Bool, m: Map<&2, KV>, +k: String, +fi: U32, +x: U32) -> Map<&2, KV>:
  match known:
    case True{}:
      fm.got(Map.get(KV, KV{fi, 0}, m, k), k, fi, x)
    case False{}:
      Map.set(&2, KV, m, k, KV{fi, x})

def fm.has(r: Map<&2, KV> & Bool, +k: String, +fi: U32, +x: U32) -> Map<&2, KV>:
  (m, +known) = r
  fm.at(known, m, k, fi, x)

# Map.fromListWith max, one entry.
def fm.max(m: Map<&2, KV>, +fi: U32, +x: U32) -> Map<&2, KV>:
  +k: String = fi.key(fi)
  fm.has(Map.has(&2, KV, m, k), k, fi, x)

def kv.vals(xs: List<&2, Sigma<&2, &2, String, _ => KV>>) -> List<&2, KV>:
  match xs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          v <> kv.vals(rest)

def fm.list(m: Map<&2, KV>) -> List<&2, KV>:
  kv.vals(Map.to_list(&2, KV, m))

# The defers' bangs.
def df.val.k1(m: Map<&2, KV>, +fi: U32, kr: VS & U32) -> VS & Map<&2, KV>:
  (v, +x) = kr
  (v, fm.max(m, fi, x))

def df.val(v: VS, m: Map<&2, KV>, d: Df) -> VS & Map<&2, KV>:
  match d:
    case Df{+fi, +b}:
      df.val.k1(m, fi, vs.val(v, b))

def df.vals(xs: List<&2, Df>, r: VS & Map<&2, KV>) -> VS & Map<&2, KV>:
  match xs:
    case Nil{}:
      r
    case Con{d, rest}:
      (v, m) = r
      df.vals(rest, df.val(v, m, d))

def ld.lvl(main: Bool, m: Map<&2, KV>, +fr: U32, +x: U32) -> Map<&2, KV>:
  match main:
    case True{}:
      m
    case False{}:
      fm.max(m, (fr - 1 : U32), x)

def ld.leaf.k2(+mx: U32, m: Map<&2, KV>, +fr: U32, +x1: U32, kr: VS & U32) -> LD:
  (v, +x2) = kr
  LD{v, u.max(mx, (x1 + x2 : U32)), ld.lvl(U32.is_eq(fr, 0), m, fr, x2)}

def ld.leaf.k1(+mx: U32, m: Map<&2, KV>, +fr: U32, +d: U32, kr: VS & U32) -> LD:
  (v, +x1) = kr
  ld.leaf.k2(mx, m, fr, x1, vs.val(v, d))

def ld.leaf(l: LD, p: Lp) -> LD:
  match l:
    case LD{v, +mx, m}:
      match p:
        case Lp{+fr, +base, +d}:
          ld.leaf.k1(mx, m, fr, d, vs.val(v, base))

def ld.go(xs: List<&2, Lp>, l: LD) -> LD:
  match xs:
    case Nil{}:
      l
    case Con{p, rest}:
      ld.go(rest, ld.leaf(l, p))

def sh.join(vs: List<&2, Lf.Shape>) -> List<&2, Lf.Shape>:
  match vs:
    case Con{+b, r1}:
      match r1:
        case Con{+a, +r2}:
          Lf.CapPair{a, b} <> r2
        case Nil{}:
          [b]
    case Nil{}:
      []

def sh.pair.at(ps: PS, s: S, +js: List<&2, SJ>, +vs: List<&2, Lf.Shape>) -> SQ:
  match ps:
    case PS{+a, +b}:
      SqGo{s, SjTau{sg.t(a)} <> SjTau{sg.t(b)} <> SjPair{} <> js, vs}

def sh.pair.k1(+js: List<&2, SJ>, +vs: List<&2, Lf.Shape>, kr: S & PS) -> SQ:
  (s, +ps) = kr
  sh.pair.at(ps, s, js, vs)

def sh.pair(s: S, +w: U32, +js: List<&2, SJ>, +vs: List<&2, Lf.Shape>) -> SQ:
  sh.pair.k1(js, vs, pair.get(s, w))

def sh.tau.k1(+js: List<&2, SJ>, +vs: List<&2, Lf.Shape>, kr: S & U32) -> SQ:
  (s, +w) = kr
  SqGo{s, SjWalked{kind(w), w} <> js, vs}

def sh.tau(s: S, +t: U32, +js: List<&2, SJ>, +vs: List<&2, Lf.Shape>) -> SQ:
  sh.tau.k1(js, vs, walk(s, t))

def sh.step(j: SJ, s: S, +js: List<&2, SJ>, +vs: List<&2, Lf.Shape>) -> SQ:
  match j:
    case SjTau{+t}:
      sh.tau(s, t, js, vs)
    case SjWalked{k, +w}:
      match k:
        case KData{}:
          SqGo{s, js, Lf.CapData{} <> vs}
        case KPair{}:
          sh.pair(s, w, js, vs)
        case KCode{}:
          SqGo{s, js, Lf.CapCode{} <> vs}
        case other:
          SqGo{s, js, Lf.CapOther{} <> vs}
    case SjPair{}:
      SqGo{s, js, sh.join(vs)}

def sh.top(vs: List<&2, Lf.Shape>, s: S) -> SQ:
  match vs:
    case Con{+v, rest}:
      SqEnd{s, v}
    case Nil{}:
      SqEnd{s, Lf.CapOther{}}

def sh.next(js: List<&2, SJ>, s: S, +vs: List<&2, Lf.Shape>) -> SQ:
  match js:
    case Con{j, rest}:
      sh.step(j, s, rest, vs)
    case Nil{}:
      sh.top(vs, s)

def sh.fin(q: SQ) -> S & Lf.Shape:
  match q:
    case SqGo{s, +js, +vs}:
      (s, Lf.CapOther{})
    case SqEnd{s, +v}:
      (s, v)

def sh.loop(fuel: Nat, q: SQ) -> S & Lf.Shape:
  match fuel:
    case 0n:
      sh.fin(q)
    case 1n+f:
      match q:
        case SqGo{s, +js, +vs}:
          sh.loop(f, sh.next(js, s, vs))
        case SqEnd{s, +v}:
          (s, v)

def shape.of(s: S, +t: U32) -> S & Lf.Shape:
  sh.loop(big(), SqGo{s, [SjTau{t}], []})

# meetShape
def all.data(s: Lf.Shape) -> Bool:
  match s:
    case Lf.CapData{}:
      True{}
    case Lf.CapPair{+a, +b}:
      Bool.and(all.data(a), all.data(b))
    case other:
      False{}

def meet.flat(data: Bool) -> Lf.Shape:
  match data:
    case True{}:
      Lf.CapData{}
    case False{}:
      Lf.CapOther{}

def meet(a: Lf.Shape, b: Lf.Shape) -> Lf.Shape:
  match a b:
    case Lf.CapPair{a1, a2} Lf.CapPair{b1, b2}:
      Lf.CapPair{meet(a1, b1), meet(a2, b2)}
    case Lf.CapCode{} Lf.CapCode{}:
      Lf.CapCode{}
    case +x +y:
      meet.flat(Bool.and(all.data(x), all.data(y)))

def sm.got(r: Map<&2, Lf.Shape> & Lf.Shape, +h: String, +x: Lf.Shape) -> Map<&2, Lf.Shape>:
  (m, +old) = r
  Map.set(&2, Lf.Shape, m, h, meet(x, old))

def sm.at(known: Bool, m: Map<&2, Lf.Shape>, +h: String, +x: Lf.Shape) -> Map<&2, Lf.Shape>:
  match known:
    case True{}:
      sm.got(Map.get(Lf.Shape, Lf.CapOther{}, m, h), h, x)
    case False{}:
      Map.set(&2, Lf.Shape, m, h, x)

def sm.has(r: Map<&2, Lf.Shape> & Bool, +h: String, +x: Lf.Shape) -> Map<&2, Lf.Shape>:
  (m, +known) = r
  sm.at(known, m, h, x)

# One capture's shape, met into its hash's.
def gs.add.k2(+m: Map<&2, Lf.Shape>, +b: Bd, kr: S & Lf.Shape) -> S & Map<&2, Lf.Shape>:
  (s, +x) = kr
  +h: String = bd.h(b)
  (s, sm.has(Map.has(&2, Lf.Shape, m, h), h, x))

def gs.add.k1(+m: Map<&2, Lf.Shape>, +ct: U32, kr: S & Bd) -> S & Map<&2, Lf.Shape>:
  (s, +b) = kr
  gs.add.k2(m, b, shape.of(s, ct))

def gs.add(s: S, +m: Map<&2, Lf.Shape>, +tag: U32, +ct: U32) -> S & Map<&2, Lf.Shape>:
  gs.add.k1(m, ct, s.bd(s, tag))

def gs.cap(code: Bool, s: S, +m: Map<&2, Lf.Shape>, +tag: U32, +cap: Maybe<&2, Sg>) -> S & Map<&2, Lf.Shape>:
  match code:
    case True{}:
      match cap:
        case Some{+c}:
          gs.add(s, m, tag, sg.t(c))
        case None{}:
          (s, m)
    case False{}:
      (s, m)

def gs.te(s: S, +m: Map<&2, Lf.Shape>, e: TE) -> S & Map<&2, Lf.Shape>:
  match e:
    case TE{+tag, +cap, +ifc}:
      gs.cap(U32.is_lt(tag, tag.gate()), s, m, tag, cap)

def gs.tes(xs: List<&2, TE>, r: S & Map<&2, Lf.Shape>) -> S & Map<&2, Lf.Shape>:
  match xs:
    case Nil{}:
      r
    case Con{e, rest}:
      (s, m) = r
      gs.tes(rest, gs.te(s, m, e))

def gs.one.k1(+m: Map<&2, Lf.Shape>, kr: S & List<&2, TE>) -> S & Map<&2, Lf.Shape>:
  (s, +ts) = kr
  gs.tes(ts, (s, m))

def gs.one(s: S, +m: Map<&2, Lf.Shape>, +i: U32) -> S & Map<&2, Lf.Shape>:
  gs.one.k1(m, s.ts(s, i))

def gs.go(n: Nat, +i: U32, r: S & Map<&2, Lf.Shape>) -> S & Map<&2, Lf.Shape>:
  match n:
    case 0n:
      r
    case 1n+k:
      (s, m) = r
      gs.go(k, (i + 1 : U32), gs.one(s, m, i))

# groundCaptureShapes: every package class's captures, met per hash.
def ground.shapes.k1(kr: S & U32) -> S & Map<&2, Lf.Shape>:
  (s, +nv) = kr
  gs.go(U32.to_nat(nv), 0, (s, Map.new(&2, Lf.Shape)))

def ground.shapes(s: S) -> S & Map<&2, Lf.Shape>:
  ground.shapes.k1(s.nv(s))

def gm.ld.k2(+top: U32, +defers: List<&2, KV>, +mx: U32, m: Map<&2, KV>, +shapes: Map<&2, Lf.Shape>, kr: S & Lf.Shape) -> S & MR:
  (s, +ms) = kr
  (s, MR{top, defers, mx, ms, shapes, fm.list(m)})

def gm.ld.k1(+top: U32, +defers: List<&2, KV>, +res: Sg, +mx: U32, m: Map<&2, KV>, kr: S & Map<&2, Lf.Shape>) -> S & MR:
  (s, +shapes) = kr
  gm.ld.k2(top, defers, mx, m, shapes, shape.of(s, sg.t(res)))

def gm.ld(l: LD, +top: U32, +defers: List<&2, KV>, +res: Sg) -> S & MR:
  match l:
    case LD{v, +mx, m}:
      match v:
        case VS{s, a}:
          gm.ld.k1(top, defers, res, mx, m, ground.shapes(s))

def gm.dfs.k1(+top: U32, +lfs: List<&2, Lp>, +res: Sg, kr: VS & Map<&2, KV>) -> S & MR:
  (v, +dm) = kr
  gm.ld(ld.go(lfs, LD{v, 0, Map.new(&2, KV)}), top, fm.list(dm), res)

def gm.dfs(v: VS, +top: U32, +lfs: List<&2, Lp>, +res: Sg, +dfs: List<&2, Df>) -> S & MR:
  gm.dfs.k1(top, lfs, res, df.vals(dfs, (v, Map.new(&2, KV))))

def gm.vals.k3(+w: WT, +dfs: List<&2, Df>, +lfs: List<&2, Lp>, kr: VS & U32) -> S & MR:
  (v, +top) = kr
  gm.dfs(v, top, lfs, wt.res(w), dfs)

def gm.vals.k2(a: Array<U32>, +w: WT, +dfs: List<&2, Df>, kr: S & List<&2, Lp>) -> S & MR:
  (s, +lfs) = kr
  gm.vals.k3(w, dfs, lfs, vs.val(VS{s, a}, wt.benv(w)))

def gm.vals.k1(a: Array<U32>, +w: WT, kr: S & List<&2, Df>) -> S & MR:
  (s, +dfs) = kr
  gm.vals.k2(a, w, dfs, s.lfs(s))

def gm.vals(s: S, a: Array<U32>, +w: WT) -> S & MR:
  gm.vals.k1(a, w, s.dfs(s))

def mr.none() -> MR:
  MR{0, [], 0, Lf.CapOther{}, Map.new(&2, Lf.Shape), []}

def gm.solved(bad: Bool, s: S, a: Array<U32>, +w: WT) -> S & MR:
  match bad:
    case True{}:
      (s, mr.none())
    case False{}:
      gm.vals(s, a, w)

def gm.solve.k2(+w: WT, a: Array<U32>, kr: S & Bool) -> S & MR:
  (s, +bad) = kr
  gm.solved(bad, s, a, w)

def gm.solve.k1(+w: WT, kr: S & Array<U32>) -> S & MR:
  (s, a) = kr
  gm.solve.k2(w, a, failed(s))

def gm.solve(s: S, +w: WT) -> S & MR:
  gm.solve.k1(w, solve.cs(s))

def gm.walked(bad: Bool, s: S, +w: WT) -> S & MR:
  match bad:
    case True{}:
      (s, mr.none())
    case False{}:
      gm.solve(s, w)

# goMain: analyzeTopWith True "program input", then the result.
def go.main.k2(+w: WT, kr: S & Bool) -> S & MR:
  (s, +bad) = kr
  gm.walked(bad, s, w)

def go.main.k1(kr: S & WT) -> S & MR:
  (s, +w) = kr
  go.main.k2(w, failed(s))

def go.main(s: S, +term: A) -> S & MR:
  go.main.k1(walk.top(s, True{}, "program input", term))

def rm.pick(e: Maybe<&2, Err>, +m: MR, +cs: List<&2, CN>) -> Result<&2, &2, Err, MR>:
  match e:
    case Some{+x}:
      Fail{err.expand(x, cs)}
    case None{}:
      Done{m}

def rm.err.k2(+m: MR, +e: Maybe<&2, Err>, kr: S & List<&2, CN>) -> Result<&2, &2, Err, MR>:
  (s, +cs) = kr
  rm.pick(e, m, cs)

def rm.err.k1(+m: MR, kr: S & Maybe<&2, Err>) -> Result<&2, &2, Err, MR>:
  (s, +e) = kr
  rm.err.k2(m, e, s.cn(s))

def rm.err(s: S, +m: MR) -> Result<&2, &2, Err, MR>:
  rm.err.k1(m, s.err(s))

def rm.got(r: S & MR) -> Result<&2, &2, Err, MR>:
  (s, +m) = r
  rm.err(s, m)

def rm.state(p: S & A) -> S & MR:
  (s, +term) = p
  go.main(s, term)

# runMain over a lifted program: its result, or the first error.
def run.main(t: Lf.Lifted, +uni: Bool) -> Result<&2, &2, Err, MR>:
  rm.got(rm.state(prog.state(t, uni)))

def rank.of(+rk: Map<&2, U32>, +h: String) -> U32:
  Pair.snd(Map<&2, U32>, U32, Map.get(U32, none(), rk, h))

# refsOf
def refs.of(l: Lf.L, +rk: Map<&2, U32>, +acc: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Lf.LRef{+loc, +h}:
      Ln.u.ins(acc, rank.of(rk, h))
    case Lf.LPair{+loc, +a, +b}:
      refs.of(b, rk, refs.of(a, rk, acc))
    case Lf.LSetEnv{+loc, +x}:
      refs.of(x, rk, acc)
    case Lf.LLeft{+loc, +x}:
      refs.of(x, rk, acc)
    case Lf.LRight{+loc, +x}:
      refs.of(x, rk, acc)
    case Lf.LCheck{+loc, +o, +tc, +c}:
      refs.of(c, rk, refs.of(tc, rk, acc))
    case other:
      acc

def pg.bds(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>, +rk: Map<&2, U32>) -> List<&2, Bd>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+h, b):
          match b:
            case Lf.Body{+fi, +body}:
              Bd{h, fi, U32.is_eq(fi, 4294967288), to.a(body, rk)} <> pg.bds(rest, rk)

def pg.refs(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>, +rk: Map<&2, U32>) -> List<&2, List<&2, U32>>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+h, b):
          match b:
            case Lf.Body{+fi, +body}:
              refs.of(body, rk, []) <> pg.refs(rest, rk)

def pg.mk(+kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>, +rk: Map<&2, U32>, +n: U32, +main: Lf.L) -> PG:
  PG{pg.bds(kvs, rk), pg.refs(kvs, rk), n, to.a(main, rk), refs.of(main, rk, [])}

def pg.of(t: Lf.Lifted) -> PG:
  match t:
    case Lf.Lifted{+bodies, +main}:
      pg.mk(Map.to_list(&2, Lf.Body, bodies), ranks(bodies), U32.from_nat(Map.size(&2, Lf.Body, bodies)), main)

def bds.arr(xs: List<&2, Bd>, +i: U32, a: Array<Bd>) -> Array<Bd>:
  match xs:
    case Nil{}:
      a
    case Con{+b, rest}:
      bds.arr(rest, (i + 1 : U32), Array.set(Bd, a, i, b))

# A fresh state over the program's bodies.
def pg.state(p: PG, +uni: Bool) -> S:
  match p:
    case PG{+bds, +refs, +n, +main, +mrefs}:
      st.new(bds.arr(bds, 0, Array.new(Bd, Ln.depth.of(n), bd.dummy())), n, uni)

def bd.got(m: Maybe<&2, Bd>) -> Bd:
  match m:
    case Some{+b}:
      b
    case None{}:
      bd.dummy()

def pg.bd(p: PG, +r: U32) -> Bd:
  match p:
    case PG{+bds, +refs, +n, +main, +mrefs}:
      bd.got(List.get(&2, Bd, bds, U32.to_nat(r)))

def pg.refs.at(p: PG, +r: U32) -> List<&2, U32>:
  match p:
    case PG{+bds, +refs, +n, +main, +mrefs}:
      ms.got(List.get(&2, List<&2, U32>, refs, U32.to_nat(r)))

def bd.term(b: Bd) -> A:
  match b:
    case Bd{+h, +fi, +link, +t}:
      t

def bd.hash(b: Bd) -> String:
  match b:
    case Bd{+h, +fi, +link, +t}:
      h

def sm.err(r: S & WT) -> Maybe<&2, Err>:
  (s, +w) = r
  Pair.snd(S, Maybe<&2, Err>, s.err(s))

# summarizeBody's structure: the body walked standalone (walk, dispatch,
# presolve), in a state of its own; its first error, if any.
def summary(+p: PG, +uni: Bool, +r: U32) -> Maybe<&2, Err>:
  +b: Bd = pg.bd(p, r)
  sm.err(walk.top(pg.state(p, uni), False{}, "env of lifted body " ++ Co.fi.show(bd.fi(b)), bd.term(b)))

def sm.ok(m: Maybe<&2, Err>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+e}:
      False{}

def pg.n(p: PG) -> U32:
  match p:
    case PG{+bds, +refs, +n, +main, +mrefs}:
      n

def vq.own(+p: PG, +uni: Bool, +r: U32) -> U32:
  Bool.pick(U32, U32.is_eq(r, pg.n(p)), 1, Bool.pick(U32, sm.ok(summary(p, uni, r)), 1, 2))

# A failure, and for main (rank n) the reference it failed at, plus one,
# at n + 1 (others write to the spare n + 2).
def vq.failed(v: Array<U32>, +n: U32, +r: U32, +d: U32) -> Array<U32>:
  Array.set(U32, Array.set(U32, v, r, 2), Bool.pick(U32, U32.is_eq(r, n), (n + 1 : U32), (n + 2 : U32)), (d + 1 : U32))

def vq.dep(unknown: Bool, ok: Bool, v: Array<U32>, +p: PG, +r: U32, +d: U32, +dr: List<&2, U32>, +rest: List<&2, VF>) -> VQ:
  match unknown:
    case True{}:
      VqGo{v, VF{d, pg.refs.at(p, d)} <> VF{r, d <> dr} <> rest}
    case False{}:
      match ok:
        case True{}:
          VqGo{v, VF{r, dr} <> rest}
        case False{}:
          VqGo{vq.failed(v, pg.n(p), r, d), rest}

def vq.look(+p: PG, +r: U32, +d: U32, +dr: List<&2, U32>, +rest: List<&2, VF>, q: Array<U32> & U32) -> VQ:
  (v, +m) = q
  vq.dep(U32.is_eq(m, 0), U32.is_eq(m, 1), v, p, r, d, dr, rest)

def vq.frame(f: VF, v: Array<U32>, +p: PG, +uni: Bool, +rest: List<&2, VF>) -> VQ:
  match f:
    case VF{+r, +ds}:
      match ds:
        case Nil{}:
          VqGo{Array.set(U32, v, r, vq.own(p, uni, r)), rest}
        case Con{+d, +dr}:
          vq.look(p, r, d, dr, rest, Array.get(U32, v, d))

def vq.step(st: List<&2, VF>, v: Array<U32>, +p: PG, +uni: Bool) -> VQ:
  match st:
    case Nil{}:
      VqEnd{v}
    case Con{+f, +rest}:
      vq.frame(f, v, p, uni, rest)

def vq.fin(q: VQ) -> Array<U32>:
  match q:
    case VqGo{v, +st}:
      v
    case VqEnd{v}:
      v

def vq.loop(fuel: Nat, q: VQ, +p: PG, +uni: Bool) -> Array<U32>:
  match fuel:
    case 0n:
      vq.fin(q)
    case 1n+f:
      match q:
        case VqGo{v, +st}:
          vq.loop(f, vq.step(st, v, p, uni), p, uni)
        case VqEnd{v}:
          v

def wd.pick(none: Bool, +p: PG, +e: Err, +d: U32) -> Err:
  match none:
    case True{}:
      e
    case False{}:
      DependencyFailed{bd.hash(pg.bd(p, (d - 1 : U32)))}

def wd.after(q: Array<U32> & U32, +p: PG, +e: Err) -> Err:
  (v, +d) = q
  wd.pick(U32.is_eq(d, 0), p, e, d)

# withDeps mainTerm (Left mainError)
def with.deps(+p: PG, +uni: Bool, +e: Err) -> Err:
  match p:
    case PG{+bds, +refs, +n, +main, +mrefs}:
      wd.after(Array.get(U32, vq.loop(big(), VqGo{Array.new(U32, Ln.depth.of((n + 3 : U32)), 0), [VF{n, mrefs}]}, p, uni), (n + 1 : U32)), p, e)

# runMain over the program as data.
def pg.main(+p: PG, +uni: Bool) -> Result<&2, &2, Err, MR>:
  match p:
    case PG{+bds, +refs, +n, +main, +mrefs}:
      rm.got(go.main(pg.state(p, uni), main))

# allDataShape
def cm.shape(m: MR) -> Maybe<&2, Err>:
  match m:
    case MR{+top, +defers, +max, +shape, +shapes, +levels}:
      Bool.pick(Maybe<&2, Err>, all.data(shape), Some{TypeMismatch{gen("EAL certification"), "main is data through and through; a program must be a function of its input"}}, None{})

# certifyMain, without the let-specialization fallbacks yet: main's
# refusal, or the first failing dependency's.
def cm.at(r: Result<&2, &2, Err, MR>, +p: PG) -> Maybe<&2, Err>:
  match r:
    case Done{+m}:
      cm.shape(m)
    case Fail{+e}:
      Some{with.deps(p, False{}, e)}

def certify.main(t: Lf.Lifted) -> Maybe<&2, Err>:
  +p: PG = pg.of(t)
  cm.at(pg.main(p, False{}), p)

# Let specialization (specializeLets)
# ------------------

# Paths are strings of steps, "L" for SL and "R" for SR, from the env
# root in application order (as envPath gives them), so string order is
# the Haskell's list order and isPrefixOf is starts_with. A substitution
# (SpecSubst) is a map from paths to lifted terms; a SpecKey is a hash, or
# "-" for Nothing (which sorts first, as Nothing does).

def path.app(m: Maybe<&2, String>, +s: String) -> Maybe<&2, String>:
  match m:
    case Some{+p}:
      Some{p ++ s}
    case None{}:
      None{}

# envPath
def path.of(t: Lf.L) -> Maybe<&2, String>:
  match t:
    case Lf.LEnv{+loc}:
      Some{""}
    case Lf.LUnsized{+loc, +tok}:
      Some{""}
    case Lf.LLeft{+loc, +x}:
      path.app(path.of(x), "L")
    case Lf.LRight{+loc, +x}:
      path.app(path.of(x), "R")
    case Lf.LCheck{+loc, +o, +tc, +c}:
      path.of(c)
    case other:
      None{}

def l.loc(t: Lf.L) -> Lc.Loc:
  match t:
    case Lf.LZero{+loc}:
      loc
    case Lf.LPair{+loc, +a, +b}:
      loc
    case Lf.LEnv{+loc}:
      loc
    case Lf.LSetEnv{+loc, +x}:
      loc
    case Lf.LGate{+loc}:
      loc
    case Lf.LLeft{+loc, +x}:
      loc
    case Lf.LRight{+loc, +x}:
      loc
    case Lf.LAbort{+loc}:
      loc
    case Lf.LUnsized{+loc, +tok}:
      loc
    case Lf.LCheck{+loc, +o, +tc, +c}:
      loc
    case Lf.LRef{+loc, +h}:
      loc

def is.l(+c: U32) -> Bool:
  U32.is_eq(c, 76)

def pj.one(+v: Lf.L, +anno: Lc.Loc, +left: Bool) -> Lf.L:
  match v:
    case Lf.LPair{+loc, +a, +b}:
      Bool.pick(Lf.L, left, a, b)
    case +other:
      Bool.pick(Lf.L, left, Lf.LLeft{anno, other}, Lf.LRight{anno, other})

# A value projected along the rest of a path: through literal pairs
# directly, else by projections at the occurrence's place.
def project(p: String, +anno: Lc.Loc, +v: Lf.L) -> Lf.L:
  match p:
    case SNil{}:
      v
    case SCon{ch, rest}:
      match ch:
        case Chr{+c}:
          project(rest, anno, pj.one(v, anno, is.l(c)))

def sa.find(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.L>>, +anno: Lc.Loc, +p: String) -> Maybe<&2, Lf.L>:
  match kvs:
    case Nil{}:
      None{}
    case Con{kv, rest}:
      match kv:
        case (+q, +v):
          Bool.pick(Maybe<&2, Lf.L>, String.starts_with(p, q), Some{project(String.drop(p, String.length(q)), anno, v)}, sa.find(rest, anno, p))

# substAt
def subst.at(+anno: Lc.Loc, sub: Map<&2, Lf.L>, +p: String) -> Maybe<&2, Lf.L>:
  sa.find(Map.to_list(&2, Lf.L, sub), anno, p)

# Map.mapKeys (step :) and Map.filter carriesCode, over substitutions.
def sub.pre(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.L>>, +s: String) -> List<&2, Sigma<&2, &2, String, _ => Lf.L>>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          (s ++ k, v) <> sub.pre(rest, s)

def sub.keep(c: Bool, +k: String, +v: Lf.L, +r: List<&2, Sigma<&2, &2, String, _ => Lf.L>>) -> List<&2, Sigma<&2, &2, String, _ => Lf.L>>:
  match c:
    case True{}:
      (k, v) <> r
    case False{}:
      r

# carriesCode
def carries.code(t: Lf.L) -> Bool:
  match t:
    case Lf.LRef{+loc, +h}:
      True{}
    case Lf.LGate{+loc}:
      True{}
    case Lf.LPair{+loc, +a, +b}:
      Bool.or(carries.code(a), carries.code(b))
    case Lf.LSetEnv{+loc, +x}:
      carries.code(x)
    case Lf.LLeft{+loc, +x}:
      carries.code(x)
    case Lf.LRight{+loc, +x}:
      carries.code(x)
    case Lf.LCheck{+loc, +o, +tc, +c}:
      Bool.or(carries.code(tc), carries.code(c))
    case other:
      False{}

def sub.code(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.L>>) -> List<&2, Sigma<&2, &2, String, _ => Lf.L>>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          sub.keep(carries.code(v), k, v, sub.code(rest))

# The entries below a path, re-rooted there.
def sub.below(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.L>>, +p: String) -> List<&2, Sigma<&2, &2, String, _ => Lf.L>>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+q, +v):
          sub.keep(Bool.and(String.starts_with(q, p), Bool.not(String.eq(q, p))), String.drop(q, String.length(p)), v, sub.below(rest, p))

def cp.at(m: Maybe<&2, Lf.L>, sub: Map<&2, Lf.L>, +p: String) -> List<&2, Sigma<&2, &2, String, _ => Lf.L>>:
  match m:
    case Some{+v}:
      [("", v)]
    case None{}:
      sub.below(Map.to_list(&2, Lf.L, sub), p)

def cp.occ(m: Maybe<&2, String>, +sub: Map<&2, Lf.L>) -> List<&2, Sigma<&2, &2, String, _ => Lf.L>>:
  match m:
    case Some{+p}:
      cp.at(subst.at(Lc.Unknown{}, sub, p), sub, p)
    case None{}:
      []

# closedParts, as an entry list (its keys come out in order). A checking
# wrapper's parts are its checked term's (its env path is that term's).
def closed.parts(+sub: Map<&2, Lf.L>, t: Lf.L) -> List<&2, Sigma<&2, &2, String, _ => Lf.L>>:
  match t:
    case Lf.LPair{+loc, +a, +b}:
      List.append(&2, Sigma<&2, &2, String, _ => Lf.L>, sub.pre(closed.parts(sub, a), "L"), sub.pre(closed.parts(sub, b), "R"))
    case Lf.LCheck{+loc, +o, +tc, +c}:
      closed.parts(sub, c)
    case other:
      cp.occ(path.of(other), sub)

# closedTerm
def closed.term(t: Lf.L) -> Bool:
  match t:
    case Lf.LEnv{+loc}:
      False{}
    case Lf.LUnsized{+loc, +tok}:
      False{}
    case Lf.LPair{+loc, +a, +b}:
      Bool.and(closed.term(a), closed.term(b))
    case Lf.LSetEnv{+loc, +x}:
      closed.term(x)
    case Lf.LLeft{+loc, +x}:
      closed.term(x)
    case Lf.LRight{+loc, +x}:
      closed.term(x)
    case Lf.LCheck{+loc, +o, +tc, +c}:
      Bool.and(closed.term(tc), closed.term(c))
    case other:
      True{}

# codeOf, as a SpecKey before origin mapping ("-" for none).
def code.of(t: Lf.L) -> String:
  match t:
    case Lf.LRef{+loc, +h}:
      h
    case Lf.LPair{+loc, +a, +b}:
      match a:
        case Lf.LRef{+aloc, +h}:
          h
        case other:
          "-"
    case other:
      "-"

def path.is(m: Maybe<&2, String>, +p: String) -> Bool:
  match m:
    case Some{+q}:
      String.eq(q, p)
    case None{}:
      False{}

# isTwiddle: (Left (Right Env), (Left Env, Right (Right Env)))
def is.twiddle(t: Lf.L) -> Bool:
  match t:
    case Lf.LPair{+loc, +x, +yz}:
      match yz:
        case Lf.LPair{+l2, +y, +z}:
          Bool.and(path.is(path.of(x), "RL"), Bool.and(path.is(path.of(y), "L"), path.is(path.of(z), "RR")))
        case other:
          False{}
    case other:
      False{}

def body.twiddle(m: Map<&2, Lf.Body> & Maybe<&2, Lf.Body>) -> Bool:
  (b, mb) = m
  match mb:
    case Some{+bd}:
      match bd:
        case Lf.Body{+fi, +body}:
          is.twiddle(body)
    case None{}:
      False{}

def twiddle.of(+bodies: Map<&2, Lf.Body>, +h: String) -> Bool:
  body.twiddle(Map.pop(&2, Lf.Body, bodies, h))

def ac.of(t: Lf.L) -> Maybe<&2, AC>:
  match t:
    case Lf.LSetEnv{+a1, +x1}:
      match x1:
        case Lf.LSetEnv{+a2, +x2}:
          match x2:
            case Lf.LPair{+a3, +tw, +p4}:
              match p4:
                case Lf.LPair{+a4, +operand, +p5}:
                  match p5:
                    case Lf.LPair{+a5, +r6, +cap}:
                      match r6:
                        case Lf.LRef{+a6, +code}:
                          Some{AC{a1, a2, a3, tw, a4, operand, a5, a6, code, cap}}
                        case other:
                          None{}
                    case other:
                      None{}
                case other:
                  None{}
            case other:
              None{}
        case other:
          None{}
    case other:
      None{}

def ac.rebuild(c: AC, +o: Lf.L, +code: String, +k: Lf.L) -> Lf.L:
  match c:
    case AC{+a1, +a2, +a3, +tw, +a4, +operand, +a5, +a6, +cd, +cap}:
      Lf.LSetEnv{a1, Lf.LSetEnv{a2, Lf.LPair{a3, tw, Lf.LPair{a4, o, Lf.LPair{a5, Lf.LRef{a6, code}, k}}}}}

# twiddleRef: the applied pair's head is the twiddle defer.
def tw.ref(tw: Lf.L, +bodies: Map<&2, Lf.Body>) -> Bool:
  match tw:
    case Lf.LRef{+loc, +h}:
      twiddle.of(bodies, h)
    case other:
      False{}

def pr.of(t: Lf.L) -> Maybe<&2, PR>:
  match t:
    case Lf.LPair{+loc, +a, +cap}:
      match a:
        case Lf.LRef{+cloc, +code}:
          Some{PR{loc, cloc, code, cap}}
        case other:
          None{}
    case other:
      None{}

def v.l(v: SV2) -> Lf.L:
  match v:
    case VL{+l}:
      l
    case VH{+h}:
      Lf.LZero{Lc.Unknown{}}

def v.h(v: SV2) -> String:
  match v:
    case VH{+h}:
      h
    case VL{+l}:
      ""

def m.has(+m: Map<&2, Bool>, +k: String) -> Bool:
  Pair.snd(Map<&2, Bool>, Bool, Map.has(&2, Bool, m, k))

def allowed.has(m: Maybe<&2, Map<&2, Bool>>, +k: String) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+s}:
      m.has(s, k)

def origin.of(+origin: Map<&2, String>, +h: String) -> String:
  Pair.snd(Map<&2, String>, String, Map.get(String, h, origin, h))

def sk.key(+origin: Map<&2, String>, +c: String) -> String:
  Bool.pick(String, String.eq(c, "-"), "-", origin.of(origin, c))

def reads.add(+reads: Map<&2, Map<&2, Bool>>, +fi: U32, +key: String) -> Map<&2, Map<&2, Bool>>:
  +k: String = fi.key(fi)
  Map.set(&2, Map<&2, Bool>, reads, k, Map.set(&2, Bool, Pair.snd(Map<&2, Map<&2, Bool>>, Map<&2, Bool>, Map.get(Map<&2, Bool>, Map.new(&2, Bool), reads, k)), key, True{}))

# An env occurrence the substitution holds a value for: noted in the
# SpecInfo, substituted if its key may be.
def st.occ.v(p: SP, +t: Lf.L, +v: Lf.L, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match p:
    case SP{+bodies, +origin, +memo, +deep, +allowed, +body, +defs, +reads}:
      +key: String = sk.key(origin, code.of(v))
      +defs2: Map<&2, Bool> = Bool.pick(Map<&2, Bool>, String.eq(key, "-"), defs, Map.set(&2, Bool, defs, key, True{}))
      +reads2: Map<&2, Map<&2, Bool>> = Bool.pick(Map<&2, Map<&2, Bool>>, U32.is_eq(body, 0), reads, reads.add(reads, (body - 1 : U32), key))
      SmGo{SP{bodies, origin, memo, deep, allowed, body, defs2, reads2}, ks, VL{Bool.pick(Lf.L, allowed.has(allowed, key), v, t)} <> vs}

def st.occ(m: Maybe<&2, Lf.L>, +p: SP, +t: Lf.L, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match m:
    case None{}:
      SmGo{p, ks, VL{t} <> vs}
    case Some{+v}:
      st.occ.v(p, t, v, ks, vs)

# The plain case: every child specialized, in order.
def st.plain(t: Lf.L, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match t:
    case Lf.LPair{+loc, +a, +b}:
      SmGo{p, SkTerm{sub, a} <> SkTerm{sub, b} <> SkPair{loc} <> ks, vs}
    case Lf.LSetEnv{+loc, +x}:
      SmGo{p, SkTerm{sub, x} <> SkSetEnv{loc} <> ks, vs}
    case Lf.LLeft{+loc, +x}:
      SmGo{p, SkTerm{sub, x} <> SkLeft{loc} <> ks, vs}
    case Lf.LRight{+loc, +x}:
      SmGo{p, SkTerm{sub, x} <> SkRight{loc} <> ks, vs}
    case Lf.LCheck{+loc, +o, +tc, +c}:
      SmGo{p, SkTerm{sub, tc} <> SkTerm{sub, c} <> SkCheck{loc, o} <> ks, vs}
    case other:
      SmGo{p, ks, VL{other} <> vs}

def st.ref(t: Lf.L, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match t:
    case Lf.LRef{+loc, +h}:
      SmGo{p, SkBody{h, Map.new(&2, Lf.L)} <> SkRef{loc} <> ks, vs}
    case other:
      st.plain(other, sub, p, ks, vs)

def st.pr(m: Maybe<&2, PR>, +t: Lf.L, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match m:
    case Some{+r}:
      match r:
        case PR{+loc, +cloc, +code, +cap}:
          SmGo{p, SkTerm{sub, cap} <> SkPRef1{sub, PR{loc, cloc, code, cap}} <> ks, vs}
    case None{}:
      st.ref(t, sub, p, ks, vs)

def sp.bodies(p: SP) -> Map<&2, Lf.Body>:
  match p:
    case SP{+bodies, +origin, +memo, +deep, +allowed, +body, +defs, +reads}:
      bodies

def st.ac.at(tw: Bool, +c: AC, +t: Lf.L, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match tw:
    case True{}:
      match c:
        case AC{+a1, +a2, +a3, +twv, +a4, +operand, +a5, +a6, +code, +cap}:
          SmGo{p, SkTerm{sub, operand} <> SkTerm{sub, cap} <> SkApp1{sub, AC{a1, a2, a3, twv, a4, operand, a5, a6, code, cap}} <> ks, vs}
    case False{}:
      st.plain(t, sub, p, ks, vs)

def ac.tw(c: AC) -> Lf.L:
  match c:
    case AC{+a1, +a2, +a3, +tw, +a4, +operand, +a5, +a6, +code, +cap}:
      tw

def st.ac(m: Maybe<&2, AC>, +t: Lf.L, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match m:
    case Some{+c}:
      st.ac.at(tw.ref(ac.tw(c), sp.bodies(p)), c, t, sub, p, ks, vs)
    case None{}:
      st.pr(pr.of(t), t, sub, p, ks, vs)

def st.path(m: Maybe<&2, String>, +t: Lf.L, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match m:
    case Some{+q}:
      st.occ(subst.at(l.loc(t), sub, q), p, t, ks, vs)
    case None{}:
      st.ac(ac.of(t), t, sub, p, ks, vs)

# specTerm, one step.
def st.term(+t: Lf.L, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  st.path(path.of(t), t, sub, p, ks, vs)

# specBody: the memo key is the hash and the substitution's text.
def sub.text(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.L>>) -> String:
  match kvs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          "[" ++ k ++ "]" ++ Lf.show(v) ++ ";" ++ sub.text(rest)

def sb.found(m: Maybe<&2, Lf.Body>, +p: SP, +h: String, +key: String, +sub: Map<&2, Lf.L>, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match m:
    case None{}:
      SmGo{p, ks, VH{h} <> vs}
    case Some{+b}:
      match b:
        case Lf.Body{+fi, +body}:
          match p:
            case SP{+bodies, +origin, +memo, +deep, +allowed, +outer, +defs, +reads}:
              SmGo{SP{bodies, origin, memo, deep, allowed, (fi + 1 : U32), defs, reads}, SkTerm{sub, body} <> SkBodyEnd{h, key, fi, outer, body} <> ks, vs}

def sb.memo(m: Maybe<&2, String>, +p: SP, +h: String, +key: String, +sub: Map<&2, Lf.L>, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match m:
    case Some{+h2}:
      SmGo{p, ks, VH{h2} <> vs}
    case None{}:
      sb.found(Pair.snd(Map<&2, Lf.Body>, Maybe<&2, Lf.Body>, Map.pop(&2, Lf.Body, sp.bodies(p), h)), p, h, key, sub, ks, vs)

def sp.memo(p: SP) -> Map<&2, String>:
  match p:
    case SP{+bodies, +origin, +memo, +deep, +allowed, +body, +defs, +reads}:
      memo

def st.body(+h: String, +sub: Map<&2, Lf.L>, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  +key: String = h ++ "#" ++ sub.text(Map.to_list(&2, Lf.L, sub))
  sb.memo(Pair.snd(Map<&2, String>, Maybe<&2, String>, Map.pop(&2, String, sp.memo(p), key)), p, h, key, sub, ks, vs)

def sb.end(p: SP, +h: String, +key: String, +fi: U32, +outer: U32, +body: Lf.L, +body2: Lf.L, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match p:
    case SP{+bodies, +origin, +memo, +deep, +allowed, +cur, +defs, +reads}:
      +text: String = Lf.show(body2)
      +same: Bool = String.eq(text, Lf.show(body))
      +h2: String = Bool.pick(String, same, h, Lf.hash(body2))
      +bodies2: Map<&2, Lf.Body> = Bool.pick(Map<&2, Lf.Body>, same, bodies, Map.set(&2, Lf.Body, bodies, h2, Lf.Body{fi, body2}))
      +origin2: Map<&2, String> = Bool.pick(Map<&2, String>, same, origin, Map.set(&2, String, origin, h2, origin.of(origin, h)))
      SmGo{SP{bodies2, origin2, Map.set(&2, String, memo, key, h2), deep, allowed, outer, defs, reads}, ks, VH{h2} <> vs}

def sp.deep(p: SP) -> Bool:
  match p:
    case SP{+bodies, +origin, +memo, +deep, +allowed, +body, +defs, +reads}:
      deep

# The second half of a Pair (DeferRef code) cap: specialize the code on
# what the captures take from the substitution, if deep and not the
# twiddle.
def pref.k(keep: Bool, r: PR, +sub: Map<&2, Lf.L>, +k: Lf.L, +p: SP, +ks: List<&2, SK>, +vs: List<&2, SV2>) -> SM:
  match keep:
    case True{}:
      match r:
        case PR{+loc, +cloc, +code, +cap}:
          SmGo{p, ks, VL{Lf.LPair{loc, Lf.LRef{cloc, code}, k}} <> vs}
    case False{}:
      match r:
        case PR{+loc, +cloc, +code, +cap}:
          SmGo{p, SkBody{code, Map.from_list(&2, Lf.L, sub.code(sub.pre(closed.parts(sub, cap), "R")))} <> SkPRef2{loc, cloc, k} <> ks, vs}

def pr.code(r: PR) -> String:
  match r:
    case PR{+loc, +cloc, +code, +cap}:
      code

def sk.pref1(+sub: Map<&2, Lf.L>, +r: PR, +p: SP, +ks: List<&2, SK>, vs: List<&2, SV2>) -> SM:
  match vs:
    case Con{+vk, +rest}:
      pref.k(Bool.or(Bool.not(sp.deep(p)), twiddle.of(sp.bodies(p), pr.code(r))), r, sub, v.l(vk), p, ks, rest)
    case Nil{}:
      SmGo{p, ks, []}

# The second half of an applied closure: the code specialized on the
# closed parts of its operand and captures.
def app.sub.of(+sub: Map<&2, Lf.L>, +from: List<&2, Sigma<&2, &2, String, _ => Lf.L>>, +cap: Lf.L) -> Map<&2, Lf.L>:
  Map.from_list(&2, Lf.L, sub.code(List.append(&2, Sigma<&2, &2, String, _ => Lf.L>, sub.pre(from, "L"), sub.pre(closed.parts(sub, cap), "R"))))

def app.sub(+sub: Map<&2, Lf.L>, +o2: Lf.L, +operand: Lf.L, +cap: Lf.L) -> Map<&2, Lf.L>:
  app.sub.of(sub, Bool.pick(List<&2, Sigma<&2, &2, String, _ => Lf.L>>, closed.term(o2), [("", o2)], closed.parts(sub, operand)), cap)

def sk.app1(+sub: Map<&2, Lf.L>, c: AC, +p: SP, +ks: List<&2, SK>, vs: List<&2, SV2>) -> SM:
  match c:
    case AC{+a1, +a2, +a3, +tw, +a4, +operand, +a5, +a6, +code, +cap}:
      match vs:
        case Con{+vk, +r1}:
          match r1:
            case Con{+vo, +r2}:
              SmGo{p, SkBody{code, app.sub(sub, v.l(vo), operand, cap)} <> SkApp2{AC{a1, a2, a3, tw, a4, operand, a5, a6, code, cap}, v.l(vo), v.l(vk)} <> ks, r2}
            case Nil{}:
              SmGo{p, ks, []}
        case Nil{}:
          SmGo{p, ks, []}

# A finished value, put together from the values below it.
def sk.one(k: SK, +p: SP, +ks: List<&2, SK>, vs: List<&2, SV2>) -> SM:
  match k:
    case SkTerm{+sub, +t}:
      st.term(t, sub, p, ks, vs)
    case SkBody{+h, +sub}:
      st.body(h, sub, p, ks, vs)
    case SkPair{+loc}:
      match vs:
        case Con{+vb, +r1}:
          match r1:
            case Con{+va, +r2}:
              SmGo{p, ks, VL{Lf.LPair{loc, v.l(va), v.l(vb)}} <> r2}
            case Nil{}:
              SmGo{p, ks, []}
        case Nil{}:
          SmGo{p, ks, []}
    case SkSetEnv{+loc}:
      match vs:
        case Con{+vx, +r1}:
          SmGo{p, ks, VL{Lf.LSetEnv{loc, v.l(vx)}} <> r1}
        case Nil{}:
          SmGo{p, ks, []}
    case SkLeft{+loc}:
      match vs:
        case Con{+vx, +r1}:
          SmGo{p, ks, VL{Lf.LLeft{loc, v.l(vx)}} <> r1}
        case Nil{}:
          SmGo{p, ks, []}
    case SkRight{+loc}:
      match vs:
        case Con{+vx, +r1}:
          SmGo{p, ks, VL{Lf.LRight{loc, v.l(vx)}} <> r1}
        case Nil{}:
          SmGo{p, ks, []}
    case SkCheck{+loc, +o}:
      match vs:
        case Con{+vc, +r1}:
          match r1:
            case Con{+vt, +r2}:
              SmGo{p, ks, VL{Lf.LCheck{loc, o, v.l(vt), v.l(vc)}} <> r2}
            case Nil{}:
              SmGo{p, ks, []}
        case Nil{}:
          SmGo{p, ks, []}
    case SkApp1{+sub, +c}:
      sk.app1(sub, c, p, ks, vs)
    case SkApp2{+c, +o, +kk}:
      match vs:
        case Con{+vh, +r1}:
          SmGo{p, ks, VL{ac.rebuild(c, o, v.h(vh), kk)} <> r1}
        case Nil{}:
          SmGo{p, ks, []}
    case SkPRef1{+sub, +r}:
      sk.pref1(sub, r, p, ks, vs)
    case SkPRef2{+loc, +cloc, +kk}:
      match vs:
        case Con{+vh, +r1}:
          SmGo{p, ks, VL{Lf.LPair{loc, Lf.LRef{cloc, v.h(vh)}, kk}} <> r1}
        case Nil{}:
          SmGo{p, ks, []}
    case SkRef{+loc}:
      match vs:
        case Con{+vh, +r1}:
          SmGo{p, ks, VL{Lf.LRef{loc, v.h(vh)}} <> r1}
        case Nil{}:
          SmGo{p, ks, []}
    case SkBodyEnd{+h, +key, +fi, +outer, +body}:
      match vs:
        case Con{+vb, +r1}:
          sb.end(p, h, key, fi, outer, body, v.l(vb), ks, r1)
        case Nil{}:
          SmGo{p, ks, []}

def sm.step(ks: List<&2, SK>, +p: SP, +vs: List<&2, SV2>) -> SM:
  match ks:
    case Nil{}:
      SmEnd{p, vs}
    case Con{+k, +rest}:
      sk.one(k, p, rest, vs)

def sm.loop(fuel: Nat, m: SM) -> SM:
  match fuel:
    case 0n:
      m
    case 1n+f:
      match m:
        case SmGo{+p, +ks, +vs}:
          sm.loop(f, sm.step(ks, p, vs))
        case SmEnd{+p, +vs}:
          SmEnd{p, vs}

def sr.of(m: SM) -> SR:
  match m:
    case SmEnd{+p, +vs}:
      match p:
        case SP{+bodies, +origin, +memo, +deep, +allowed, +body, +defs, +reads}:
          match vs:
            case Con{+v, +rest}:
              SR{bodies, origin, v.l(v), defs, reads}
            case Nil{}:
              SR{bodies, origin, Lf.LZero{Lc.Unknown{}}, defs, reads}
    case SmGo{+p, +ks, +vs}:
      SR{sp.bodies(p), Map.new(&2, String), Lf.LZero{Lc.Unknown{}}, Map.new(&2, Bool), Map.new(&2, Map<&2, Bool>)}

def specialize(+allowed: Maybe<&2, Map<&2, Bool>>, +deep: Bool, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> SR:
  sr.of(sm.loop(big(), SmGo{SP{bodies, Map.new(&2, String), Map.new(&2, String), deep, allowed, 0, Map.new(&2, Bool), Map.new(&2, Map<&2, Bool>)}, [SkTerm{Map.new(&2, Lf.L), main}], []}))

# The let-polymorphic fallbacks (inferEALLiftedWith)
# --------------------------

# Sets of strings, as maps to True.
def set.add.all(kvs: List<&2, Sigma<&2, &2, String, _ => Bool>>, +m: Map<&2, Bool>) -> Map<&2, Bool>:
  match kvs:
    case Nil{}:
      m
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          set.add.all(rest, Map.set(&2, Bool, m, k, True{}))

def set.union(+a: Map<&2, Bool>, +b: Map<&2, Bool>) -> Map<&2, Bool>:
  set.add.all(Map.to_list(&2, Bool, b), a)

def set.keep(c: Bool, +k: String, +r: List<&2, String>) -> List<&2, String>:
  match c:
    case True{}:
      k <> r
    case False{}:
      r

# The keys of a not in b.
def set.minus.go(kvs: List<&2, Sigma<&2, &2, String, _ => Bool>>, +b: Map<&2, Bool>) -> List<&2, String>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          set.keep(Bool.not(m.has(b, k)), k, set.minus.go(rest, b))

def set.of(xs: List<&2, String>, +m: Map<&2, Bool>) -> Map<&2, Bool>:
  match xs:
    case Nil{}:
      m
    case Con{+x, rest}:
      set.of(rest, Map.set(&2, Bool, m, x, True{}))

def set.minus(+a: Map<&2, Bool>, +b: Map<&2, Bool>) -> Map<&2, Bool>:
  set.of(set.minus.go(Map.to_list(&2, Bool, a), b), Map.new(&2, Bool))

def set.any.in(kvs: List<&2, Sigma<&2, &2, String, _ => Bool>>, +b: Map<&2, Bool>) -> Bool:
  match kvs:
    case Nil{}:
      False{}
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          Bool.or(m.has(b, k), set.any.in(rest, b))

def set.meets(+a: Map<&2, Bool>, +b: Map<&2, Bool>) -> Bool:
  set.any.in(Map.to_list(&2, Bool, a), b)

def set.empty(+a: Map<&2, Bool>) -> Bool:
  U32.is_eq(U32.from_nat(Map.size(&2, Bool, a)), 0)

# errorBodies: the bodies a failure's blames were made in (by fi.key).
def eb.blame(+m: Map<&2, Bool>, b: Blame) -> Map<&2, Bool>:
  match b:
    case Blame{+loc, +why, +fr}:
      Bool.pick(Map<&2, Bool>, U32.is_eq(fr, 0), m, Map.set(&2, Bool, m, fi.key((fr - 1 : U32)), True{}))

def eb.blames(bs: List<&2, Blame>, +m: Map<&2, Bool>) -> Map<&2, Bool>:
  match bs:
    case Nil{}:
      m
    case Con{+b, rest}:
      eb.blames(rest, eb.blame(m, b))

def error.bodies(e: Err) -> Map<&2, Bool>:
  match e:
    case BoxConflict{+need, +forbid}:
      eb.blame(eb.blame(Map.new(&2, Bool), need), forbid)
    case Unsat{+bs}:
      eb.blames(bs, Map.new(&2, Bool))
    case other:
      Map.new(&2, Bool)

def rq.add(q: Array<Map<&2, Bool>> & Map<&2, Bool>, +m: Map<&2, Bool>) -> Array<Map<&2, Bool>> & Map<&2, Bool>:
  (a, +s) = q
  (a, set.union(m, s))

def rq.union(xs: List<&2, U32>, q: Array<Map<&2, Bool>> & Map<&2, Bool>) -> Array<Map<&2, Bool>> & Map<&2, Bool>:
  match xs:
    case Nil{}:
      q
    case Con{+x, rest}:
      (a, +m) = q
      rq.union(rest, rq.add(Array.get(Map<&2, Bool>, a, x), m))

def rq.done(q: Array<Map<&2, Bool>> & Map<&2, Bool>, d: Array<U32>, +r: U32, +rest: List<&2, RF>) -> RQ:
  (a, +m) = q
  RqGo{Array.set(Map<&2, Bool>, a, r, m), Array.set(U32, d, r, 1), rest}

def rq.dep(seen: Bool, a: Array<Map<&2, Bool>>, d: Array<U32>, +p: PG, +r: U32, +x: U32, +xs: List<&2, U32>, +rest: List<&2, RF>) -> RQ:
  match seen:
    case True{}:
      RqGo{a, d, RF{r, xs} <> rest}
    case False{}:
      RqGo{a, d, RF{x, pg.refs.at(p, x)} <> RF{r, x <> xs} <> rest}

def rq.look(a: Array<Map<&2, Bool>>, q: Array<U32> & U32, +p: PG, +r: U32, +x: U32, +xs: List<&2, U32>, +rest: List<&2, RF>) -> RQ:
  (d, +m) = q
  rq.dep(U32.is_eq(m, 1), a, d, p, r, x, xs, rest)

def rq.frame(f: RF, a: Array<Map<&2, Bool>>, d: Array<U32>, +p: PG, +rest: List<&2, RF>) -> RQ:
  match f:
    case RF{+r, +ds}:
      match ds:
        case Nil{}:
          rq.done(rq.union(pg.refs.at(p, r), (a, Map.set(&2, Bool, Map.new(&2, Bool), fi.key(bd.fi(pg.bd(p, r))), True{}))), d, r, rest)
        case Con{+x, +xs}:
          rq.look(a, Array.get(U32, d, x), p, r, x, xs, rest)

def rq.step(st: List<&2, RF>, a: Array<Map<&2, Bool>>, d: Array<U32>, +p: PG) -> RQ:
  match st:
    case Nil{}:
      RqEnd{a}
    case Con{+f, +rest}:
      rq.frame(f, a, d, p, rest)

def rq.fin(q: RQ) -> Array<Map<&2, Bool>>:
  match q:
    case RqGo{a, d, +st}:
      a
    case RqEnd{a}:
      a

def rq.loop(fuel: Nat, q: RQ, +p: PG) -> Array<Map<&2, Bool>>:
  match fuel:
    case 0n:
      rq.fin(q)
    case 1n+f:
      match q:
        case RqGo{a, d, +st}:
          rq.loop(f, rq.step(st, a, d, p), p)
        case RqEnd{a}:
          a

def rq.roots(n: Nat, +i: U32) -> List<&2, RF>:
  match n:
    case 0n:
      []
    case 1n+k:
      RF{i, []} <> rq.roots(k, (i + 1 : U32))

def rq.seed(n: Nat, +i: U32, +p: PG) -> List<&2, RF>:
  match n:
    case 0n:
      []
    case 1n+k:
      RF{i, pg.refs.at(p, i)} <> rq.seed(k, (i + 1 : U32), p)

# Every body's reach, by rank: each rank gets a frame whose references are
# pushed as it is met.
def reach.all(+p: PG) -> Array<Map<&2, Bool>>:
  rq.loop(big(), RqGo{Array.new(Map<&2, Bool>, Ln.depth.of(pg.n(p)), Map.new(&2, Bool)), Array.new(U32, Ln.depth.of(pg.n(p)), 0), rq.seed(U32.to_nat(pg.n(p)), 0, p)}, p)

# The reaches as data: a list by rank.
def rl.add(q: Array<Map<&2, Bool>> & Map<&2, Bool>, +acc: List<&2, Map<&2, Bool>>) -> Array<Map<&2, Bool>> & List<&2, Map<&2, Bool>>:
  (a, +m) = q
  (a, m <> acc)

def rl.go(n: Nat, +i: U32, q: Array<Map<&2, Bool>> & List<&2, Map<&2, Bool>>) -> Array<Map<&2, Bool>> & List<&2, Map<&2, Bool>>:
  match n:
    case 0n:
      q
    case 1n+k:
      (a, +acc) = q
      rl.go(k, (i + 1 : U32), rl.add(Array.get(Map<&2, Bool>, a, i), acc))

def rl.fin(q: Array<Map<&2, Bool>> & List<&2, Map<&2, Bool>>) -> List<&2, Map<&2, Bool>>:
  (a, +acc) = q
  List.reverse(&2, Map<&2, Bool>, acc)

def reach.list(n: Nat, a: Array<Map<&2, Bool>>) -> List<&2, Map<&2, Bool>>:
  rl.fin(rl.go(n, 0, (a, [])))

def reach.got(m: Maybe<&2, Map<&2, Bool>>) -> Map<&2, Bool>:
  match m:
    case Some{+x}:
      x
    case None{}:
      Map.new(&2, Bool)

def reach.of(+ni: NI, +h: String) -> Map<&2, Bool>:
  match ni:
    case NI{+rk, +reach, +defs, +reads}:
      reach.got(List.get(&2, Map<&2, Bool>, reach, U32.to_nat(rank.of(rk, h))))

# readIn: what the given bodies read.
def read.in.go(kvs: List<&2, Sigma<&2, &2, String, _ => Bool>>, +reads: Map<&2, Map<&2, Bool>>, +acc: Map<&2, Bool>) -> Map<&2, Bool>:
  match kvs:
    case Nil{}:
      acc
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          read.in.go(rest, reads, set.union(acc, Pair.snd(Map<&2, Map<&2, Bool>>, Map<&2, Bool>, Map.get(Map<&2, Bool>, Map.new(&2, Bool), reads, k))))

def read.in(+ni: NI, +fis: Map<&2, Bool>) -> Map<&2, Bool>:
  match ni:
    case NI{+rk, +reach, +defs, +reads}:
      read.in.go(Map.to_list(&2, Bool, fis), reads, Map.new(&2, Bool))

# owners: the definitions whose code reaches one of the bodies.
def owners.go(kvs: List<&2, Sigma<&2, &2, String, _ => Bool>>, +ni: NI, +fis: Map<&2, Bool>, +acc: Map<&2, Bool>) -> Map<&2, Bool>:
  match kvs:
    case Nil{}:
      acc
    case Con{kv, rest}:
      match kv:
        case (+h, +v):
          owners.go(rest, ni, fis, Bool.pick(Map<&2, Bool>, set.meets(reach.of(ni, h), fis), Map.set(&2, Bool, acc, h, True{}), acc))

def ni.defs(ni: NI) -> Map<&2, Bool>:
  match ni:
    case NI{+rk, +reach, +defs, +reads}:
      defs

# What the owners' reaches read, for every owner with code.
def owned.go(kvs: List<&2, Sigma<&2, &2, String, _ => Bool>>, +ni: NI, +acc: Map<&2, Bool>) -> Map<&2, Bool>:
  match kvs:
    case Nil{}:
      acc
    case Con{kv, rest}:
      match kv:
        case (+o, +v):
          owned.go(rest, ni, Bool.pick(Map<&2, Bool>, String.eq(o, "-"), acc, set.union(acc, read.in(ni, reach.of(ni, o)))))

def pa.owners(+ni: NI, +owners: Map<&2, Bool>) -> Map<&2, Bool>:
  set.union(owners, owned.go(Map.to_list(&2, Bool, owners), ni, Map.new(&2, Bool)))

# pointedAt
def pointed.at(+ni: NI, +fis: Map<&2, Bool>) -> Map<&2, Bool>:
  pa.owners(ni, set.union(owners.go(Map.to_list(&2, Bool, ni.defs(ni)), ni, fis, Map.new(&2, Bool)), read.in(ni, fis)))

def ni.sr(r: SR, +rk: Map<&2, U32>, +reach: List<&2, Map<&2, Bool>>) -> NI:
  match r:
    case SR{+bodies, +origin, +main, +defs, +reads}:
      NI{rk, reach, defs, reads}

def ni.of(+bodies: Map<&2, Lf.Body>, +main: Lf.L, +p: PG) -> NI:
  ni.sr(specialize(None{}, True{}, bodies, main), ranks(bodies), reach.list(U32.to_nat(pg.n(p)), reach.all(p)))

# A specialized program's main pass.
def sr.main(r: SR) -> Result<&2, &2, Err, MR>:
  match r:
    case SR{+bodies, +origin, +main, +defs, +reads}:
      pg.main(pg.of(Lf.Lifted{bodies, main}), False{})

def sk.keys(kvs: List<&2, Sigma<&2, &2, String, _ => String>>, +m: Map<&2, Bool>) -> Map<&2, Bool>:
  match kvs:
    case Nil{}:
      m
    case Con{kv, rest}:
      match kv:
        case (+k, +v):
          sk.keys(rest, Map.set(&2, Bool, m, k, True{}))

def sr.changed(r: SR) -> Bool:
  match r:
    case SR{+bodies, +origin, +main, +defs, +reads}:
      Bool.not(set.empty(sk.keys(Map.to_list(&2, String, origin), Map.new(&2, Bool))))

def res.some(r: Result<&2, &2, Err, MR>) -> Maybe<&2, MR>:
  match r:
    case Done{+m}:
      Some{m}
    case Fail{+e}:
      None{}

def ol.put(+h: String, +s: Lf.Shape, +m: Map<&2, Lf.Shape>) -> Map<&2, Lf.Shape>:
  sm.has(Map.has(&2, Lf.Shape, m, h), h, s)

# originLayouts: a specialized body's layout is its origin's, met.
def ol.go(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Shape>>, +origin: Map<&2, String>, +m: Map<&2, Lf.Shape>) -> Map<&2, Lf.Shape>:
  match kvs:
    case Nil{}:
      m
    case Con{kv, rest}:
      match kv:
        case (+h, +s):
          ol.go(rest, origin, ol.put(origin.of(origin, h), s, m))

def mr.origin(m: MR, +origin: Map<&2, String>) -> MR:
  match m:
    case MR{+top, +defers, +max, +shape, +shapes, +levels}:
      MR{top, defers, max, shape, ol.go(Map.to_list(&2, Lf.Shape, shapes), origin, Map.new(&2, Lf.Shape)), levels}

def sr.origin(r: SR) -> Map<&2, String>:
  match r:
    case SR{+bodies, +origin, +main, +defs, +reads}:
      origin

def res.some.o(r: Result<&2, &2, Err, MR>, +origin: Map<&2, String>) -> Maybe<&2, MR>:
  match r:
    case Done{+m}:
      Some{mr.origin(m, origin)}
    case Fail{+e}:
      None{}

# specialized deep: substitute everything, if anything changed.
def specialized.at(changed: Bool, +r: SR) -> Maybe<&2, MR>:
  match changed:
    case True{}:
      res.some.o(sr.main(r), sr.origin(r))
    case False{}:
      None{}

def specialized(+deep: Bool, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> Maybe<&2, MR>:
  +r: SR = specialize(None{}, deep, bodies, main)
  specialized.at(sr.changed(r), r)

def nf.run(r: Result<&2, &2, Err, MR>, +allowed: Map<&2, Bool>, +origin: Map<&2, String>) -> NF:
  match r:
    case Done{+m}:
      NfDone{Some{mr.origin(m, origin)}}
    case Fail{+e}:
      NfGo{allowed, e}

def nf.sr(+r: SR, +allowed: Map<&2, Bool>) -> NF:
  nf.run(sr.main(r), allowed, sr.origin(r))

def nf.at(none: Bool, +allowed: Map<&2, Bool>, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> NF:
  match none:
    case True{}:
      NfDone{None{}}
    case False{}:
      nf.sr(specialize(Some{allowed}, True{}, bodies, main), allowed)

def nf.step(+ni: NI, +allowed: Map<&2, Bool>, +e: Err, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> NF:
  +new: Map<&2, Bool> = set.minus(pointed.at(ni, error.bodies(e)), allowed)
  nf.at(set.empty(new), set.union(allowed, new), bodies, main)

def nf.loop(fuel: Nat, +n: NF, +ni: NI, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> Maybe<&2, MR>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match n:
        case NfGo{+allowed, +e}:
          nf.loop(f, nf.step(ni, allowed, e, bodies, main), ni, bodies, main)
        case NfDone{+r}:
          r

def narrowed(+e: Err, +bodies: Map<&2, Lf.Body>, +main: Lf.L, +p: PG) -> Maybe<&2, MR>:
  nf.loop(big(), NfGo{Map.new(&2, Bool), e}, ni.of(bodies, main, p), bodies, main)

# narrowed <|> specialized False <|> specialized True
def fb.two(m: Maybe<&2, MR>, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> Maybe<&2, MR>:
  match m:
    case Some{+x}:
      Some{x}
    case None{}:
      specialized(True{}, bodies, main)

def fb.one(m: Maybe<&2, MR>, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> Maybe<&2, MR>:
  match m:
    case Some{+x}:
      Some{x}
    case None{}:
      fb.two(specialized(False{}, bodies, main), bodies, main)

def fallback(+e: Err, t: Lf.Lifted, +p: PG) -> Maybe<&2, MR>:
  match t:
    case Lf.Lifted{+bodies, +main}:
      fb.one(narrowed(e, bodies, main, p), bodies, main)

# ealLiftedMain of inferEALLifted: main's pass, else a fallback's, else
# main's failure behind its dependencies'.
def lm.fb(m: Maybe<&2, MR>, +p: PG, +e: Err) -> Result<&2, &2, Err, MR>:
  match m:
    case Some{+x}:
      Done{x}
    case None{}:
      Fail{with.deps(p, False{}, e)}

def lm.at(r: Result<&2, &2, Err, MR>, +t: Lf.Lifted, +p: PG) -> Result<&2, &2, Err, MR>:
  match r:
    case Done{+m}:
      Done{m}
    case Fail{+e}:
      lm.fb(fallback(e, t, p), p, e)

def lifted.main(+t: Lf.Lifted) -> Result<&2, &2, Err, MR>:
  +p: PG = pg.of(t)
  lm.at(pg.main(p, False{}), t, p)

# certifyMain
def cmain.at(r: Result<&2, &2, Err, MR>) -> Maybe<&2, Err>:
  match r:
    case Done{+m}:
      cm.shape(m)
    case Fail{+e}:
      Some{e}

def certify.main.full(+t: Lf.Lifted) -> Maybe<&2, Err>:
  cmain.at(lifted.main(t))

def ly.at(r: Map<&2, Lf.Shape> & Bool, +h: String, +m: Map<&2, Lf.Shape>) -> Map<&2, Lf.Shape>:
  (shapes, +known) = r
  Bool.pick(Map<&2, Lf.Shape>, known, Map.set(&2, Lf.Shape, m, h, Pair.snd(Map<&2, Lf.Shape>, Lf.Shape, Map.get(Lf.Shape, Lf.CapOther{}, shapes, h))), m)

# ealCaptureLayouts of inferEALLifted: every body's layout when the
# program certifies (through a fallback, by origin), none otherwise.
def ly.keep(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>, +shapes: Map<&2, Lf.Shape>, +m: Map<&2, Lf.Shape>) -> Map<&2, Lf.Shape>:
  match kvs:
    case Nil{}:
      m
    case Con{kv, rest}:
      match kv:
        case (+h, +b):
          ly.keep(rest, shapes, ly.at(Map.has(&2, Lf.Shape, shapes, h), h, m))

def ly.res(r: Result<&2, &2, Err, MR>, t: Lf.Lifted) -> Map<&2, Lf.Shape>:
  match r:
    case Fail{+e}:
      Map.new(&2, Lf.Shape)
    case Done{+m}:
      match m:
        case MR{+top, +defers, +max, +shape, +shapes, +levels}:
          match t:
            case Lf.Lifted{+bodies, +main}:
              ly.keep(Map.to_list(&2, Lf.Body, bodies), shapes, Map.new(&2, Lf.Shape))

def layouts(+t: Lf.Lifted) -> Map<&2, Lf.Shape>:
  ly.res(lifted.main(t), t)

# certifyMain (the gate).
def certify(+t: Lf.Lifted) -> Maybe<&2, Err>:
  certify.main.full(t)

