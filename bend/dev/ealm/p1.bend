import Base
import ./Show.bend as Sh
import ./Loc.bend as Lc
import ./Core.bend as Co
import ./Lift.bend as Lf
import ./Linear.bend as Ln
import ./Expr.bend as E

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
  Blame{+loc: Lc.Loc, +why: Why, +fr: U32}

# A blame's reason, rendered only when an error shows it (renderBlame): a
# message by number (why.msg), a text, a duplicated capture's path, or a
# presolve step's derivation of another blame (derivedBlame), which reads
# "what: reason". Equations carry blames by the hundred thousand, and
# presolve derives them every round, so none is a string until shown.
type Why is Data:
  WMsg{+k: U32}
  WText{+s: String}
  WDup{+what: String, +path: List<&2, U32>}
  WDer{+d: Wd, +base: Why}

# A derivation's "what": a step's name (der.msg) and the equation it read
# (eq.note) or the cycle note it names (cn.ph), or a text.
type Wd is Data:
  WdEq{+k: U32, +lhs: List<&2, U32>, +rhs: U32}
  WdCyc{+k: U32, +id: U32}
  WdTxt{+s: String}

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

# A sum equation over class roots (EqR).
type ER is Data:
  ER{+lhs: List<&2, U32>, +rhs: U32, +bl: Blame}

# A cycle note of presolve's cycleStep, kept for rendering: the cycle's
# members and the equations touching it, shown only when an error is
# rendered (th.str). A derived blame holds a placeholder for it (\1
# number \2), expanded then too (the Haskell builds the note lazily, and
# it is long: shown eagerly, every round's notes were most of the walk's
# memory).
type CN is Data:
  CN{+id: U32, +ms: List<&2, U32>, +tl: List<&2, ER>}

# The state (EALState).
type S is Type:
  S{tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>,
    pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat,
    na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>,
    nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32}

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

type K is Data:
  KVar{}
  KCode{}
  KCap{}
  KPair{}
  KData{}
  KAbort{}

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
  Blame{loc, WText{why}, 0}

def bm(+loc: Lc.Loc, +k: U32) -> Blame:
  Blame{loc, WMsg{k}, 0}

def why.msg(+k: U32) -> String:
  match k:
    case 0:
      "the unit box count"
    case 1:
      "the program's root sits at depth zero"
    case 2:
      "a duplicated capture's bang = door + what the body opens"
    case 3:
      "at most one door per duplicated capture"
    case 4:
      "env occurrence depth = the bangs this body opens"
    case 5:
      "variable occurrence is locally unboxed"
    case 6:
      "a door needs the closure's own box"
    case 7:
      "boxes entered = boxes on the applied pair + on the function"
    case 8:
      "operand boxes = applied pair boxes + its own"
    case 9:
      "operand boxes = boxes entered + boxes the callee sees"
    case 10:
      "result boxes = boxes entered + the callee's result boxes"
    case 11:
      "projected component boxes = pair boxes + its own"
    case 12:
      "box depth = the parent's depth + this edge's boxes"
    case 13:
      "view bangs = edge boxes + intrinsic bangs"
    case 14:
      "taken branch boxes = branch pair boxes + its own"
    case 15:
      "an equation the solver named is missing"
    case 16:
      "an occurrence's global depth = its frame's base + its depth"
    case 17:
      "pair constructor is locally unboxed"
    case 18:
      "gate is an unboxed value"
    case 19:
      "code constant is an unboxed value"
    case 20:
      "gate switch function is locally unboxed"
    case 21:
      "Zero is an unboxed value"
    case _:
      ""

def der.msg(+k: U32) -> String:
  match k:
    case 0:
      "summand of an unboxed total"
    case 1:
      "all summands unboxed"
    case 2:
      "sum of summand lower bounds"
    case 3:
      "total equal to two of its own summands"
    case 4:
      "summand beside one equal to the total"
    case _:
      ""

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
    case Lf.LAborted{loc, o, m}:
      AAbort{loc, to.a(m, rk)}

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
      why.text(why) ++ render.at(Lc.render_compact(loc))

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

