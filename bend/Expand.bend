import Base
import ./Loc.bend as L
import ./Syntax.bend as S

# Expansion (Telomare.Expand): multi-pattern lambdas become single-binder
# lambdas over case destructuring, let definitions become plain bindings, a
# refinement `x : T = v` becomes a check, as does a lambda parameter
# `(x : T)`, and list assignments become their per-slot bindings.

type ExpErr is Data:
  ListArityMismatch{+loc: L.Loc, +names: Nat, +slots: Nat}
  DuplicatePatternVariable{+loc: L.Loc, +name: String}
  GuardUsesOwnBinder{+loc: L.Loc, +name: String}
  MissingMain{}

# The lets and lambdas a list assignment's list literal sits under, outermost
# first: every slot is re-wrapped in them.
type Layer is Data:
  WLet{+loc: L.Loc, +binds: List<&2, S.ExpandedBind()>}
  WLam{+loc: L.Loc, +v: L.Name}

# The slots of a list literal under lets and lambdas (listAssignmentSlots),
# with the layers above it, innermost first in `acc`.
type Slots is Data:
  Slots{+xs: List<&2, S.Expanded()>, +layers: List<&2, Layer>}
  NoSlots{}

# What the walk expands (parsed), and what it gives back (expanded).
type EN is Data:
  ETerm{+t: S.Parsed()}
  EPat{+p: S.ParsedPat()}
  ELPats{+ps: List<&2, S.ParsedLPat()>}
  ETerms{+xs: List<&2, S.Parsed()>}
  EBinds{+bs: List<&2, S.ParsedBind()>}
  EDefs{+ds: List<&2, S.Def>}
  EAlts{+loc: L.Loc, +alts: List<&2, S.ParsedAlt()>}

type EV is Data:
  VT{+t: S.Expanded()}
  VP{+p: S.ExpandedPat()}
  VLPs{+ps: List<&2, S.ExpandedLPat()>}
  VTs{+xs: List<&2, S.Expanded()>}
  VBs{+bs: List<&2, S.ExpandedBind()>}
  VAs{+alts: List<&2, S.ExpandedAlt()>}

def at.got(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      " at " ++ s
    case None{}:
      ""

def at.loc(l: L.Loc) -> String:
  at.got(L.render(l))

def R(-A: Data) -> Data:
  Result<&2, &2, ExpErr, A>

# Wrapping layers
# ---------------

def wrap(ls: List<&2, Layer>, t: S.Expanded()) -> S.Expanded():
  match ls:
    case Nil{}:
      t
    case Con{l, rest}:
      match l:
        case WLet{loc, binds}:
          S.SLet{loc, binds, wrap(rest, t)}
        case WLam{loc, v}:
          S.SLam{loc, v, wrap(rest, t)}

def wrap.all(+ls: List<&2, Layer>, ts: List<&2, S.Expanded()>) -> List<&2, S.Expanded()>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      wrap(ls, t) <> wrap.all(ls, rest)

def slots(t: S.Expanded(), acc: List<&2, Layer>) -> Slots:
  match t:
    case S.SList{loc, xs}:
      Slots{xs, List.reverse(&2, Layer, acc)}
    case S.SLet{loc, binds, inner}:
      slots(inner, WLet{loc, binds} <> acc)
    case S.SLam{loc, v, inner}:
      slots(inner, WLam{loc, v} <> acc)
    case _:
      NoSlots{}

# renderExpansionError
def render(e: ExpErr) -> String:
  match e:
    case ListArityMismatch{loc, names, slots}:
      "list assignment arity mismatch: " ++ Nat.show(names) ++ " names for "
        ++ Nat.show(slots) ++ " values" ++ at.loc(loc)
    case DuplicatePatternVariable{loc, name}:
      "pattern binds " ++ name ++ " more than once" ++ at.loc(loc)
    case GuardUsesOwnBinder{loc, name}:
      "a guard mentions " ++ name ++ ", which its own pattern binds" ++ at.loc(loc)
    case MissingMain{}:
      "missing 'main' definition"

# Accessors
# ---------

def rights(n: Nat, +loc: L.Loc, e: S.Expanded()) -> S.Expanded():
  match n:
    case 0n:
      e
    case 1n+k:
      S.SRight{loc, rights(k, loc, e)}

# Element n of a list-shaped value (accessAt).
def access(+loc: L.Loc, n: Nat, e: S.Expanded()) -> S.Expanded():
  S.SLeft{loc, rights(n, loc, e)}

# Plain list assignments
# ----------------------

def intermediate.name(m: Maybe<&2, L.Pos>) -> String:
  match m:
    case Some{p}:
      match p:
        case L.Pos{line, col, off}:
          "__list_assignment_" ++ U32.show(line) ++ "_" ++ U32.show(col)
    case None{}:
      "__list_assignment"

def zip.slots(+ls: List<&2, Layer>, names: List<&2, L.Name>, xs: List<&2, S.Expanded()>) -> List<&2, S.ExpandedBind()>:
  match names:
    case Nil{}:
      []
    case Con{n, rest}:
      match xs:
        case Nil{}:
          []
        case Con{x, xrest}:
          S.Bind{n, wrap(ls, x)} <> zip.slots(ls, rest, xrest)

def accessors(names: List<&2, L.Name>, +loc: L.Loc, +i: Nat, +src: S.Expanded()) -> List<&2, S.ExpandedBind()>:
  match names:
    case Nil{}:
      []
    case Con{n, rest}:
      S.Bind{n, access(loc, i, src)} <> accessors(rest, loc, 1n+i, src)

def plain.slots(+loc: L.Loc, +names: List<&2, L.Name>, xs: List<&2, S.Expanded()>,
                ls: List<&2, Layer>, same: Bool) -> R(List<&2, S.ExpandedBind()>):
  match same:
    case True{}:
      Done{zip.slots(ls, names, xs)}
    case False{}:
      Fail{ListArityMismatch{loc, List.length(&2, L.Name, names), List.length(&2, S.Expanded(), xs)}}

def plain.none(+loc: L.Loc, names: List<&2, L.Name>, body: S.Expanded()) -> R(List<&2, S.ExpandedBind()>):
  +name = intermediate.name(L.start(loc))
  Done{S.Bind{L.Name{L.GenIn{"listAssignmentIntermediate", loc}, name}, body}
       <> accessors(names, loc, 0n, S.SVar{loc, name})}

# `[a, b, c] = e` (expandPlainListAssignment).
def plain(+loc: L.Loc, +names: List<&2, L.Name>, +body: S.Expanded(), s: Slots) -> R(List<&2, S.ExpandedBind()>):
  match s:
    case Slots{+xs, ls}:
      plain.slots(loc, names, xs, ls,
                  Nat.is_eq(List.length(&2, L.Name, names), List.length(&2, S.Expanded(), xs)))
    case NoSlots{}:
      plain.none(loc, names, body)

# A list definition, its body already expanded (expandDef's ListDefF).
def expand.list(+loc: L.Loc, +names: List<&2, L.Name>, +body: S.Expanded()) -> R(List<&2, S.ExpandedBind()>):
  plain(loc, names, body, slots(body, []))

# Multi-pattern lambdas
# ---------------------

# The binder of lambda parameter i: its variable, or a generated name for
# any other pattern (lambdaVarNames).
def lam.name(+i: Nat, lp: S.ExpandedLPat()) -> L.Name:
  match lp:
    case S.LPat{+loc, p}:
      match p:
        case S.PVar{name}:
          name
        case _:
          L.Name{L.GenIn{"lambda pattern", loc}, "__lambda_pattern_" ++ Nat.show(i)}

def lam.names(ps: List<&2, S.ExpandedLPat()>, +i: Nat) -> List<&2, L.Name>:
  match ps:
    case Nil{}:
      []
    case Con{p, rest}:
      lam.name(i, p) <> lam.names(rest, 1n+i)

# One parameter's destructuring around the body (applyDestructure), at the
# lambda's location lt; the parameter starts at loc. A refinement `(p : T)`
# binds the checked value: `\(x : T) -> body` is `\v -> let x = T checks v
# in body`, as `let x : T = v` would be, and an annotated pattern that is no
# variable is destructured from that binding. Annotations further in are
# guards of the parameter's destructuring case, whose fallback aborts, so a
# parameter's guard that fails aborts as a refinement does.
def destructure(+lt: L.Loc, +loc: L.Loc, p: S.ExpandedPat(), +v: String, inner: S.Expanded()) -> S.Expanded():
  match p:
    case S.PVar{name}:
      inner
    case S.PAnn{q, t}:
      match q:
        case S.PVar{name}:
          S.SLet{lt, [S.Bind{name, S.SCheck{loc, L.KRefine{}, t, S.SVar{lt, v}}}], inner}
        case other:
          S.SLet{lt, [S.Bind{L.Name{L.GenIn{"annotated lambda pattern", loc}, v ++ "_checked"},
                             S.SCheck{loc, L.KRefine{}, t, S.SVar{lt, v}}}],
            destructure(lt, loc, other, v ++ "_checked", inner)}
    case other:
      S.SCase{lt, S.SVar{lt, v},
        [S.Alt{other, inner},
         S.Alt{S.PIgnore{}, S.abort.term(Empty, Unit, Empty, L.KCase{}, loc,
                                   S.SStr{loc, "lambda argument does not match its pattern"})}], Unit{}}

def destructure.all(ps: List<&2, S.ExpandedLPat()>, +lt: L.Loc, names: List<&2, L.Name>, body: S.Expanded()) -> S.Expanded():
  match ps:
    case Nil{}:
      body
    case Con{lp, rest}:
      match lp:
        case S.LPat{loc, p}:
          match names:
            case Nil{}:
              body
            case Con{n, nrest}:
              destructure(lt, loc, p, L.Name.text(n), destructure.all(rest, lt, nrest, body))

# A lambda takes its body's annotation (LamP).
def lams(names: List<&2, L.Name>, +anno: L.Loc, body: S.Expanded()) -> S.Expanded():
  match names:
    case Nil{}:
      body
    case Con{n, rest}:
      S.SLam{anno, n, lams(rest, anno, body)}

def multi.lambda.go(+names: List<&2, L.Name>, +d: S.Expanded()) -> S.Expanded():
  lams(names, S.loc(Empty, Unit, Empty, d), d)

# \p1 p2 ... -> body (buildMultiLambda).
def multi.lambda(+lt: L.Loc, +pats: List<&2, S.ExpandedLPat()>, body: S.Expanded()) -> S.Expanded():
  +names = lam.names(pats, 0n)
  multi.lambda.go(names, destructure.all(pats, lt, names, body))

# What a pattern may not do
# -------------------------

# The names a pattern binds, left to right, ahead of acc (patternBinders).
def binders(p: S.ExpandedPat(), acc: List<&2, String>) -> List<&2, String>:
  match p:
    case S.PVar{name}:
      L.Name.text(name) <> acc
    case S.PAnn{q, t}:
      binders(q, acc)
    case S.PPair{a, b}:
      binders(a, binders(b, acc))
    case _:
      acc

# The pattern's guards, a guard after the pattern it annotates, ahead of acc.
def guards(p: S.ExpandedPat(), acc: List<&2, S.Expanded()>) -> List<&2, S.Expanded()>:
  match p:
    case S.PAnn{q, t}:
      guards(q, t <> acc)
    case S.PPair{a, b}:
      guards(a, guards(b, acc))
    case _:
      acc

def named(xs: List<&2, String>, +n: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      String.eq(x, n) || named(rest, n)

def first.dup.if(dup: Bool, +n: String, later: Maybe<&2, String>) -> Maybe<&2, String>:
  match dup:
    case True{}:
      Some{n}
    case False{}:
      later

# The first name that comes twice.
def first.dup(xs: List<&2, String>) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, +rest}:
      first.dup.if(named(rest, x), x, first.dup(rest))

def first.in.if(yes: Bool, +n: String, later: Maybe<&2, String>) -> Maybe<&2, String>:
  match yes:
    case True{}:
      Some{n}
    case False{}:
      later

# The first of xs among names.
def first.in(xs: List<&2, String>, +names: List<&2, String>) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, rest}:
      first.in.if(named(names, x), x, first.in(rest, names))

# What a free-variable walk visits.
type FN is Data:
  FT{+t: S.Expanded()}
  FTs{+xs: List<&2, S.Expanded()>}
  FBs{+bs: List<&2, S.ExpandedBind()>}
  FAs{+alts: List<&2, S.ExpandedAlt()>}
  FP{+p: S.ExpandedPat()}

def set.minus(xs: List<&2, String>, s: Set()) -> Set():
  match xs:
    case Nil{}:
      s
    case Con{x, rest}:
      set.minus(rest, Set.del(s, x))

def bind.names(bs: List<&2, S.ExpandedBind()>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          L.Name.text(name) <> bind.names(rest)

def set.plus(a: Set(), b: Set()) -> Set():
  Map.union(&2, Unit, a, b)

# The names a term uses without binding them (freeVars), through
# foldMapScoped's scopes: a lambda's body, a let's values and body, a case
# alternative's body, and the terms in its pattern's annotations with no
# extra binders.
def free(+fuel: Nat, n: FN) -> Set():
  match fuel:
    case 0n:
      Set.new()
    case 1n+f:
      match n:
        case FT{t}:
          match t:
            case S.SVar{loc, name}:
              Set.add(Set.new(), name)
            case S.SApp{loc, a, b}:
              set.plus(free(f, FT{a}), free(f, FT{b}))
            case S.SLam{loc, v, body}:
              Set.del(free(f, FT{body}), L.Name.text(v))
            case S.SPair{loc, a, b}:
              set.plus(free(f, FT{a}), free(f, FT{b}))
            case S.SCheck{loc, k, a, b}:
              set.plus(free(f, FT{a}), free(f, FT{b}))
            case S.SIte{loc, a, b, c}:
              set.plus(free(f, FT{a}), set.plus(free(f, FT{b}), free(f, FT{c})))
            case S.SLeft{loc, x}:
              free(f, FT{x})
            case S.SRight{loc, x}:
              free(f, FT{x})
            case S.SRec{loc, a, b, c}:
              set.plus(free(f, FT{a}), set.plus(free(f, FT{b}), free(f, FT{c})))
            case S.SLet{loc, +binds, body}:
              set.minus(bind.names(binds), set.plus(free(f, FBs{binds}), free(f, FT{body})))
            case S.SList{loc, xs}:
              free(f, FTs{xs})
            case S.SCase{loc, scrut, alts, w}:
              set.plus(free(f, FT{scrut}), free(f, FAs{alts}))
            case _:
              Set.new()
        case FTs{xs}:
          match xs:
            case Nil{}:
              Set.new()
            case Con{x, rest}:
              set.plus(free(f, FT{x}), free(f, FTs{rest}))
        case FBs{bs}:
          match bs:
            case Nil{}:
              Set.new()
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  set.plus(free(f, FT{val}), free(f, FBs{rest}))
        case FAs{alts}:
          match alts:
            case Nil{}:
              Set.new()
            case Con{alt, rest}:
              match alt:
                case S.Alt{+p, body}:
                  set.plus(free(f, FP{p}),
                    set.plus(set.minus(binders(p, []), free(f, FT{body})), free(f, FAs{rest})))
        case FP{p}:
          match p:
            case S.PAnn{q, t}:
              set.plus(free(f, FP{q}), free(f, FT{t}))
            case S.PPair{a, b}:
              set.plus(free(f, FP{a}), free(f, FP{b}))
            case _:
              Set.new()

def fuel() -> Nat:
  U32.to_nat(4294967295)

# The first name a guard uses that the pattern binds, in guard order and
# each guard's names ascending.
def own.binder(gs: List<&2, S.Expanded()>, +names: List<&2, String>) -> Maybe<&2, String>:
  match gs:
    case Nil{}:
      None{}
    case Con{g, rest}:
      Maybe.or(&2, String, first.in(Set.to_list(free(fuel(), FT{g})), names), own.binder(rest, names))

def pat.guarded(m: Maybe<&2, String>, +loc: L.Loc, p: S.ExpandedPat()) -> R(S.ExpandedPat()):
  match m:
    case Some{n}:
      Fail{GuardUsesOwnBinder{loc, n}}
    case None{}:
      Done{p}

def pat.dup(m: Maybe<&2, String>, +loc: L.Loc, +names: List<&2, String>, +p: S.ExpandedPat()) -> R(S.ExpandedPat()):
  match m:
    case Some{n}:
      Fail{DuplicatePatternVariable{loc, n}}
    case None{}:
      pat.guarded(own.binder(guards(p, []), names), loc, p)

def pat.names(+names: List<&2, String>, +loc: L.Loc, +p: S.ExpandedPat()) -> R(S.ExpandedPat()):
  pat.dup(first.dup(names), loc, names, p)

# What a pattern may not do while the scoping of its guards is undecided
# (checkPattern): bind one name twice, or mention in a guard a name the same
# pattern binds.
def pat.ok(+loc: L.Loc, +p: S.ExpandedPat()) -> R(S.ExpandedPat()):
  pat.names(binders(p, []), loc, p)

def lpats.ok(ps: List<&2, S.ExpandedLPat()>) -> R(List<&2, S.ExpandedLPat()>):
  match ps:
    case Nil{}:
      Done{[]}
    case Con{lp, rest}:
      match lp:
        case S.LPat{+loc, +p}:
          do Result<&2, &2, ExpErr, List<&2, S.ExpandedLPat()>>:
            p2 : S.ExpandedPat() <- pat.ok(loc, p)
            r2 : List<&2, S.ExpandedLPat()> <- lpats.ok(rest)
            return S.LPat{loc, p2} <> r2

# The expansion walk
# ------------------

def vt(v: EV) -> S.Expanded():
  match v:
    case VT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def vp(v: EV) -> S.ExpandedPat():
  match v:
    case VP{p}:
      p
    case _:
      S.PIgnore{}

def vlps(v: EV) -> List<&2, S.ExpandedLPat()>:
  match v:
    case VLPs{ps}:
      ps
    case _:
      []

def vts(v: EV) -> List<&2, S.Expanded()>:
  match v:
    case VTs{xs}:
      xs
    case _:
      []

def vbs(v: EV) -> List<&2, S.ExpandedBind()>:
  match v:
    case VBs{bs}:
      bs
    case _:
      []

def vas(v: EV) -> List<&2, S.ExpandedAlt()>:
  match v:
    case VAs{alts}:
      alts
    case _:
      []

def ok.t(t: S.Expanded()) -> R(EV):
  Done{VT{t}}

def ok.bs(bs: List<&2, S.ExpandedBind()>) -> R(EV):
  Done{VBs{bs}}

def binds.then(bs: List<&2, S.ExpandedBind()>, rest: EV) -> R(EV):
  Done{VBs{List.append(&2, S.ExpandedBind(), bs, vbs(rest))}}

# Expand a term, pattern or list of them; errors surface in source order.
def ex(+fuel: Nat, n: EN) -> R(EV):
  match fuel:
    case 0n:
      Fail{MissingMain{}}
    case 1n+f:
      match n:
        case ETerm{t}:
          match t:
            case S.SApp{loc, a, b}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, ETerm{a})
                b2 : EV <- ex(f, ETerm{b})
                return VT{S.SApp{loc, vt(a2), vt(b2)}}
            case S.SLam{loc, v, body}:
              do Result<&2, &2, ExpErr, EV>:
                b2 : EV <- ex(f, ETerm{body})
                return VT{S.SLam{loc, v, vt(b2)}}
            case S.SLamPat{loc, pats, body, w}:
              do Result<&2, &2, ExpErr, EV>:
                p2 : EV <- ex(f, ELPats{pats})
                ps : List<&2, S.ExpandedLPat()> <- lpats.ok(vlps(p2))
                b2 : EV <- ex(f, ETerm{body})
                return VT{multi.lambda(loc, ps, vt(b2))}
            case S.SPair{loc, a, b}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, ETerm{a})
                b2 : EV <- ex(f, ETerm{b})
                return VT{S.SPair{loc, vt(a2), vt(b2)}}
            case S.SCheck{loc, k, a, b}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, ETerm{a})
                b2 : EV <- ex(f, ETerm{b})
                return VT{S.SCheck{loc, k, vt(a2), vt(b2)}}
            case S.SIte{loc, a, b, c}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, ETerm{a})
                b2 : EV <- ex(f, ETerm{b})
                c2 : EV <- ex(f, ETerm{c})
                return VT{S.SIte{loc, vt(a2), vt(b2), vt(c2)}}
            case S.SLeft{loc, x}:
              do Result<&2, &2, ExpErr, EV>:
                x2 : EV <- ex(f, ETerm{x})
                return VT{S.SLeft{loc, vt(x2)}}
            case S.SRight{loc, x}:
              do Result<&2, &2, ExpErr, EV>:
                x2 : EV <- ex(f, ETerm{x})
                return VT{S.SRight{loc, vt(x2)}}
            case S.SRec{loc, a, b, c}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, ETerm{a})
                b2 : EV <- ex(f, ETerm{b})
                c2 : EV <- ex(f, ETerm{c})
                return VT{S.SRec{loc, vt(a2), vt(b2), vt(c2)}}
            case S.SLet{loc, binds, body}:
              do Result<&2, &2, ExpErr, EV>:
                b1 : EV <- ex(f, EBinds{binds})
                b2 : EV <- ex(f, ETerm{body})
                return VT{S.SLet{loc, vbs(b1), vt(b2)}}
            case S.SLetSugar{loc, defs, body, w}:
              do Result<&2, &2, ExpErr, EV>:
                b1 : EV <- ex(f, EDefs{defs})
                b2 : EV <- ex(f, ETerm{body})
                return VT{S.SLet{loc, vbs(b1), vt(b2)}}
            case S.SList{loc, xs}:
              do Result<&2, &2, ExpErr, EV>:
                x2 : EV <- ex(f, ETerms{xs})
                return VT{S.SList{loc, vts(x2)}}
            case S.SCase{+loc, scrut, alts, w}:
              do Result<&2, &2, ExpErr, EV>:
                s2 : EV <- ex(f, ETerm{scrut})
                a2 : EV <- ex(f, EAlts{loc, alts})
                return VT{S.SCase{loc, vt(s2), vas(a2), w}}
            case S.SVar{loc, name}:
              ok.t(S.SVar{loc, name})
            case S.SZero{loc}:
              ok.t(S.SZero{loc})
            case S.SChurch{loc, n}:
              ok.t(S.SChurch{loc, n})
            case S.SInt{loc, n}:
              ok.t(S.SInt{loc, n})
            case S.SStr{loc, str}:
              ok.t(S.SStr{loc, str})
            case S.SLamN{loc, n, v, body, w}:
              Empty.absurd(R(EV), w)
        case EPat{p}:
          match p:
            case S.PAnn{q, t}:
              do Result<&2, &2, ExpErr, EV>:
                q2 : EV <- ex(f, EPat{q})
                t2 : EV <- ex(f, ETerm{t})
                return VP{S.PAnn{vp(q2), vt(t2)}}
            case S.PPair{a, b}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, EPat{a})
                b2 : EV <- ex(f, EPat{b})
                return VP{S.PPair{vp(a2), vp(b2)}}
            case S.PVar{name}:
              Done{VP{S.PVar{name}}}
            case S.PInt{n}:
              Done{VP{S.PInt{n}}}
            case S.PStr{str}:
              Done{VP{S.PStr{str}}}
            case S.PIgnore{}:
              Done{VP{S.PIgnore{}}}
        case ELPats{ps}:
          match ps:
            case Nil{}:
              Done{VLPs{[]}}
            case Con{lp, rest}:
              match lp:
                case S.LPat{loc, p}:
                  do Result<&2, &2, ExpErr, EV>:
                    p2 : EV <- ex(f, EPat{p})
                    r2 : EV <- ex(f, ELPats{rest})
                    return VLPs{S.LPat{loc, vp(p2)} <> vlps(r2)}
        case ETerms{xs}:
          match xs:
            case Nil{}:
              Done{VTs{[]}}
            case Con{x, rest}:
              do Result<&2, &2, ExpErr, EV>:
                x2 : EV <- ex(f, ETerm{x})
                r2 : EV <- ex(f, ETerms{rest})
                return VTs{vt(x2) <> vts(r2)}
        case EBinds{bs}:
          match bs:
            case Nil{}:
              Done{VBs{[]}}
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  do Result<&2, &2, ExpErr, EV>:
                    v2 : EV <- ex(f, ETerm{val})
                    r2 : EV <- ex(f, EBinds{rest})
                    return VBs{S.Bind{name, vt(v2)} <> vbs(r2)}
        case EDefs{ds}:
          match ds:
            case Nil{}:
              Done{VBs{[]}}
            case Con{d, rest}:
              match d:
                case S.DSingle{name, body}:
                  do Result<&2, &2, ExpErr, EV>:
                    b2 : EV <- ex(f, ETerm{body})
                    r2 : EV <- ex(f, EDefs{rest})
                    binds.then([S.Bind{name, vt(b2)}], r2)
                case S.DChecked{name, cloc, check, body}:
                  do Result<&2, &2, ExpErr, EV>:
                    c2 : EV <- ex(f, ETerm{check})
                    b2 : EV <- ex(f, ETerm{body})
                    r2 : EV <- ex(f, EDefs{rest})
                    binds.then([S.Bind{name, S.SCheck{cloc, L.KRefine{}, vt(c2), vt(b2)}}], r2)
                case S.DList{loc, names, body}:
                  do Result<&2, &2, ExpErr, EV>:
                    b2 : EV <- ex(f, ETerm{body})
                    bs : List<&2, S.ExpandedBind()> <- expand.list(loc, names, vt(b2))
                    r2 : EV <- ex(f, EDefs{rest})
                    binds.then(bs, r2)
        case EAlts{+loc, alts}:
          match alts:
            case Nil{}:
              Done{VAs{[]}}
            case Con{alt, rest}:
              match alt:
                case S.Alt{p, body}:
                  do Result<&2, &2, ExpErr, EV>:
                    p2 : EV <- ex(f, EPat{p})
                    q : S.ExpandedPat() <- pat.ok(loc, vp(p2))
                    b2 : EV <- ex(f, ETerm{body})
                    r2 : EV <- ex(f, EAlts{loc, rest})
                    return VAs{S.Alt{q, vt(b2)} <> vas(r2)}

def term(t: S.Parsed()) -> R(S.Expanded()):
  do Result<&2, &2, ExpErr, S.Expanded()>:
    v : EV <- ex(fuel(), ETerm{t})
    return vt(v)

def ebinds(bs: List<&2, S.ExpandedBind()>) -> List<&2, S.EItem>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          S.EBind{name, val} <> ebinds(rest)

def module.then(bs: EV, rest: List<&2, S.EItem>) -> R(List<&2, S.EItem>):
  Done{List.append(&2, S.EItem, ebinds(vbs(bs)), rest)}

# A module's items, expanded (expandModule).
def module(items: List<&2, S.Item>) -> R(List<&2, S.EItem>):
  match items:
    case Nil{}:
      Done{[]}
    case Con{item, rest}:
      match item:
        case S.IImport{imp}:
          do Result<&2, &2, ExpErr, List<&2, S.EItem>>:
            r : List<&2, S.EItem> <- module(rest)
            return S.EImport{imp} <> r
        case S.IDef{d}:
          do Result<&2, &2, ExpErr, List<&2, S.EItem>>:
            bs : EV <- ex(fuel(), EDefs{[d]})
            r : List<&2, S.EItem> <- module(rest)
            module.then(bs, r)
