import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Show.bend as Sh

# Expansion (haskell-final's Telomare.Expand): multi-pattern lambdas become
# single-binder lambdas over case destructuring, let definitions become plain
# bindings, a refinement `x : T = v` becomes a check, and list assignments
# and UDT declarations become their per-slot bindings.

type ExpErr is Data:
  ListArityMismatch{+loc: L.Loc, +names: Nat, +slots: Nat}
  UDTBodyNotList{+loc: L.Loc, +tname: String, +desc: String}
  UDTArityMismatch{+loc: L.Loc, +tname: String, +names: Nat, +slots: Nat}
  MissingMain{}

# The lets and lambdas a list assignment's list literal sits under, outermost
# first: every slot is re-wrapped in them.
type Layer is Data:
  WLet{+loc: L.Loc, +binds: List<&2, S.Bind>}
  WLam{+loc: L.Loc, +v: L.Name}

# The slots of a list literal under lets and lambdas (listAssignmentSlots),
# with the layers above it, innermost first in `acc`.
type Slots is Data:
  Slots{+xs: List<&2, S.Surf>, +layers: List<&2, Layer>}
  NoSlots{}

# A UDT body's slots: lets around a list literal (udtSlots). Anything else is
# an error naming what was found instead.
type USlots is Data:
  USlots{+xs: List<&2, S.Surf>, +layers: List<&2, Layer>}
  UNotList{+desc: String}

type EN is Data:
  ETerm{+t: S.Surf}
  EPat{+p: S.Pat}
  ELPats{+ps: List<&2, S.LPat>}
  ETerms{+xs: List<&2, S.Surf>}
  EBinds{+bs: List<&2, S.Bind>}
  EDefs{+ds: List<&2, S.Def>}
  EAlts{+alts: List<&2, S.Alt>}

type EV is Data:
  VT{+t: S.Surf}
  VP{+p: S.Pat}
  VLPs{+ps: List<&2, S.LPat>}
  VTs{+xs: List<&2, S.Surf>}
  VBs{+bs: List<&2, S.Bind>}
  VAs{+alts: List<&2, S.Alt>}

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

def wrap(ls: List<&2, Layer>, t: S.Surf) -> S.Surf:
  match ls:
    case Nil{}:
      t
    case Con{l, rest}:
      match l:
        case WLet{loc, binds}:
          S.SLet{loc, binds, wrap(rest, t)}
        case WLam{loc, v}:
          S.SLam{loc, v, wrap(rest, t)}

def wrap.all(+ls: List<&2, Layer>, ts: List<&2, S.Surf>) -> List<&2, S.Surf>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      wrap(ls, t) <> wrap.all(ls, rest)

def slots(t: S.Surf, acc: List<&2, Layer>) -> Slots:
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
    case UDTBodyNotList{loc, tname, desc}:
      "UDT body for [" ++ tname ++ "] must reduce to a list literal; got: "
        ++ desc ++ at.loc(loc)
    case UDTArityMismatch{loc, tname, names, slots}:
      "UDT declaration for [" ++ tname ++ "] has " ++ Nat.show(names)
        ++ " names for " ++ Nat.show(slots) ++ " value slots; expected one type name "
        ++ "plus one name per slot" ++ at.loc(loc)
    case MissingMain{}:
      "missing 'main' definition"

# A few words for what a UDT body turned out to be (Haskell shows the node).
def describe(t: S.Surf) -> String:
  match t:
    case S.SInt{loc, n}:
      "IntUPF " ++ U32.show(n)
    case S.SStr{loc, s}:
      "StringUPF " ++ Sh.string(s)
    case S.SVar{loc, name}:
      "UnprocessedParsedTermL (VarF " ++ Sh.string(name) ++ ")"
    case S.SPair{loc, a, b}:
      "UnprocessedParsedTermB (PairSF () ())"
    case S.SApp{loc, f, x}:
      "UnprocessedParsedTermL (AppF () ())"
    case S.SLam{loc, v, b}:
      "UnprocessedParsedTermL (LamF " ++ Sh.string(L.Name.text(v)) ++ " ())"
    case _:
      "a term that is not a list literal"

def uslots(t: S.Surf, acc: List<&2, Layer>) -> USlots:
  match t:
    case S.SList{loc, xs}:
      USlots{xs, List.reverse(&2, Layer, acc)}
    case S.SLet{loc, binds, inner}:
      uslots(inner, WLet{loc, binds} <> acc)
    case other:
      UNotList{describe(other)}

# Accessors
# ---------

def rights(n: Nat, +loc: L.Loc, e: S.Surf) -> S.Surf:
  match n:
    case 0n:
      e
    case 1n+k:
      S.SRight{loc, rights(k, loc, e)}

# Element n of a list-shaped value (accessAt).
def access(+loc: L.Loc, n: Nat, e: S.Surf) -> S.Surf:
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

def zip.slots(+ls: List<&2, Layer>, names: List<&2, L.Name>, xs: List<&2, S.Surf>) -> List<&2, S.Bind>:
  match names:
    case Nil{}:
      []
    case Con{n, rest}:
      match xs:
        case Nil{}:
          []
        case Con{x, xrest}:
          S.Bind{n, wrap(ls, x)} <> zip.slots(ls, rest, xrest)

def accessors(names: List<&2, L.Name>, +loc: L.Loc, +i: Nat, +src: S.Surf) -> List<&2, S.Bind>:
  match names:
    case Nil{}:
      []
    case Con{n, rest}:
      S.Bind{n, access(loc, i, src)} <> accessors(rest, loc, 1n+i, src)

def plain.slots(+loc: L.Loc, +names: List<&2, L.Name>, xs: List<&2, S.Surf>,
                ls: List<&2, Layer>, same: Bool) -> R(List<&2, S.Bind>):
  match same:
    case True{}:
      Done{zip.slots(ls, names, xs)}
    case False{}:
      Fail{ListArityMismatch{loc, List.length(&2, L.Name, names), List.length(&2, S.Surf, xs)}}

def plain.none(+loc: L.Loc, names: List<&2, L.Name>, body: S.Surf) -> R(List<&2, S.Bind>):
  +name = intermediate.name(L.start(loc))
  Done{S.Bind{L.Name{L.GenIn{"listAssignmentIntermediate", loc}, name}, body}
       <> accessors(names, loc, 0n, S.SVar{loc, name})}

# `[a, b, c] = e` where e is not a UDT (expandPlainListAssignment).
def plain(+loc: L.Loc, +names: List<&2, L.Name>, +body: S.Surf, s: Slots) -> R(List<&2, S.Bind>):
  match s:
    case Slots{+xs, ls}:
      plain.slots(loc, names, xs, ls,
                  Nat.is_eq(List.length(&2, L.Name, names), List.length(&2, S.Surf, xs)))
    case NoSlots{}:
      plain.none(loc, names, body)

# UDT declarations
# ----------------

# \__udt_v -> if dEqual (left __udt_v) h then right __udt_v else abort "not T"
def validator(+loc: L.Loc, tname: String, +h: String) -> S.Surf:
  S.SLam{loc, L.Name{L.GenIn{"annotated pattern lambda", loc}, "__udt_v"},
    S.SIte{loc,
      S.SApp{loc, S.SApp{loc, S.SVar{loc, "dEqual"}, S.SLeft{loc, S.SVar{loc, "__udt_v"}}},
             S.SVar{loc, h}},
      S.SRight{loc, S.SVar{loc, "__udt_v"}},
      S.SApp{loc, S.SVar{loc, "abort"}, S.SStr{loc, "not " ++ tname}}}}

def generated(+parent: L.Loc, +name: String) -> L.Name:
  L.Name{L.GenIn{name, parent}, name}

def udt.core(names: List<&2, L.Name>, +loc: L.Loc, +i: Nat, +src: S.Surf) -> List<&2, S.Bind>:
  accessors(names, loc, i, src)

def udt.hoisted(names: List<&2, L.Name>, +loc: L.Loc, +h: L.Name, +tname: String,
                +ls: List<&2, Layer>, slots: List<&2, S.Surf>) -> List<&2, S.Bind>:
  match names:
    case Nil{}:
      []
    case Con{n, rest}:
      match slots:
        case Nil{}:
          []
        case Con{x, xrest}:
          S.Bind{n, S.SLet{loc,
                  [S.Bind{h, S.SVar{loc, "__udt_" ++ tname ++ "_hash"}},
                   S.Bind{L.Name{loc, tname}, validator(loc, tname, L.Name.text(h))}],
                  wrap(ls, x)}}
            <> udt.hoisted(rest, loc, h, tname, ls, xrest)

def udt.build(+loc: L.Loc, +names: List<&2, L.Name>, +tname: String, +h: L.Name,
              +xs: List<&2, S.Surf>, +ls: List<&2, Layer>) -> List<&2, S.Bind>:
  +inter = "__udt_" ++ tname
  +core = List.take(&2, S.Surf, xs, 2n)
  +ncore = {1n+List.length(&2, S.Surf, core) : Nat}
  +wrapper = {S.SLam{loc, h,
    S.SLet{loc, [S.Bind{L.Name{loc, tname}, validator(loc, tname, L.Name.text(h))}],
      wrap(ls, S.SList{loc, S.SVar{loc, L.Name.text(h)} <> S.SVar{loc, tname} <> core})}} : S.Surf}
  S.Bind{generated(loc, inter), S.SApp{loc, wrapper, S.SHash{loc, wrapper}}}
    <> S.Bind{generated(loc, inter ++ "_hash"), access(loc, 0n, S.SVar{loc, inter})}
    <> List.append(&2, S.Bind,
         udt.core(List.take(&2, L.Name, names, ncore), loc, 1n, S.SVar{loc, inter}),
         udt.hoisted(List.drop(&2, L.Name, names, ncore), loc, h, tname, ls,
                     List.drop(&2, S.Surf, xs, 2n)))

def udt.check(+loc: L.Loc, +names: List<&2, L.Name>, +tname: String, +h: L.Name,
              +xs: List<&2, S.Surf>, +ls: List<&2, Layer>, ok: Bool) -> R(List<&2, S.Bind>):
  match ok:
    case True{}:
      Done{udt.build(loc, names, tname, h, xs, ls)}
    case False{}:
      Fail{UDTArityMismatch{loc, tname, List.length(&2, L.Name, names), List.length(&2, S.Surf, xs)}}

def udt.slots(+loc: L.Loc, +names: List<&2, L.Name>, +tname: String, +h: L.Name, s: USlots) ->
  R(List<&2, S.Bind>):
  match s:
    case USlots{+xs, ls}:
      udt.check(loc, names, tname, h, xs, ls,
                Nat.is_eq(List.length(&2, L.Name, names), 1n+List.length(&2, S.Surf, xs)))
    case UNotList{desc}:
      Fail{UDTBodyNotList{loc, tname, desc}}

def udt.plain(names: List<&2, L.Name>, +loc: L.Loc, +i: Nat, +body: S.Surf) -> List<&2, S.Bind>:
  accessors(names, loc, i, body)

def udt.body(+loc: L.Loc, +names: List<&2, L.Name>, +tname: String, body: S.Surf) -> R(List<&2, S.Bind>):
  match body:
    case S.SLam{l, h, inner}:
      udt.slots(loc, names, tname, h, uslots(inner, []))
    case +other:
      Done{udt.plain(names, loc, 0n, other)}

# `[T, mk, unT, ops...] = \h -> lets [s0, s1, ...]` (expandUDTLocated).
def udt(+loc: L.Loc, +names: List<&2, L.Name>, body: S.Surf) -> R(List<&2, S.Bind>):
  match names:
    case Nil{}:
      Done{[]}
    case Con{first, rest}:
      udt.body(loc, names, L.Name.text(first), body)

def is.upper.first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_upper(c)

# A list definition is a UDT when its first name is capitalised and its body
# a lambda.
def is.udt(names: List<&2, L.Name>, body: S.Surf) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{first, rest}:
      match body:
        case S.SLam{loc, v, b}:
          is.upper.first(L.Name.text(first))
        case _:
          False{}

def list.def(+loc: L.Loc, +names: List<&2, L.Name>, +body: S.Surf, isudt: Bool) -> R(List<&2, S.Bind>):
  match isudt:
    case True{}:
      udt(loc, names, body)
    case False{}:
      plain(loc, names, body, slots(body, []))

# One definition, its terms already expanded (expandDef).
def expand.def(d: S.Def) -> R(List<&2, S.Bind>):
  match d:
    case S.DSingle{name, body}:
      Done{[S.Bind{name, body}]}
    case S.DChecked{name, cloc, check, body}:
      Done{[S.Bind{name, S.SCheck{cloc, check, body}}]}
    case S.DList{+loc, +names, +body}:
      list.def(loc, names, body, is.udt(names, body))

# Multi-pattern lambdas
# ---------------------

# The binder of lambda parameter i: its variable, or a generated name for
# any other pattern (lambdaVarNames).
def lam.name(+i: Nat, lp: S.LPat) -> L.Name:
  match lp:
    case S.LPat{+loc, p}:
      match p:
        case S.PVar{name}:
          name
        case _:
          L.Name{L.GenIn{"lambda pattern", loc}, "__lambda_pattern_" ++ Nat.show(i)}

def lam.names(ps: List<&2, S.LPat>, +i: Nat) -> List<&2, L.Name>:
  match ps:
    case Nil{}:
      []
    case Con{p, rest}:
      lam.name(i, p) <> lam.names(rest, 1n+i)

# One parameter's destructuring around the body (applyDestructure).
def destructure(+lt: L.Loc, p: S.Pat, +v: String, inner: S.Surf) -> S.Surf:
  match p:
    case S.PVar{name}:
      inner
    case S.PAnn{q, +t}:
      S.SCase{lt, S.SApp{S.loc(t), t, S.SVar{lt, v}}, [S.Alt{q, inner}]}
    case other:
      S.SCase{lt, S.SVar{lt, v},
        [S.Alt{other, inner},
         S.Alt{S.PIgnore{}, S.SApp{lt, S.SVar{lt, "abort"},
                                   S.SStr{lt, "buildMultiLambda: pattern not reached"}}}]}

def destructure.all(ps: List<&2, S.LPat>, +lt: L.Loc, names: List<&2, L.Name>, body: S.Surf) -> S.Surf:
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
              destructure(lt, p, L.Name.text(n), destructure.all(rest, lt, nrest, body))

# A lambda takes its body's annotation (LamP).
def lams(names: List<&2, L.Name>, +anno: L.Loc, body: S.Surf) -> S.Surf:
  match names:
    case Nil{}:
      body
    case Con{n, rest}:
      S.SLam{anno, n, lams(rest, anno, body)}

def multi.lambda.go(+names: List<&2, L.Name>, +d: S.Surf) -> S.Surf:
  lams(names, S.loc(d), d)

# \p1 p2 ... -> body (buildMultiLambda).
def multi.lambda(+lt: L.Loc, +pats: List<&2, S.LPat>, body: S.Surf) -> S.Surf:
  +names = lam.names(pats, 0n)
  multi.lambda.go(names, destructure.all(pats, lt, names, body))

# The expansion walk
# ------------------

def vt(v: EV) -> S.Surf:
  match v:
    case VT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def vp(v: EV) -> S.Pat:
  match v:
    case VP{p}:
      p
    case _:
      S.PIgnore{}

def vlps(v: EV) -> List<&2, S.LPat>:
  match v:
    case VLPs{ps}:
      ps
    case _:
      []

def vts(v: EV) -> List<&2, S.Surf>:
  match v:
    case VTs{xs}:
      xs
    case _:
      []

def vbs(v: EV) -> List<&2, S.Bind>:
  match v:
    case VBs{bs}:
      bs
    case _:
      []

def vas(v: EV) -> List<&2, S.Alt>:
  match v:
    case VAs{alts}:
      alts
    case _:
      []

def ok.t(t: S.Surf) -> R(EV):
  Done{VT{t}}

def ok.bs(bs: List<&2, S.Bind>) -> R(EV):
  Done{VBs{bs}}

def binds.then(bs: List<&2, S.Bind>, rest: EV) -> R(EV):
  Done{VBs{List.append(&2, S.Bind, bs, vbs(rest))}}

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
            case S.SLamPat{loc, pats, body}:
              do Result<&2, &2, ExpErr, EV>:
                p2 : EV <- ex(f, ELPats{pats})
                b2 : EV <- ex(f, ETerm{body})
                return VT{multi.lambda(loc, vlps(p2), vt(b2))}
            case S.SPair{loc, a, b}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, ETerm{a})
                b2 : EV <- ex(f, ETerm{b})
                return VT{S.SPair{loc, vt(a2), vt(b2)}}
            case S.SCheck{loc, a, b}:
              do Result<&2, &2, ExpErr, EV>:
                a2 : EV <- ex(f, ETerm{a})
                b2 : EV <- ex(f, ETerm{b})
                return VT{S.SCheck{loc, vt(a2), vt(b2)}}
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
            case S.STrace{loc, x}:
              do Result<&2, &2, ExpErr, EV>:
                x2 : EV <- ex(f, ETerm{x})
                return VT{S.STrace{loc, vt(x2)}}
            case S.SHash{loc, x}:
              do Result<&2, &2, ExpErr, EV>:
                x2 : EV <- ex(f, ETerm{x})
                return VT{S.SHash{loc, vt(x2)}}
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
            case S.SLetSugar{loc, defs, body}:
              do Result<&2, &2, ExpErr, EV>:
                b1 : EV <- ex(f, EDefs{defs})
                b2 : EV <- ex(f, ETerm{body})
                return VT{S.SLet{loc, vbs(b1), vt(b2)}}
            case S.SList{loc, xs}:
              do Result<&2, &2, ExpErr, EV>:
                x2 : EV <- ex(f, ETerms{xs})
                return VT{S.SList{loc, vts(x2)}}
            case S.SCase{loc, scrut, alts}:
              do Result<&2, &2, ExpErr, EV>:
                s2 : EV <- ex(f, ETerm{scrut})
                a2 : EV <- ex(f, EAlts{alts})
                return VT{S.SCase{loc, vt(s2), vas(a2)}}
            case other:
              ok.t(other)
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
            case other:
              Done{VP{other}}
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
                    bs : List<&2, S.Bind> <- expand.def(S.DSingle{name, vt(b2)})
                    r2 : EV <- ex(f, EDefs{rest})
                    binds.then(bs, r2)
                case S.DChecked{name, cloc, check, body}:
                  do Result<&2, &2, ExpErr, EV>:
                    c2 : EV <- ex(f, ETerm{check})
                    b2 : EV <- ex(f, ETerm{body})
                    bs : List<&2, S.Bind> <- expand.def(S.DChecked{name, cloc, vt(c2), vt(b2)})
                    r2 : EV <- ex(f, EDefs{rest})
                    binds.then(bs, r2)
                case S.DList{loc, names, body}:
                  do Result<&2, &2, ExpErr, EV>:
                    b2 : EV <- ex(f, ETerm{body})
                    bs : List<&2, S.Bind> <- expand.def(S.DList{loc, names, vt(b2)})
                    r2 : EV <- ex(f, EDefs{rest})
                    binds.then(bs, r2)
        case EAlts{alts}:
          match alts:
            case Nil{}:
              Done{VAs{[]}}
            case Con{alt, rest}:
              match alt:
                case S.Alt{p, body}:
                  do Result<&2, &2, ExpErr, EV>:
                    p2 : EV <- ex(f, EPat{p})
                    b2 : EV <- ex(f, ETerm{body})
                    r2 : EV <- ex(f, EAlts{rest})
                    return VAs{S.Alt{vp(p2), vt(b2)} <> vas(r2)}

def fuel() -> Nat:
  U32.to_nat(4294967295)

def term(t: S.Surf) -> R(S.Surf):
  do Result<&2, &2, ExpErr, S.Surf>:
    v : EV <- ex(fuel(), ETerm{t})
    return vt(v)

def ebinds(bs: List<&2, S.Bind>) -> List<&2, S.EItem>:
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
