import Base
import ./Loc.bend as L

# The surface syntax (haskell-final's Telomare.IR.Surface): one plain type
# for the parsed, expanded and desugared stages, a Loc on every node where
# Haskell has a Cofree. The parser builds the sugar (SLamPat, SLetSugar);
# expansion turns it into single-binder lambdas and plain lets; desugaring
# removes SCase. SLamN exists only between annotateUnsizedCount and
# letsToApps: one of the n placeholder lambdas around a let binding with n
# recursion sites.

type Pat is Data:
  PVar{+name: L.Name}
  PAnn{+p: Pat, +t: Surf}
  PInt{+n: U32}
  PStr{+s: String}
  PIgnore{}
  PPair{+a: Pat, +b: Pat}

# A lambda parameter and where it starts.
type LPat is Data:
  LPat{+loc: L.Loc, +p: Pat}

# A definition as written: `name = body`, `name : check = body` (the check's
# Loc is the colon's), `[n1, n2, ...] = body` (Loc at the bracket).
type Def is Data:
  DSingle{+name: L.Name, +body: Surf}
  DChecked{+name: L.Name, +cloc: L.Loc, +check: Surf, +body: Surf}
  DList{+loc: L.Loc, +names: List<&2, L.Name>, +body: Surf}

type Bind is Data:
  Bind{+name: L.Name, +val: Surf}

type Alt is Data:
  Alt{+p: Pat, +body: Surf}

type Surf is Data:
  SVar{+loc: L.Loc, +name: String}
  SApp{+loc: L.Loc, +f: Surf, +x: Surf}
  SLam{+loc: L.Loc, +v: L.Name, +body: Surf}
  SLamPat{+loc: L.Loc, +pats: List<&2, LPat>, +body: Surf}
  SZero{+loc: L.Loc}
  SPair{+loc: L.Loc, +a: Surf, +b: Surf}
  SCheck{+loc: L.Loc, +tc: Surf, +c: Surf}
  SIte{+loc: L.Loc, +i: Surf, +t: Surf, +e: Surf}
  SLeft{+loc: L.Loc, +x: Surf}
  SRight{+loc: L.Loc, +x: Surf}
  STrace{+loc: L.Loc, +x: Surf}
  SHash{+loc: L.Loc, +x: Surf}
  SChurch{+loc: L.Loc, +n: U32}
  SRec{+loc: L.Loc, +t: Surf, +r: Surf, +b: Surf}
  SLet{+loc: L.Loc, +binds: List<&2, Bind>, +body: Surf}
  SLetSugar{+loc: L.Loc, +defs: List<&2, Def>, +body: Surf}
  SList{+loc: L.Loc, +xs: List<&2, Surf>}
  SInt{+loc: L.Loc, +n: U32}
  SStr{+loc: L.Loc, +s: String}
  SCase{+loc: L.Loc, +scrut: Surf, +alts: List<&2, Alt>}
  SLamN{+loc: L.Loc, +n: Nat, +v: L.Name, +body: Surf}

# `import M` or `import qualified M as Q`.
type Import is Data:
  Import{+loc: L.Loc, +module: L.Name, +qual: Maybe<&2, L.Name>}

# A module as parsed, and as expanded.
type Item is Data:
  IImport{+imp: Import}
  IDef{+d: Def}

type EItem is Data:
  EImport{+imp: Import}
  EBind{+name: L.Name, +val: Surf}

# The annotation of a term.
def loc(t: Surf) -> L.Loc:
  match t:
    case SVar{loc, name}:
      loc
    case SApp{loc, f, x}:
      loc
    case SLam{loc, v, body}:
      loc
    case SLamPat{loc, pats, body}:
      loc
    case SZero{loc}:
      loc
    case SPair{loc, a, b}:
      loc
    case SCheck{loc, tc, c}:
      loc
    case SIte{loc, i, t, e}:
      loc
    case SLeft{loc, x}:
      loc
    case SRight{loc, x}:
      loc
    case STrace{loc, x}:
      loc
    case SHash{loc, x}:
      loc
    case SChurch{loc, n}:
      loc
    case SRec{loc, t, r, b}:
      loc
    case SLet{loc, binds, body}:
      loc
    case SLetSugar{loc, defs, body}:
      loc
    case SList{loc, xs}:
      loc
    case SInt{loc, n}:
      loc
    case SStr{loc, s}:
      loc
    case SCase{loc, scrut, alts}:
      loc
    case SLamN{loc, n, v, body}:
      loc
