import Base
import ./Loc.bend as L

# The surface syntax (haskell-final's Telomare.IR.Surface), a Loc on every
# node where Haskell has a Cofree. One term type serves every surface
# stage, indexed by what the stage still holds (DESIGN.md H1, as Haskell
# does it with Void): a constructor a stage has eliminated carries a
# witness of type Empty there, so it cannot be built or received.
#
#   P  expansion's sugar: pattern lambdas (SLamPat) and let definitions
#      (SLetSugar), parsed only; expansion turns them into single-binder
#      lambdas and plain lets.
#   C  `case` (SCase), until desugaring lowers it.
#   N  a placeholder lambda (SLamN), only while lowering: one of the n
#      lambdas around a let binding with n recursion sites, between
#      annotateUnsizedCount and letsToApps.
#
# The stages are the aliases below: Parsed, Expanded, Desugared, Lowering.

type Pat<-P: Data, -C: Data, -N: Data> is Data:
  PVar{+name: L.Name}
  PAnn{+p: Pat<P, C, N>, +t: Surf<P, C, N>}
  PInt{+n: U32}
  PStr{+s: String}
  PIgnore{}
  PPair{+a: Pat<P, C, N>, +b: Pat<P, C, N>}

type Bind<-P: Data, -C: Data, -N: Data> is Data:
  Bind{+name: L.Name, +val: Surf<P, C, N>}

type Alt<-P: Data, -C: Data, -N: Data> is Data:
  Alt{+p: Pat<P, C, N>, +body: Surf<P, C, N>}

# A lambda parameter and where it starts.
type LPat<-P: Data, -C: Data, -N: Data> is Data:
  LPat{+loc: L.Loc, +p: Pat<P, C, N>}

# A definition as written (parsed only): `name = body`, `name : check =
# body` (the check's Loc is the colon's), `[n1, n2, ...] = body` (Loc at
# the bracket).
type Def is Data:
  DSingle{+name: L.Name, +body: Surf<Unit, Unit, Empty>}
  DChecked{+name: L.Name, +cloc: L.Loc, +check: Surf<Unit, Unit, Empty>, +body: Surf<Unit, Unit, Empty>}
  DList{+loc: L.Loc, +names: List<&2, L.Name>, +body: Surf<Unit, Unit, Empty>}

type Surf<-P: Data, -C: Data, -N: Data> is Data:
  SVar{+loc: L.Loc, +name: String}
  SApp{+loc: L.Loc, +f: Surf<P, C, N>, +x: Surf<P, C, N>}
  SLam{+loc: L.Loc, +v: L.Name, +body: Surf<P, C, N>}
  SLamPat{+loc: L.Loc, +pats: List<&2, LPat<P, C, N>>, +body: Surf<P, C, N>, +sugar: P}
  SZero{+loc: L.Loc}
  SPair{+loc: L.Loc, +a: Surf<P, C, N>, +b: Surf<P, C, N>}
  SCheck{+loc: L.Loc, +tc: Surf<P, C, N>, +c: Surf<P, C, N>}
  SIte{+loc: L.Loc, +i: Surf<P, C, N>, +t: Surf<P, C, N>, +e: Surf<P, C, N>}
  SLeft{+loc: L.Loc, +x: Surf<P, C, N>}
  SRight{+loc: L.Loc, +x: Surf<P, C, N>}
  STrace{+loc: L.Loc, +x: Surf<P, C, N>}
  SHash{+loc: L.Loc, +x: Surf<P, C, N>}
  SChurch{+loc: L.Loc, +n: U32}
  SRec{+loc: L.Loc, +t: Surf<P, C, N>, +r: Surf<P, C, N>, +b: Surf<P, C, N>}
  SLet{+loc: L.Loc, +binds: List<&2, Bind<P, C, N>>, +body: Surf<P, C, N>}
  SLetSugar{+loc: L.Loc, +defs: List<&2, Def>, +body: Surf<P, C, N>, +sugar: P}
  SList{+loc: L.Loc, +xs: List<&2, Surf<P, C, N>>}
  SInt{+loc: L.Loc, +n: U32}
  SStr{+loc: L.Loc, +s: String}
  SCase{+loc: L.Loc, +scrut: Surf<P, C, N>, +alts: List<&2, Alt<P, C, N>>, +cased: C}
  SLamN{+loc: L.Loc, +n: Nat, +v: L.Name, +body: Surf<P, C, N>, +placeholder: N}

# The stages
# ----------

# What the parser builds.
def Parsed() -> Data:
  Surf<Unit, Unit, Empty>

# After expansion (and through resolution): no pattern lambdas, no let
# definitions.
def Expanded() -> Data:
  Surf<Empty, Unit, Empty>

# After desugaring: no case either. Lowering starts here.
def Desugared() -> Data:
  Surf<Empty, Empty, Empty>

# While lowering: placeholder lambdas around let bindings.
def Lowering() -> Data:
  Surf<Empty, Empty, Unit>

def ParsedPat() -> Data:
  Pat<Unit, Unit, Empty>

def ExpandedPat() -> Data:
  Pat<Empty, Unit, Empty>

def ExpandedBind() -> Data:
  Bind<Empty, Unit, Empty>

def ExpandedAlt() -> Data:
  Alt<Empty, Unit, Empty>

def ParsedLPat() -> Data:
  LPat<Unit, Unit, Empty>

def ExpandedLPat() -> Data:
  LPat<Empty, Unit, Empty>

def ParsedBind() -> Data:
  Bind<Unit, Unit, Empty>

def ParsedAlt() -> Data:
  Alt<Unit, Unit, Empty>

def DesugaredBind() -> Data:
  Bind<Empty, Empty, Empty>

def LoweringBind() -> Data:
  Bind<Empty, Empty, Unit>

# `import M` or `import qualified M as Q`.
type Import is Data:
  Import{+loc: L.Loc, +module: L.Name, +qual: Maybe<&2, L.Name>}

# A module as parsed, and as expanded.
type Item is Data:
  IImport{+imp: Import}
  IDef{+d: Def}

type EItem is Data:
  EImport{+imp: Import}
  EBind{+name: L.Name, +val: Surf<Empty, Unit, Empty>}

# The annotation of a term, at any stage.
def loc(-P: Data, -C: Data, -N: Data, t: Surf<P, C, N>) -> L.Loc:
  match t:
    case SVar{loc, name}:
      loc
    case SApp{loc, f, x}:
      loc
    case SLam{loc, v, body}:
      loc
    case SLamPat{loc, pats, body, w}:
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
    case SLetSugar{loc, defs, body, w}:
      loc
    case SList{loc, xs}:
      loc
    case SInt{loc, n}:
      loc
    case SStr{loc, s}:
      loc
    case SCase{loc, scrut, alts, w}:
      loc
    case SLamN{loc, n, v, body, w}:
      loc
