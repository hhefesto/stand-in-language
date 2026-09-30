import Base
import ./Loc.bend as L

# The resolver's term types (haskell-final's Telomare.IR.Core): Term1 and
# Term2 share one type (names in Term1, de Bruijn indices in Term2), and
# Term3 is the closure-converted core that sizing takes.

# LamType: Open, Closed, or a let binding with c recursion placeholders
# (LetBinding c).
type LamKind is Data:
  Open{}
  Closed{}
  LetB{+c: Nat}

# Term1 / Term2 (ParserTermF over LocTag). TIdx appears in Term2 only.
type T is Data:
  TZero{+loc: L.Loc}
  TPair{+loc: L.Loc, +a: T, +b: T}
  TVar{+loc: L.Loc, +name: String}
  TIdx{+loc: L.Loc, +i: Nat}
  TApp{+loc: L.Loc, +f: T, +x: T}
  TLam{+loc: L.Loc, +k: LamKind, +name: String, +body: T}
  TCheck{+loc: L.Loc, +tc: T, +c: T}
  TIte{+loc: L.Loc, +i: T, +t: T, +e: T}
  TLeft{+loc: L.Loc, +x: T}
  TRight{+loc: L.Loc, +x: T}
  TTrace{+loc: L.Loc, +x: T}
  THash{+loc: L.Loc, +x: T}
  TChurch{+loc: L.Loc, +n: U32}
  TRec{+loc: L.Loc, +t: T, +r: T, +b: T}
  TRep{+loc: L.Loc}

# Term3 (Term3F over LocTag): zero, pairs, the environment, SetEnv, Defer
# with its function index, Gate, Left, Right, Abort, a recursion
# placeholder with its token, and a refinement check (its own Loc, the
# check, the value).
type C is Data:
  CZero{+loc: L.Loc}
  CPair{+loc: L.Loc, +a: C, +b: C}
  CEnv{+loc: L.Loc}
  CSetEnv{+loc: L.Loc, +x: C}
  CDefer{+loc: L.Loc, +fi: U32, +x: C}
  CGate{+loc: L.Loc}
  CLeft{+loc: L.Loc, +x: C}
  CRight{+loc: L.Loc, +x: C}
  CAbort{+loc: L.Loc}
  CUnsized{+loc: L.Loc, +tok: U32}
  CCheck{+loc: L.Loc, +cloc: L.Loc, +tc: C, +c: C}

def T.loc(t: T) -> L.Loc:
  match t:
    case TZero{loc}:
      loc
    case TPair{loc, a, b}:
      loc
    case TVar{loc, name}:
      loc
    case TIdx{loc, i}:
      loc
    case TApp{loc, f, x}:
      loc
    case TLam{loc, k, name, body}:
      loc
    case TCheck{loc, tc, c}:
      loc
    case TIte{loc, i, t, e}:
      loc
    case TLeft{loc, x}:
      loc
    case TRight{loc, x}:
      loc
    case TTrace{loc, x}:
      loc
    case THash{loc, x}:
      loc
    case TChurch{loc, n}:
      loc
    case TRec{loc, t, r, b}:
      loc
    case TRep{loc}:
      loc

def C.loc(t: C) -> L.Loc:
  match t:
    case CZero{loc}:
      loc
    case CPair{loc, a, b}:
      loc
    case CEnv{loc}:
      loc
    case CSetEnv{loc, x}:
      loc
    case CDefer{loc, fi, x}:
      loc
    case CGate{loc}:
      loc
    case CLeft{loc, x}:
      loc
    case CRight{loc, x}:
      loc
    case CAbort{loc}:
      loc
    case CUnsized{loc, tok}:
      loc
    case CCheck{loc, cloc, tc, c}:
      loc

# rewriteOuterTag
def C.retag(+l: L.Loc, t: C) -> C:
  match t:
    case CZero{loc}:
      CZero{l}
    case CPair{loc, a, b}:
      CPair{l, a, b}
    case CEnv{loc}:
      CEnv{l}
    case CSetEnv{loc, x}:
      CSetEnv{l, x}
    case CDefer{loc, fi, x}:
      CDefer{l, fi, x}
    case CGate{loc}:
      CGate{l}
    case CLeft{loc, x}:
      CLeft{l, x}
    case CRight{loc, x}:
      CRight{l, x}
    case CAbort{loc}:
      CAbort{l}
    case CUnsized{loc, tok}:
      CUnsized{l, tok}
    case CCheck{loc, cloc, tc, c}:
      CCheck{l, cloc, tc, c}

# i2t: n as nested pairs, every node at one Loc.
def ints.i2t(n: Nat, +loc: L.Loc) -> T:
  match n:
    case 0n:
      TZero{loc}
    case 1n+k:
      TPair{loc, ints.i2t(k, loc), TZero{loc}}

# s2t: a string as a list of its code points.
def ints.s2t(s: String, +loc: L.Loc) -> T:
  match s:
    case SNil{}:
      TZero{loc}
    case SCon{Chr{c}, rest}:
      TPair{loc, ints.i2t(U32.to_nat(c), loc), ints.s2t(rest, loc)}
