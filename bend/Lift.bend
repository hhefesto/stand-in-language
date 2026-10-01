import Base
import ./Show.bend as Sh
import ./Loc.bend as Lc
import ./Term.bend as T
import ./Core.bend as Co
import ./Sha256.bend as Sha

# Defer lifting (haskell-final's Resolve.deferLift, Term3Lifting,
# hashLiftedBody), what EAL and the IC share: every Defer body becomes a
# reference to its hash, the bodies go in a map keyed by that hash, and the
# hash is SHA-256 of the body's Haskell `show` text. EAL types code by
# these hashes; the IC finds the capture layout EAL published for a
# closure by its code's hash.

# Term3Lifting: Term3 with each Defer replaced by its body's hash.

type L is Data:
  LZero{+loc: Lc.Loc}
  LPair{+loc: Lc.Loc, +a: L, +b: L}
  LEnv{+loc: Lc.Loc}
  LSetEnv{+loc: Lc.Loc, +x: L}
  LGate{+loc: Lc.Loc}
  LLeft{+loc: Lc.Loc, +x: L}
  LRight{+loc: Lc.Loc, +x: L}
  LAbort{+loc: Lc.Loc}
  LUnsized{+loc: Lc.Loc, +tok: U32}
  LCheck{+loc: Lc.Loc, +cloc: Lc.Loc, +tc: L, +c: L}
  LRef{+loc: Lc.Loc, +h: String}

# A lifted body and the first index it was seen with.
type Body is Data:
  Body{+fi: U32, +body: L}

# CapShape: what EAL knows of the capture a code's closures carry.
type Shape is Data:
  CapData{}
  CapCode{}
  CapPair{+a: Shape, +b: Shape}
  CapOther{}

# The derived Show of a CapShape; `paren` when it is an argument.
def shape.show(s: Shape, +paren: Bool) -> String:
  match s:
    case CapData{}:
      "CapData"
    case CapCode{}:
      "CapCode"
    case CapOther{}:
      "CapOther"
    case CapPair{a, b}:
      Bool.pick(String, paren, "(", "") ++ "CapPair " ++ shape.show(a, True{}) ++ " " ++ shape.show(b, True{})
        ++ Bool.pick(String, paren, ")", "")

# The lifted program and its bodies (deferLift).
type Lifted is Data:
  Lifted{+bodies: Map<&2, Body>, +main: L}

# The text
# --------

# The bodies found so far, by hash, and the hashes already taken, by text:
# inlining repeats bodies, and a repeat costs a lookup, not a digest.

def pos.show(p: Lc.Pos) -> String:
  match p:
    case Lc.Pos{line, col, off}:
      "SourcePosition {sourcePositionLine = " ++ U32.show(line) ++ ", sourcePositionColumn = "
        ++ U32.show(col) ++ ", sourcePositionOffset = " ++ U32.show(off) ++ "}"

def file.show(+f: String, none: Bool) -> String:
  match none:
    case True{}:
      "Nothing"
    case False{}:
      "Just " ++ Sh.string(f)

# The derived Show of a LocTag; `paren` when it is an argument.
def loc.show(l: Lc.Loc, +paren: Bool) -> String:
  match l:
    case Lc.Src{+file, start, stop}:
      Bool.pick(String, paren, "(", "") ++ "SourceLoc (SourceSpan {sourceSpanFile = "
        ++ file.show(file, String.is_empty(file)) ++ ", sourceSpanStart = " ++ pos.show(start)
        ++ ", sourceSpanEnd = " ++ pos.show(stop) ++ "})" ++ Bool.pick(String, paren, ")", "")
    case Lc.GenIn{reason, parent}:
      Bool.pick(String, paren, "(", "") ++ "GeneratedLoc " ++ Sh.string(reason) ++ " (Just "
        ++ loc.show(parent, True{}) ++ ")" ++ Bool.pick(String, paren, ")", "")
    case Lc.Gen{reason}:
      Bool.pick(String, paren, "(", "") ++ "GeneratedLoc " ++ Sh.string(reason) ++ " Nothing"
        ++ Bool.pick(String, paren, ")", "")
    case Lc.Builtin{name}:
      Bool.pick(String, paren, "(", "") ++ "BuiltinLoc " ++ Sh.string(name) ++ Bool.pick(String, paren, ")", "")
    case Lc.RuntimeLoc{}:
      "RuntimeLoc"
    case Lc.DecompiledLoc{}:
      "DecompiledLoc"
    case Lc.Unknown{}:
      "UnknownLoc"

# `show (Fix Term3LiftingF)`, onto acc: data-fix's Show over Show1
# instances that quote their constructor text.
def show.go(l: L, acc: String) -> String:
  match l:
    case LZero{loc}:
      "Fix \"ZeroSF\"" ++ acc
    case LPair{loc, a, b}:
      "Fix \"PairSF (\"" ++ show.go(a, "\", \"" ++ show.go(b, "\")\"" ++ acc))
    case LEnv{loc}:
      "Fix \"EnvSF\"" ++ acc
    case LSetEnv{loc, x}:
      "Fix \"SetEnvSF (\"" ++ show.go(x, "\")\"" ++ acc)
    case LGate{loc}:
      "Fix \"GateSF\"" ++ acc
    case LLeft{loc, x}:
      "Fix \"LeftSF (\"" ++ show.go(x, "\")\"" ++ acc)
    case LRight{loc, x}:
      "Fix \"RightSF (\"" ++ show.go(x, "\")\"" ++ acc)
    case LAbort{loc}:
      "Fix \"AbortF\"" ++ acc
    case LUnsized{loc, tok}:
      "Fix \"Term3LUnsizedUnsizedRecursionToken {unUnsizedRecursionToken = " ++ U32.show(tok) ++ "}\"" ++ acc
    case LCheck{loc, cloc, tc, c}:
      "Fix \"Term3LCheckingWrapper(\"" ++ loc.show(cloc, False{}) ++ "\", \""
        ++ show.go(tc, "\", \"" ++ show.go(c, "\")\"" ++ acc))
    case LRef{loc, h}:
      "Fix \"Term3LDeferRef \"" ++ h ++ acc

def show(l: L) -> String:
  show.go(l, "")

# hashLiftedBody
def hash(l: L) -> String:
  Sha.string(show(l))

# Lifting
# -------

# The bodies found so far, by hash.
def D(-A: Data) -> Type:
  Map<&2, Body> -> A & Map<&2, Body>

def D.pure(-A: Data, x: A) -> D(A):
  m => (x, m)

def D.run(-A: Data, -B: Data, f: A -> D(B), r: A & Map<&2, Body>) -> B & Map<&2, Body>:
  (a, m) = r
  f(a)(m)

def D.bind(-A: Data, -B: Data, m: D(A), f: A -> D(B)) -> D(B):
  s => D.run(A, B, f, m(s))

# A body goes in under the first index it was seen with.
def keep(+h: String, +fi: U32, +body: L, r: Map<&2, Body> & Bool) -> Map<&2, Body>:
  (m, known) = r
  match known:
    case True{}:
      m
    case False{}:
      Map.set(&2, Body, m, h, Body{fi, body})

def add.go(+loc: Lc.Loc, +fi: U32, +body: L, +h: String, m: Map<&2, Body>) -> L & Map<&2, Body>:
  (LRef{loc, h}, keep(h, fi, body, Map.has(&2, Body, m, h)))

def add(+loc: Lc.Loc, +fi: U32, +body: L) -> D(L):
  m => add.go(loc, fi, body, hash(body), m)

# Children first, left to right, so the first index seen is the one the
# Haskell's left-biased union keeps.
def lift(t: T.C) -> D(L):
  match t:
    case T.CZero{loc}:
      D.pure(L, LZero{loc})
    case T.CPair{loc, a, b}:
      do D<L>:
        a2 : L <- lift(a)
        b2 : L <- lift(b)
        return LPair{loc, a2, b2}
    case T.CEnv{loc}:
      D.pure(L, LEnv{loc})
    case T.CSetEnv{loc, x}:
      do D<L>:
        x2 : L <- lift(x)
        return LSetEnv{loc, x2}
    case T.CDefer{loc, fi, x}:
      do D<L>:
        x2 : L <- lift(x)
        add(loc, fi, x2)
    case T.CGate{loc}:
      D.pure(L, LGate{loc})
    case T.CLeft{loc, x}:
      do D<L>:
        x2 : L <- lift(x)
        return LLeft{loc, x2}
    case T.CRight{loc, x}:
      do D<L>:
        x2 : L <- lift(x)
        return LRight{loc, x2}
    case T.CAbort{loc}:
      D.pure(L, LAbort{loc})
    case T.CUnsized{loc, tok}:
      D.pure(L, LUnsized{loc, tok})
    case T.CCheck{loc, cloc, tc, c}:
      do D<L>:
        tc2 : L <- lift(tc)
        c2 : L <- lift(c)
        return LCheck{loc, cloc, tc2, c2}

def lifted(r: L & Map<&2, Body>) -> Lifted:
  (l, m) = r
  Lifted{m, l}

def defer.lift(t: T.C) -> Lifted:
  lifted(lift(t)(Map.new(&2, Body)))

# compiled2Term3: a sized program as Term3, every node at one generated
# location. An aborted value (a result, never a program) reads as Abort.
def of.expr.at(v: Co.V, +loc: Lc.Loc) -> T.C:
  match v:
    case Co.VZero{}:
      T.CZero{loc}
    case Co.VPair{a, b}:
      T.CPair{loc, of.expr.at(a, loc), of.expr.at(b, loc)}
    case Co.VEnv{}:
      T.CEnv{loc}
    case Co.VSetEnv{a}:
      T.CSetEnv{loc, of.expr.at(a, loc)}
    case Co.VDefer{fi, a}:
      T.CDefer{loc, fi, of.expr.at(a, loc)}
    case Co.VGate{}:
      T.CGate{loc}
    case Co.VLeft{a}:
      T.CLeft{loc, of.expr.at(a, loc)}
    case Co.VRight{a}:
      T.CRight{loc, of.expr.at(a, loc)}
    case Co.VAbort{}:
      T.CAbort{loc}
    case Co.VAborted{m}:
      T.CAbort{loc}

def of.expr(v: Co.V) -> T.C:
  of.expr.at(v, Lc.Gen{"compiled2Term3"})
