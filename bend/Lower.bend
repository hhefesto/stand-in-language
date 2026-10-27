import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Term.bend as T
import ./Resolve.bend as Rs
import ./Show.bend as Sh
import ./Sha256.bend as Sha

# From the desugared program to Term2 (Telomare.Resolve, process2Term2).
# One term serves EAL certification, sizing and running (main2Term3let):
# annotateUnsizedCount, then letsToApps (lets become lambda redexes, each
# recursion site a placeholder argument), which also checks the names: a
# name the program never defines, among the ones the program reaches, is
# reported at one of its uses. Then debruijinize and closeLams.

type Cyc is Data:
  CEnd{}
  CAt{+c: String, +seen: Bool}

type Ctx is Data:
  Ctx{+k: T.LamKind, +name: String}

type Hit is Data:
  Hit{+i: Nat, +k: T.LamKind}
  Miss{}

type AN is Data:
  AT{+t: S.Desugared()}
  ABs{+bs: List<&2, S.DesugaredBind()>}

type AV is Data:
  AVT{+t: S.Lowering()}
  AVBs{+bs: List<&2, S.LoweringBind()>}

# A name a term refers to without binding it, with where it is used: the
# first use in a left-to-right walk (Haskell's left-biased Map union).
def Refs() -> Data:
  Map<&2, L.Loc>

type LB is Data:
  LB{+name: String, +t: T.Term1(), +refs: Refs(), +c: Nat}

type LN is Data:
  LNT{+t: S.Lowering()}
  LNTs{+xs: List<&2, S.Lowering()>}
  LNBs{+bs: List<&2, S.LoweringBind()>}

type LV is Data:
  LVT{+t: T.Term1(), +refs: Refs()}
  LVTs{+ts: List<&2, T.Term1()>, +refs: Refs()}
  LVBs{+bs: List<&2, LB>}

type TSt is Data:
  TSt{+todo: List<&2, String>, +acc: Set()}

type ARS is Data:
  ARGo{+empty: Bool, +refs: Refs(), +t: T.Term1()}
  ARFound{+found: Bool, +a: L.Loc, +x: T.Term1(), +v: String, +refs: Refs()}

# A name the program uses and never defines, and where.
type KL is Data:
  KL{+k: String, +l: L.Loc}

def R(-A: Data) -> Data:
  Result<&2, &2, Rs.ResErr, A>

def fuel() -> Nat:
  U32.to_nat(4294967295)

def has(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

def minus(bs: List<&2, String>, a: Set()) -> Set():
  match bs:
    case Nil{}:
      a
    case Con{b, rest}:
      minus(rest, Set.del(a, b))

def generated.var() -> L.Loc:
  L.Gen{"LamBase Cofree instance"}

# What desugaring leaves no trace of (a case, a pattern lambda): never
# seen here.
def not.term() -> Rs.ResErr:
  Rs.MissingDefinitions{["(not a term)"]}

# Topological order (topologicalSort)
# -----------------------------------

def deps.of(+deps: Map<&2, Set()>, +n: String) -> Set():
  Pair.snd(Map<&2, Set()>, Set(), Map.get(Set(), Set.new(), deps, n))

def none.in(ds: List<&2, String>, +rem: List<&2, String>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, rest}:
      Bool.not(List.contains(~String, ~String.eq, rem, d)) && none.in(rest, rem)

def find.ready.if(ok: Bool, x: String, later: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{x}
    case False{}:
      later

def find.ready(xs: List<&2, String>, +deps: Map<&2, Set()>, +rem: List<&2, String>) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, rest}:
      find.ready.if(none.in(Set.to_list(deps.of(deps, x)), rem), x, find.ready(rest, deps, rem))

def delete.if(same: Bool, y: String, rest: List<&2, String>) -> List<&2, String>:
  match same:
    case True{}:
      rest
    case False{}:
      y <> rest

def delete(xs: List<&2, String>, +x: String) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+y, rest}:
      delete.if(String.eq(x, y), y, delete(rest, x))

def first.in(ds: List<&2, String>, +rem: List<&2, String>) -> Maybe<&2, String>:
  match ds:
    case Nil{}:
      None{}
    case Con{+d, rest}:
      find.ready.if(List.contains(~String, ~String.eq, rem, d), d, first.in(rest, rem))

def cyc.next(m: Maybe<&2, String>, +visited: Set()) -> Cyc:
  match m:
    case None{}:
      CEnd{}
    case Some{+n}:
      CAt{n, has(visited, n)}

# The cycle through the first name left (findCycleFrom).
def cycle(fuel: Nat, +deps: Map<&2, Set()>, +rem: List<&2, String>, +visited: Set(), cur: Cyc) ->
  List<&2, String>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match cur:
        case CEnd{}:
          []
        case CAt{+c, seen}:
          match seen:
            case True{}:
              [c]
            case False{}:
              +v2 = Set.add(visited, c)
              c <> cycle(f, deps, rem, v2, cyc.next(first.in(Set.to_list(deps.of(deps, c)), rem), v2))

def head.or(xs: List<&2, String>) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, rest}:
      Some{x}

def topo(fuel: Nat, +deps: Map<&2, Set()>, +rem: List<&2, String>, acc: List<&2, String>,
         next: Maybe<&2, String>) -> R(List<&2, String>):
  match fuel:
    case 0n:
      Done{List.reverse(&2, String, acc)}
    case 1n+f:
      match rem:
        case Nil{}:
          Done{List.reverse(&2, String, acc)}
        case Con{r0, rrest}:
          match next:
            case None{}:
              Fail{Rs.DefinitionCycle{cycle(fuel(), deps, rem, Set.new(), cyc.next(head.or(rem), Set.new()))}}
            case Some{+n}:
              +rem2 = delete(rem, n)
              topo(f, deps, rem2, n <> acc, find.ready(rem2, deps, rem2))

def topological.sort(+names: List<&2, String>, +deps: Map<&2, Set()>) -> R(List<&2, String>):
  topo(fuel(), deps, names, [], find.ready(names, deps, names))

def pairs(+loc: L.Loc, xs: List<&2, T.Term1()>) -> T.Term1():
  match xs:
    case Nil{}:
      T.TZero{loc}
    case Con{x, rest}:
      T.TPair{loc, x, pairs(loc, rest)}

# de Bruijn indices (debruijinizeApp)
# -------------------------------------------------

def lookup.pick(yes: Bool, h: Hit, later: Hit) -> Hit:
  match yes:
    case True{}:
      h
    case False{}:
      later

def lookup.at(ctx: List<&2, Ctx>, +n: String, +i: Nat) -> Hit:
  match ctx:
    case Nil{}:
      Miss{}
    case Con{c, rest}:
      match c:
        case Ctx{k, name}:
          lookup.pick(String.eq(name, n), Hit{i, k}, lookup.at(rest, n, 1n+i))

def conv.kind(k: T.LamKind) -> T.LamKind:
  match k:
    case T.LetB{c}:
      T.Open{}
    case other:
      other

def repeaters(c: Nat, +anno: L.Loc, ix: T.Term2()) -> T.Term2():
  match c:
    case 0n:
      ix
    case 1n+k:
      repeaters(k, anno, T.TApp{generated.var(), ix, T.TRep{anno}})

# A variable's index; a let-bound one also takes its binding's
# placeholders, fresh at each use (debruijinizeApp).
def index.of(+anno: L.Loc, +n: String, h: Hit) -> R(T.Term2()):
  match h:
    case Miss{}:
      Fail{Rs.MissingDefinitions{["undefined identifier " ++ n]}}
    case Hit{i, k}:
      match k:
        case T.LetB{c}:
          Done{repeaters(c, anno, T.TVar{generated.var(), i})}
        case _:
          Done{T.TVar{generated.var(), i}}

def debruijn(+fuel: Nat, +ctx: List<&2, Ctx>, t: T.Term1()) -> R(T.Term2()):
  match fuel:
    case 0n:
      Fail{Rs.MissingDefinitions{["(nesting too deep)"]}}
    case 1n+f:
      match t:
        case T.TLam{a, +k, +name, body}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            b2 : T.T<Nat> <- debruijn(f, Ctx{k, name} <> ctx, body)
            return T.TLam{a, conv.kind(k), name, b2}
        case T.TVar{+a, +name}:
          index.of(a, name, lookup.at(ctx, name, 0n))
        case T.TApp{a, x, y}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            y2 : T.T<Nat> <- debruijn(f, ctx, y)
            return T.TApp{a, x2, y2}
        case T.TPair{a, x, y}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            y2 : T.T<Nat> <- debruijn(f, ctx, y)
            return T.TPair{a, x2, y2}
        case T.TCheck{a, k, x, y}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            y2 : T.T<Nat> <- debruijn(f, ctx, y)
            return T.TCheck{a, k, x2, y2}
        case T.TIte{a, x, y, z}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            y2 : T.T<Nat> <- debruijn(f, ctx, y)
            z2 : T.T<Nat> <- debruijn(f, ctx, z)
            return T.TIte{a, x2, y2, z2}
        case T.TRec{a, x, y, z}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            y2 : T.T<Nat> <- debruijn(f, ctx, y)
            z2 : T.T<Nat> <- debruijn(f, ctx, z)
            return T.TRec{a, x2, y2, z2}
        case T.TLeft{a, x}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            return T.TLeft{a, x2}
        case T.TRight{a, x}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            return T.TRight{a, x2}
        case T.THash{a, x}:
          do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
            x2 : T.T<Nat> <- debruijn(f, ctx, x)
            return T.THash{a, x2}
        case T.TZero{a}:
          Done{T.TZero{a}}
        case T.TChurch{a, n}:
          Done{T.TChurch{a, n}}
        case T.TRep{a}:
          Done{T.TRep{a}}

def close.lam(naked: Bool, k: T.LamKind, name: String, +body: T.Term2()) -> T.Term2():
  match naked:
    case True{}:
      T.TLam{T.T.loc(Nat, body), T.Closed{}, name, body}
    case False{}:
      T.TLam{T.T.loc(Nat, body), k, name, body}

# A lambda outside every lambda is closed; every lambda takes its body's
# annotation (closeLams).
def close.lams(+fuel: Nat, +naked: Bool, t: T.Term2()) -> T.Term2():
  match fuel:
    case 0n:
      t
    case 1n+f:
      match t:
        case T.TLam{a, k, name, body}:
          close.lam(naked, k, name, close.lams(f, False{}, body))
        case T.TApp{a, x, y}:
          T.TApp{a, close.lams(f, naked, x), close.lams(f, naked, y)}
        case T.TPair{a, x, y}:
          T.TPair{a, close.lams(f, naked, x), close.lams(f, naked, y)}
        case T.TCheck{a, k, x, y}:
          T.TCheck{a, k, close.lams(f, naked, x), close.lams(f, naked, y)}
        case T.TIte{a, x, y, z}:
          T.TIte{a, close.lams(f, naked, x), close.lams(f, naked, y), close.lams(f, naked, z)}
        case T.TRec{a, x, y, z}:
          T.TRec{a, close.lams(f, naked, x), close.lams(f, naked, y), close.lams(f, naked, z)}
        case T.TLeft{a, x}:
          T.TLeft{a, close.lams(f, naked, x)}
        case T.TRight{a, x}:
          T.TRight{a, close.lams(f, naked, x)}
        case T.THash{a, x}:
          T.THash{a, close.lams(f, naked, x)}
        case other:
          other

# Hashes (generateAllHashes)
# --------------------------

def kind.show(k: T.LamKind) -> String:
  match k:
    case T.Open{}:
      "Open ()"
    case T.Closed{}:
      "Closed ()"
    case T.LetB{c}:
      "LetBinding " ++ U32.show(U32.from_nat(c)) ++ " ()"

def lp(paren: Bool) -> String:
  Bool.pick(String, paren, "(", "")

def rp(paren: Bool, acc: String) -> String:
  match paren:
    case True{}:
      ")" ++ acc
    case False{}:
      acc

# `show (forget term2)` onto acc: data-fix's Show (`Fix `, parenthesized as
# an argument) over ParserTermF's Show1 instances, whose basic
# constructors quote their text.
def show(t: T.Term2(), +paren: Bool, acc: String) -> String:
  match t:
    case T.TZero{a}:
      lp(paren) ++ "Fix \"ZeroSF\"" ++ rp(paren, acc)
    case T.TPair{a, x, y}:
      lp(paren) ++ "Fix \"PairSF (\"" ++ show(x, False{}, "\", \"" ++ show(y, False{}, "\")\"" ++ rp(paren, acc)))
    case T.TVar{a, i}:
      lp(paren) ++ "Fix VarUPF " ++ U32.show(U32.from_nat(i)) ++ rp(paren, acc)
    case T.TApp{a, f, x}:
      lp(paren) ++ "Fix AppUPF " ++ show(f, True{}, " " ++ show(x, True{}, rp(paren, acc)))
    case T.TLam{a, k, name, body}:
      lp(paren) ++ "Fix LamUPF " ++ kind.show(k) ++ " " ++ show(body, True{}, rp(paren, acc))
    case T.TCheck{a, k, x, y}:
      lp(paren) ++ "Fix CheckUPF " ++ L.kind.show(k) ++ " " ++ show(x, True{}, " " ++ show(y, True{}, rp(paren, acc)))
    case T.TIte{a, x, y, z}:
      lp(paren) ++ "Fix ITEUPF " ++ show(x, True{}, " " ++ show(y, True{}, " " ++ show(z, True{}, rp(paren, acc))))
    case T.TLeft{a, x}:
      lp(paren) ++ "Fix LeftUPF " ++ show(x, True{}, rp(paren, acc))
    case T.TRight{a, x}:
      lp(paren) ++ "Fix RightUPF " ++ show(x, True{}, rp(paren, acc))
    case T.THash{a, x}:
      lp(paren) ++ "Fix HashUPF " ++ show(x, True{}, rp(paren, acc))
    case T.TChurch{a, n}:
      lp(paren) ++ "Fix ChurchUPF " ++ U32.show(n) ++ rp(paren, acc)
    case T.TRec{a, x, y, z}:
      lp(paren) ++ "Fix UnsizedRecursionUPF " ++ show(x, True{}, " " ++ show(y, True{}, " " ++ show(z, True{}, rp(paren, acc))))
    case T.TRep{a}:
      lp(paren) ++ "Fix TUnsizedRepeaterF" ++ rp(paren, acc)

# ints2t
def ints(bs: List<&2, U32>, +loc: L.Loc) -> T.Term2():
  match bs:
    case Nil{}:
      T.TZero{loc}
    case Con{b, rest}:
      T.TPair{loc, T.ints.i2t(Nat, U32.to_nat(b), loc), ints(rest, loc)}

# generateAllHashes: every `#` (HashF), innermost first, becomes a number
# for its term: the last 8 bytes of the SHA-256 of the term's `show`, as a
# list, at the whole term's location.
def hashes(t: T.Term2(), +loc: L.Loc) -> T.Term2():
  match t:
    case T.THash{a, x}:
      ints(List.drop(&2, U32, Sha.raw(show(hashes(x, loc), False{}, "")), 24n), loc)
    case T.TPair{a, x, y}:
      T.TPair{a, hashes(x, loc), hashes(y, loc)}
    case T.TApp{a, f, x}:
      T.TApp{a, hashes(f, loc), hashes(x, loc)}
    case T.TLam{a, k, name, body}:
      T.TLam{a, k, name, hashes(body, loc)}
    case T.TCheck{a, k, x, y}:
      T.TCheck{a, k, hashes(x, loc), hashes(y, loc)}
    case T.TIte{a, x, y, z}:
      T.TIte{a, hashes(x, loc), hashes(y, loc), hashes(z, loc)}
    case T.TLeft{a, x}:
      T.TLeft{a, hashes(x, loc)}
    case T.TRight{a, x}:
      T.TRight{a, hashes(x, loc)}
    case T.TRec{a, x, y, z}:
      T.TRec{a, hashes(x, loc), hashes(y, loc), hashes(z, loc)}
    case other:
      other

def hashed(+t: T.Term2()) -> T.Term2():
  hashes(t, T.T.loc(Nat, t))

# annotateUnsizedCount (the let path)
# -----------------------------------

# A counter threaded through a walk, as Haskell's StateT Integer.
def St(-A: Data) -> Type:
  Nat -> A & Nat

def St.pure(-A: Data, x: A) -> St(A):
  n => (x, n)

def St.run(-A: Data, -B: Data, f: A -> St(B), r: A & Nat) -> B & Nat:
  (a, s) = r
  f(a)(s)

def St.bind(-A: Data, -B: Data, m: St(A), f: A -> St(B)) -> St(B):
  n => St.run(A, B, f, m(n))

def tick() -> St(Nat):
  +n => (n, 1n+n)

def avt(v: AV) -> S.Lowering():
  match v:
    case AVT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def avbs(v: AV) -> List<&2, S.LoweringBind()>:
  match v:
    case AVBs{bs}:
      bs
    case _:
      []

def site.name(n: Nat) -> String:
  ":" ++ Nat.show(n)

# \:0 -> \:1 -> ... x, one placeholder lambda per recursion site the
# binding's value holds, each knowing how many there are (cap).
def cap.lams(+i: Nat, +k: Nat, +anno: L.Loc, x: S.Lowering()) -> S.Lowering():
  match i:
    case 0n:
      x
    case 1n+j:
      cap.lams(j, k, anno, S.SLamN{anno, k, L.Name{anno, site.name(j)}, x, Unit{}})

def cap.with(+k: Nat, +x: S.Lowering()) -> S.Lowering():
  cap.lams(k, k, S.loc(Empty, Empty, Unit, x), x)

def cap.bind(name: L.Name, r: AV & Nat) -> S.LoweringBind():
  (v, +k) = r
  S.Bind{name, cap.with(k, avt(v))}

# (\:0 -> (\:1 -> x) :1) :0 for the sites outside every binding (capTop).
def top.apps(+i: Nat, +anno: L.Loc, x: S.Lowering()) -> S.Lowering():
  match i:
    case 0n:
      x
    case 1n+j:
      top.apps(j, anno, S.SApp{anno, S.SLam{anno, L.Name{anno, site.name(j)}, x}, S.SVar{anno, site.name(j)}})

def cap.top.with(k: Nat, +x: S.Lowering()) -> S.Lowering():
  top.apps(k, S.loc(Empty, Empty, Unit, x), x)

def cap.top(r: AV & Nat) -> S.Lowering():
  (v, k) = r
  cap.top.with(k, avt(v))

def list.items(t: S.Lowering()) -> List<&2, S.Lowering()>:
  match t:
    case S.SList{loc, xs}:
      xs
    case _:
      []

# letsToApps
# ----------

# Number the recursion sites, post-order, each let binding's value from 0
# on its own; each site becomes `{t, r, b} :n` (annotateUnsizedCount).
def annotate(+fuel: Nat, n: AN) -> St(AV):
  match fuel:
    case 0n:
      St.pure(AV, AVT{S.SZero{L.Unknown{}}})
    case 1n+f:
      match n:
        case ABs{bs}:
          match bs:
            case Nil{}:
              St.pure(AV, AVBs{[]})
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  do St<AV>:
                    r : AV <- annotate(f, ABs{rest})
                    return AVBs{cap.bind(name, annotate(f, AT{val})(0n)) <> avbs(r)}
        case AT{t}:
          match t:
            case S.SRec{+loc, a, b, c}:
              do St<AV>:
                a2 : AV <- annotate(f, AT{a})
                b2 : AV <- annotate(f, AT{b})
                c2 : AV <- annotate(f, AT{c})
                k : Nat <- tick()
                return AVT{S.SApp{loc, S.SRec{loc, avt(a2), avt(b2), avt(c2)}, S.SVar{loc, site.name(k)}}}
            case S.SLet{loc, binds, inner}:
              do St<AV>:
                b2 : AV <- annotate(f, ABs{binds})
                i2 : AV <- annotate(f, AT{inner})
                return AVT{S.SLet{loc, avbs(b2), avt(i2)}}
            case S.SApp{loc, a, b}:
              do St<AV>:
                a2 : AV <- annotate(f, AT{a})
                b2 : AV <- annotate(f, AT{b})
                return AVT{S.SApp{loc, avt(a2), avt(b2)}}
            case S.SLam{loc, v, body}:
              do St<AV>:
                b2 : AV <- annotate(f, AT{body})
                return AVT{S.SLam{loc, v, avt(b2)}}
            case S.SPair{loc, a, b}:
              do St<AV>:
                a2 : AV <- annotate(f, AT{a})
                b2 : AV <- annotate(f, AT{b})
                return AVT{S.SPair{loc, avt(a2), avt(b2)}}
            case S.SCheck{loc, k, a, b}:
              do St<AV>:
                a2 : AV <- annotate(f, AT{a})
                b2 : AV <- annotate(f, AT{b})
                return AVT{S.SCheck{loc, k, avt(a2), avt(b2)}}
            case S.SIte{loc, a, b, c}:
              do St<AV>:
                a2 : AV <- annotate(f, AT{a})
                b2 : AV <- annotate(f, AT{b})
                c2 : AV <- annotate(f, AT{c})
                return AVT{S.SIte{loc, avt(a2), avt(b2), avt(c2)}}
            case S.SLeft{loc, x}:
              do St<AV>:
                x2 : AV <- annotate(f, AT{x})
                return AVT{S.SLeft{loc, avt(x2)}}
            case S.SRight{loc, x}:
              do St<AV>:
                x2 : AV <- annotate(f, AT{x})
                return AVT{S.SRight{loc, avt(x2)}}
            case S.SHash{loc, x}:
              do St<AV>:
                x2 : AV <- annotate(f, AT{x})
                return AVT{S.SHash{loc, avt(x2)}}
            case S.SList{loc, xs}:
              match xs:
                case Nil{}:
                  St.pure(AV, AVT{S.SList{loc, []}})
                case Con{x, rest}:
                  do St<AV>:
                    x2 : AV <- annotate(f, AT{x})
                    r2 : AV <- annotate(f, AT{S.SList{loc, rest}})
                    return AVT{S.SList{loc, avt(x2) <> list.items(avt(r2))}}
            case S.SVar{loc, name}:
              St.pure(AV, AVT{S.SVar{loc, name}})
            case S.SZero{loc}:
              St.pure(AV, AVT{S.SZero{loc}})
            case S.SChurch{loc, k}:
              St.pure(AV, AVT{S.SChurch{loc, k}})
            case S.SInt{loc, k}:
              St.pure(AV, AVT{S.SInt{loc, k}})
            case S.SStr{loc, str}:
              St.pure(AV, AVT{S.SStr{loc, str}})
            case S.SLamPat{loc, ps, body, w}:
              Empty.absurd(St(AV), w)
            case S.SLetSugar{loc, ds, body, w}:
              Empty.absurd(St(AV), w)
            case S.SCase{loc, x, alts, w}:
              Empty.absurd(St(AV), w)
            case S.SLamN{loc, k, v, body, w}:
              Empty.absurd(St(AV), w)

def lv.t(v: LV) -> T.Term1():
  match v:
    case LVT{t, refs}:
      t
    case _:
      T.TZero{L.Unknown{}}

def lv.refs(v: LV) -> Refs():
  match v:
    case LVT{t, refs}:
      refs
    case LVTs{ts, refs}:
      refs
    case _:
      Map.new(&2, L.Loc)

# The union of two reference maps, a's use of a name kept over b's.
def refs.union(a: Refs(), b: Refs()) -> Refs():
  Map.union(&2, L.Loc, b, a)

def refs.one(+name: String, +loc: L.Loc) -> Refs():
  Map.set(&2, L.Loc, Map.new(&2, L.Loc), name, loc)

def refs.keys(r: Refs()) -> Set():
  Set.from_list(Map.keys(&2, L.Loc, r))

def refs.size(r: Refs()) -> Nat:
  Map.size(&2, L.Loc, r)

def refs.has(r: Refs(), +n: String) -> Bool:
  Pair.snd(Refs(), Bool, Map.has(&2, L.Loc, r, n))

def restrict.if(keep: Bool, +k: String, +l: L.Loc, acc: Refs()) -> Refs():
  match keep:
    case True{}:
      Map.set(&2, L.Loc, acc, k, l)
    case False{}:
      acc

# The entries whose names are in keep (restrictKeys).
def restrict(kvs: List<&2, Sigma<&2, &2, String, _ => L.Loc>>, +keep: Set(), acc: Refs()) -> Refs():
  match kvs:
    case Nil{}:
      acc
    case Con{kv, rest}:
      match kv:
        case (+k, +l):
          restrict(rest, keep, restrict.if(has(keep, k), k, l, acc))

def lv.ts(v: LV) -> List<&2, T.Term1()>:
  match v:
    case LVTs{ts, refs}:
      ts
    case _:
      []

def lv.bs(v: LV) -> List<&2, LB>:
  match v:
    case LVBs{bs}:
      bs
    case _:
      []

# The placeholder count of a binding's value: its outer lambda's, if the
# value is wrapped in placeholder lambdas.
def count.of(t: S.Lowering()) -> Nat:
  match t:
    case S.SLamN{loc, k, v, body, w}:
      k
    case _:
      0n

def lam.kind(n: Nat) -> T.LamKind:
  match n:
    case 0n:
      T.Closed{}
    case _:
      T.Open{}

def lb.names(bs: List<&2, LB>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case LB{name, t, refs, c}:
          name <> lb.names(rest)

def lb.deps(bs: List<&2, LB>, acc: Map<&2, Set()>) -> Map<&2, Set()>:
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case LB{name, t, refs, c}:
          lb.deps(rest, Map.set(&2, Set(), acc, name, refs.keys(refs)))

def lb.refs.if(yes: Bool, refs: Refs(), acc: Refs()) -> Refs():
  match yes:
    case True{}:
      refs.union(acc, refs)
    case False{}:
      acc

# What the live bindings refer to, in their written order, after acc.
def lb.refs(bs: List<&2, LB>, +live: Set(), acc: Refs()) -> Refs():
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case LB{+name, t, refs, c}:
          lb.refs(rest, live, lb.refs.if(has(live, name), refs, acc))

def lb.with.name.if(yes: Bool, b: LB, rest: List<&2, LB>) -> List<&2, LB>:
  match yes:
    case True{}:
      b <> rest
    case False{}:
      rest

def lb.with.name(bs: List<&2, LB>, +n: String) -> List<&2, LB>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case LB{+name, t, refs, c}:
          lb.with.name.if(String.eq(name, n), LB{name, t, refs, c}, lb.with.name(rest, n))

def lb.in.order(sorted: List<&2, String>, +bs: List<&2, LB>) -> List<&2, LB>:
  match sorted:
    case Nil{}:
      []
    case Con{n, rest}:
      List.append(&2, LB, lb.with.name(bs, n), lb.in.order(rest, bs))

def lb.live(bs: List<&2, LB>, +live: Set()) -> List<&2, LB>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case LB{+name, t, refs, c}:
          lb.with.name.if(has(live, name), LB{name, t, refs, c}, lb.live(rest, live))

def trans.step(seen: Bool, +n: String, rest: List<&2, String>, +acc: Set(), +deps: Map<&2, Set()>) -> TSt:
  match seen:
    case True{}:
      TSt{rest, acc}
    case False{}:
      TSt{List.append(&2, String, Set.to_list(deps.of(deps, n)), rest), Set.add(acc, n)}

# Every name reachable from the refs through the bindings (getTransitive').
def transitive(fuel: Nat, +deps: Map<&2, Set()>, st: TSt) -> Set():
  match fuel:
    case 0n:
      match st:
        case TSt{todo, acc}:
          acc
    case 1n+f:
      match st:
        case TSt{todo, +acc}:
          match todo:
            case Nil{}:
              acc
            case Con{+n, rest}:
              transitive(f, deps, trans.step(has(acc, n), n, rest, acc, deps))

def make.binding(name: String, d: T.Term1(), c: Nat, +body: T.Term1()) -> T.Term1():
  T.TApp{T.T.loc(String, body), T.TLam{T.T.loc(String, body), T.LetB{c}, name, body}, d}

# (\n -> body) value, the lambda a let binding with c placeholders
# (makeBinding).
def bindings.wrap(bs: List<&2, LB>, body: T.Term1()) -> T.Term1():
  match bs:
    case Nil{}:
      body
    case Con{b, rest}:
      match b:
        case LB{name, t, refs, c}:
          make.binding(name, t, c, bindings.wrap(rest, body))

# A let becomes lambda redexes in dependency order, dropping the bindings
# its body cannot reach; what it still needs from outside is its refs: the
# body's, then the live bindings', as written.
def let.build(+inner: LV, +bs: List<&2, LB>, sorted: List<&2, String>) -> LV:
  +deps = lb.deps(bs, Map.new(&2, Set()))
  +trans = transitive(fuel(), deps, TSt{Map.keys(&2, L.Loc, lv.refs(inner)), Set.new()})
  +live = lb.live(lb.in.order(sorted, bs), trans)
  +bound = Set.from_list(lb.names(live))
  +used = lb.refs(bs, bound, lv.refs(inner))
  LVT{bindings.wrap(List.reverse(&2, LB, live), lv.t(inner)),
      restrict(Map.to_list(&2, L.Loc, used), minus(lb.names(live), trans), Map.new(&2, L.Loc))}

def lb.cons(name: String, +v: LV, c: Nat, r: LV) -> LV:
  LVBs{LB{name, lv.t(v), lv.refs(v), c} <> lv.bs(r)}

def left.mk(a: L.Loc, x: T.Term1()) -> T.Term1():
  T.TLeft{a, x}

def right.mk(a: L.Loc, x: T.Term1()) -> T.Term1():
  T.TRight{a, x}

def hash.mk(a: L.Loc, x: T.Term1()) -> T.Term1():
  T.THash{a, x}

def one(~k: L.Loc -> T.Term1() -> T.Term1(), +x: LV, a: L.Loc) -> LV:
  LVT{k(a, lv.t(x)), lv.refs(x)}

def list.lv(+a: L.Loc, +x: LV) -> LV:
  LVT{pairs(a, lv.ts(x)), lv.refs(x)}

def lts.cons(+x: LV, +r: LV) -> LV:
  LVTs{lv.t(x) <> lv.ts(r), refs.union(lv.refs(x), lv.refs(r))}

def app.mk(a: L.Loc, x: T.Term1(), y: T.Term1()) -> T.Term1():
  T.TApp{a, x, y}

def pair.mk(a: L.Loc, x: T.Term1(), y: T.Term1()) -> T.Term1():
  T.TPair{a, x, y}

def ite.mk(a: L.Loc, x: T.Term1(), y: T.Term1(), z: T.Term1()) -> T.Term1():
  T.TIte{a, x, y, z}

def rec.mk(a: L.Loc, x: T.Term1(), y: T.Term1(), z: T.Term1()) -> T.Term1():
  T.TRec{a, x, y, z}

def two(~k: L.Loc -> T.Term1() -> T.Term1() -> T.Term1(), +x: LV, +y: LV, a: L.Loc) -> LV:
  LVT{k(a, lv.t(x), lv.t(y)), refs.union(lv.refs(x), lv.refs(y))}

def check.two(+a: L.Loc, +k: L.AbortKind, +x: LV, +y: LV) -> LV:
  LVT{T.TCheck{a, k, lv.t(x), lv.t(y)}, refs.union(lv.refs(x), lv.refs(y))}

def three(~k: L.Loc -> T.Term1() -> T.Term1() -> T.Term1() -> T.Term1(), +x: LV, +y: LV, +z: LV, a: L.Loc) -> LV:
  LVT{k(a, lv.t(x), lv.t(y), lv.t(z)), refs.union(lv.refs(x), refs.union(lv.refs(y), lv.refs(z)))}

def lam.kind.of(+refs: Refs(), placeholder: Bool) -> T.LamKind:
  match placeholder:
    case True{}:
      T.Open{}
    case False{}:
      lam.kind(refs.size(refs))

# A lambda is closed when nothing inside refers outside it and it is no
# placeholder lambda.
def lam.done(a: L.Loc, +name: String, +b: LV, placeholder: Bool) -> LV:
  +refs = Map.del(&2, L.Loc, lv.refs(b), name)
  LVT{T.TLam{a, lam.kind.of(refs, placeholder), name, lv.t(b)}, refs}

def let.after.sorted(inner: LV, +bs: List<&2, LB>, r: R(List<&2, String>)) -> R(LV):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{sorted}:
      Done{let.build(inner, bs, List.reverse(&2, String, sorted))}

def let.after(inner: LV, +bs: List<&2, LB>) -> R(LV):
  let.after.sorted(inner, bs, topological.sort(lb.names(bs), lb.deps(bs, Map.new(&2, Set()))))

def lta(+fuel: Nat, n: LN) -> R(LV):
  match fuel:
    case 0n:
      Fail{Rs.MissingDefinitions{["(nesting too deep)"]}}
    case 1n+f:
      match n:
        case LNBs{bs}:
          match bs:
            case Nil{}:
              Done{LVBs{[]}}
            case Con{b, rest}:
              match b:
                case S.Bind{name, +val}:
                  do Result<&2, &2, Rs.ResErr, LV>:
                    v2 : LV <- lta(f, LNT{val})
                    r2 : LV <- lta(f, LNBs{rest})
                    return lb.cons(L.Name.text(name), v2, count.of(val), r2)
        case LNTs{xs}:
          match xs:
            case Nil{}:
              Done{LVTs{[], Map.new(&2, L.Loc)}}
            case Con{x, rest}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                r2 : LV <- lta(f, LNTs{rest})
                return lts.cons(x2, r2)
        case LNT{t}:
          match t:
            case S.SVar{+a, +name}:
              Done{LVT{T.TVar{a, name}, refs.one(name, a)}}
            case S.SLam{a, v, body}:
              do Result<&2, &2, Rs.ResErr, LV>:
                b2 : LV <- lta(f, LNT{body})
                return lam.done(a, L.Name.text(v), b2, False{})
            case S.SLamN{a, k, v, body, w}:
              do Result<&2, &2, Rs.ResErr, LV>:
                b2 : LV <- lta(f, LNT{body})
                return lam.done(a, L.Name.text(v), b2, True{})
            case S.SLet{a, binds, inner}:
              do Result<&2, &2, Rs.ResErr, LV>:
                i2 : LV <- lta(f, LNT{inner})
                b2 : LV <- lta(f, LNBs{binds})
                let.after(i2, lv.bs(b2))
            case S.SApp{a, x, y}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                y2 : LV <- lta(f, LNT{y})
                return two(~app.mk, x2, y2, a)
            case S.SPair{a, x, y}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                y2 : LV <- lta(f, LNT{y})
                return two(~pair.mk, x2, y2, a)
            case S.SCheck{a, k, x, y}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                y2 : LV <- lta(f, LNT{y})
                return check.two(a, k, x2, y2)
            case S.SIte{a, x, y, z}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                y2 : LV <- lta(f, LNT{y})
                z2 : LV <- lta(f, LNT{z})
                return three(~ite.mk, x2, y2, z2, a)
            case S.SRec{a, x, y, z}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                y2 : LV <- lta(f, LNT{y})
                z2 : LV <- lta(f, LNT{z})
                return three(~rec.mk, x2, y2, z2, a)
            case S.SLeft{a, x}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                return one(~left.mk, x2, a)
            case S.SRight{a, x}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                return one(~right.mk, x2, a)
            case S.SHash{a, x}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                return one(~hash.mk, x2, a)
            case S.SList{+a, xs}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNTs{xs})
                return list.lv(a, x2)
            case S.SInt{a, k}:
              Done{LVT{T.ints.i2t(String, U32.to_nat(k), a), Map.new(&2, L.Loc)}}
            case S.SStr{a, s}:
              Done{LVT{T.ints.s2t(String, s, a), Map.new(&2, L.Loc)}}
            case S.SZero{a}:
              Done{LVT{T.TZero{a}, Map.new(&2, L.Loc)}}
            case S.SChurch{a, k}:
              Done{LVT{T.TChurch{a, k}, Map.new(&2, L.Loc)}}
            case _:
              Fail{not.term()}

def is.placeholder(k: String) -> Bool:
  match k:
    case SCon{Chr{58}, t}:
      True{}
    case _:
      False{}

def kls.if(yes: Bool, +k: String, +l: L.Loc, rest: List<&2, KL>) -> List<&2, KL>:
  match yes:
    case True{}:
      rest
    case False{}:
      KL{k, l} <> rest

# The references that are no placeholder.
def kls(kvs: List<&2, Sigma<&2, &2, String, _ => L.Loc>>) -> List<&2, KL>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (+k, +l):
          kls.if(is.placeholder(k), k, l, kls(rest))

def kl.pick(c: Cmp, x: KL, y: KL) -> KL:
  match c:
    case LT{}:
      x
    case _:
      y

def kl.less(x: KL, y: KL) -> KL:
  match x:
    case KL{+kx, lx}:
      match y:
        case KL{+ky, ly}:
          kl.pick(Pair.snd(String & String, Cmp, String.cmp(kx, ky)), KL{kx, lx}, KL{ky, ly})

# The name first in order (Map.toList's first).
def kl.min(xs: List<&2, KL>, best: KL) -> KL:
  match xs:
    case Nil{}:
      best
    case Con{x, rest}:
      kl.min(rest, kl.less(x, best))

def missing.at(kl: KL) -> Rs.ResErr:
  match kl:
    case KL{k, l}:
      Rs.MissingDefinitionAt{l, k}

def missing.of(xs: List<&2, KL>, +refs: Refs()) -> Rs.ResErr:
  match xs:
    case Nil{}:
      Rs.MissingDefinitions{Map.keys(&2, L.Loc, refs)}
    case Con{x, rest}:
      missing.at(kl.min(rest, x))

# A name left over that no placeholder accounts for is one the program
# never defines: the first by name, where it is used.
def missing(+refs: Refs()) -> Rs.ResErr:
  missing.of(kls(Map.to_list(&2, L.Loc, refs)), refs)

# The references left over at the top are the placeholders of recursion
# sites outside every binding, each applied in turn (addRepeaters).
def add.repeaters(fuel: Nat, st: ARS) -> R(T.Term1()):
  match fuel:
    case 0n:
      Fail{Rs.MissingDefinitions{["(nesting too deep)"]}}
    case 1n+f:
      match st:
        case ARGo{empty, +refs, t}:
          match empty:
            case True{}:
              Done{t}
            case False{}:
              match t:
                case T.TApp{a, x, T.TVar{b, +v}}:
                  add.repeaters(f, ARFound{refs.has(refs, v), a, x, v, refs})
                case _:
                  Fail{missing(refs)}
        case ARFound{found, +a, x, v, +refs}:
          match found:
            case False{}:
              Fail{missing(refs)}
            case True{}:
              +rest = Map.del(&2, L.Loc, refs, v)
              do Result<&2, &2, Rs.ResErr, T.Term1()>:
                x2 : T.Term1() <- add.repeaters(f, ARGo{Nat.is_eq(refs.size(rest), 0n), rest, x})
                return T.TApp{a, x2, T.TRep{a}}

def cleanup(v: LV) -> R(T.Term1()):
  match v:
    case LVT{t, +refs}:
      add.repeaters(fuel(), ARGo{Nat.is_eq(refs.size(refs), 0n), refs, t})
    case _:
      Fail{not.term()}

# main2Term3let's Term2, the one EAL certifies, sizing sizes and the
# command runs.
def process(+t: S.Desugared()) -> R(T.Term2()):
  do Result<&2, &2, Rs.ResErr, T.T<Nat>>:
    v : LV <- lta(fuel(), LNT{cap.top(annotate(fuel(), AT{t})(0n))})
    t1 : T.T<String> <- cleanup(v)
    t2 : T.T<Nat> <- debruijn(fuel(), [], t1)
    return hashed(close.lams(fuel(), True{}, t2))
