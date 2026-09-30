import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Term.bend as T
import ./Resolve.bend as Rs
import ./Show.bend as Sh
import ./Sha256.bend as Sha

# From the desugared program to Term2 (haskell-final's Telomare.Resolve),
# two ways, as Haskell does:
#
# - process (main2Term3): validateVariables inlines every let binding at
#   each use, then debruijinize. EAL certifies this term, and its variable
#   check is where a missing definition is reported.
# - processWlet (main2Term3let): annotateUnsizedCount, letsToApps (lets
#   become lambda redexes, each recursion site a placeholder argument),
#   debruijinizeApp and closeLams. Sizing and the run take this one.

type Cyc is Data:
  CEnd{}
  CAt{+c: String, +seen: Bool}

type DN is Data:
  DT{+t: S.Surf}
  DTs{+xs: List<&2, S.Surf>}
  DBs{+bs: List<&2, S.Bind>}

type VN is Data:
  VTerm{+t: S.Surf}
  VList{+xs: List<&2, S.Surf>}
  VLet{+bs: List<&2, Rs.NB>, +inner: S.Surf}
  VOrdered{+r: Result<&2, &2, Rs.ResErr, List<&2, Rs.NB>>, +inner: S.Surf}

type VV is Data:
  VT{+t: T.T}
  VTs{+xs: List<&2, T.T>}

type Ctx is Data:
  Ctx{+k: T.LamKind, +name: String}

type Hit is Data:
  Hit{+i: Nat, +k: T.LamKind}
  Miss{}

type AN is Data:
  AT{+t: S.Surf}
  ABs{+bs: List<&2, S.Bind>}

type AV is Data:
  AVT{+t: S.Surf}
  AVBs{+bs: List<&2, S.Bind>}

type LB is Data:
  LB{+name: String, +t: T.T, +refs: Set(), +c: Nat}

type LN is Data:
  LNT{+t: S.Surf}
  LNTs{+xs: List<&2, S.Surf>}
  LNBs{+bs: List<&2, S.Bind>}

type LV is Data:
  LVT{+t: T.T, +refs: Set()}
  LVTs{+ts: List<&2, T.T>, +refs: Set()}
  LVBs{+bs: List<&2, LB>}

type TSt is Data:
  TSt{+todo: List<&2, String>, +acc: Set()}

type ARS is Data:
  ARGo{+empty: Bool, +refs: Set(), +t: T.T}
  ARFound{+found: Bool, +a: L.Loc, +x: T.T, +v: String, +refs: Set()}

def R(-A: Data) -> Data:
  Result<&2, &2, Rs.ResErr, A>

def fuel() -> Nat:
  U32.to_nat(4294967295)

def has(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

def union(a: Set(), b: Set()) -> Set():
  Map.union(&2, Unit, a, b)

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

def bind.names(bs: List<&2, S.Bind>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          L.Name.text(name) <> bind.names(rest)

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

# validateVariables (the process path)
# ------------------------------------

def dd.var(yes: Bool, +name: String) -> Set():
  match yes:
    case True{}:
      Set.add(Set.new(), name)
    case False{}:
      Set.new()

# The names of `names` a let binding's value uses directly (getDirectDeps).
def dd(+fuel: Nat, +names: Set(), n: DN) -> Set():
  match fuel:
    case 0n:
      Set.new()
    case 1n+f:
      match n:
        case DT{t}:
          match t:
            case S.SVar{loc, +name}:
              dd.var(has(names, name), name)
            case S.SLam{loc, v, body}:
              Set.del(dd(f, names, DT{body}), L.Name.text(v))
            case S.SLamN{loc, k, v, body}:
              Set.del(dd(f, names, DT{body}), L.Name.text(v))
            case S.SLet{loc, +binds, body}:
              +bound = bind.names(binds)
              union(minus(bound, dd(f, names, DBs{binds})), minus(bound, dd(f, names, DT{body})))
            case S.SIte{loc, a, b, c}:
              union(dd(f, names, DT{a}), union(dd(f, names, DT{b}), dd(f, names, DT{c})))
            case S.SPair{loc, a, b}:
              union(dd(f, names, DT{a}), dd(f, names, DT{b}))
            case S.SList{loc, xs}:
              dd(f, names, DTs{xs})
            case S.SApp{loc, a, b}:
              union(dd(f, names, DT{a}), dd(f, names, DT{b}))
            case S.SRec{loc, a, b, c}:
              union(dd(f, names, DT{a}), union(dd(f, names, DT{b}), dd(f, names, DT{c})))
            case S.SLeft{loc, x}:
              dd(f, names, DT{x})
            case S.SRight{loc, x}:
              dd(f, names, DT{x})
            case S.STrace{loc, x}:
              dd(f, names, DT{x})
            case S.SCheck{loc, a, b}:
              union(dd(f, names, DT{a}), dd(f, names, DT{b}))
            case S.SHash{loc, x}:
              dd(f, names, DT{x})
            case _:
              Set.new()
        case DTs{xs}:
          match xs:
            case Nil{}:
              Set.new()
            case Con{x, rest}:
              union(dd(f, names, DT{x}), dd(f, names, DTs{rest}))
        case DBs{bs}:
          match bs:
            case Nil{}:
              Set.new()
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  union(dd(f, names, DT{val}), dd(f, names, DBs{rest}))

def let.deps(bs: List<&2, S.Bind>, +names: Set(), acc: Map<&2, Set()>) -> Map<&2, Set()>:
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          let.deps(rest, names, Map.set(&2, Set(), acc, L.Name.text(name), dd(fuel(), names, DT{val})))

def intersects(xs: List<&2, String>, +s: Set()) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      has(s, x) || intersects(rest, s)

# Whether a binding uses one written after it (hasForwardRef).
def forward(names: List<&2, String>, +deps: Map<&2, Set()>) -> Bool:
  match names:
    case Nil{}:
      False{}
    case Con{n, +rest}:
      intersects(rest, deps.of(deps, n)) || forward(rest, deps)

def nbs(bs: List<&2, S.Bind>) -> List<&2, Rs.NB>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          Rs.NB{L.Name.text(name), val} <> nbs(rest)

def with.name.if(yes: Bool, b: Rs.NB, rest: List<&2, Rs.NB>) -> List<&2, Rs.NB>:
  match yes:
    case True{}:
      b <> rest
    case False{}:
      rest

def with.name(bs: List<&2, Rs.NB>, +n: String) -> List<&2, Rs.NB>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case Rs.NB{+name, val}:
          with.name.if(String.eq(name, n), Rs.NB{name, val}, with.name(rest, n))

# [(name, def) | name <- sorted, (name', def) <- bindings, name == name']
def in.order(sorted: List<&2, String>, +bs: List<&2, Rs.NB>) -> List<&2, Rs.NB>:
  match sorted:
    case Nil{}:
      []
    case Con{n, rest}:
      List.append(&2, Rs.NB, with.name(bs, n), in.order(rest, bs))

def let.sorted(+bs: List<&2, Rs.NB>, r: R(List<&2, String>)) -> R(List<&2, Rs.NB>):
  match r:
    case Fail{e}:
      Fail{e}
    case Done{sorted}:
      Done{in.order(sorted, bs)}

def let.order.pick(+bs: List<&2, S.Bind>, +names: List<&2, String>, +deps: Map<&2, Set()>, fwd: Bool) ->
  R(List<&2, Rs.NB>):
  match fwd:
    case True{}:
      let.sorted(nbs(bs), topological.sort(names, deps))
    case False{}:
      Done{nbs(bs)}

# The order a let's bindings are checked in: as written, unless one uses a
# later one; then dependency order.
def let.order(+bs: List<&2, S.Bind>) -> R(List<&2, Rs.NB>):
  +names = bind.names(bs)
  +deps = let.deps(bs, Set.from_list(names), Map.new(&2, Set()))
  let.order.pick(bs, names, deps, forward(names, deps))

def env.get.if(yes: Bool, +env: Map<&2, T.T>, +n: String) -> Maybe<&2, T.T>:
  match yes:
    case True{}:
      Some{Pair.snd(Map<&2, T.T>, T.T, Map.get(T.T, T.TZero{L.Unknown{}}, env, n))}
    case False{}:
      None{}

def env.get(+env: Map<&2, T.T>, +n: String) -> Maybe<&2, T.T>:
  env.get.if(Pair.snd(Map<&2, T.T>, Bool, Map.has(&2, T.T, env, n)), env, n)

def var.found(+loc: L.Loc, +n: String, m: Maybe<&2, T.T>) -> R(T.T):
  match m:
    case Some{t}:
      Done{t}
    case None{}:
      Fail{Rs.MissingDefinitionAt{loc, n}}

def pairs(+loc: L.Loc, xs: List<&2, T.T>) -> T.T:
  match xs:
    case Nil{}:
      T.TZero{loc}
    case Con{x, rest}:
      T.TPair{loc, x, pairs(loc, rest)}

def vt(v: VV) -> T.T:
  match v:
    case VT{t}:
      t
    case _:
      T.TZero{L.Unknown{}}

def vts(v: VV) -> List<&2, T.T>:
  match v:
    case VTs{xs}:
      xs
    case _:
      []

def open.lambda(+name: String, +body: T.T) -> T.T:
  T.TLam{T.T.loc(body), T.Open{}, name, body}

# Check every variable, inlining each let binding's checked value at every
# use (validateVariables).
def validate(+fuel: Nat, +env: Map<&2, T.T>, n: VN) -> R(VV):
  match fuel:
    case 0n:
      Fail{Rs.MissingDefinitions{["(nesting too deep)"]}}
    case 1n+f:
      match n:
        case VOrdered{r, inner}:
          match r:
            case Fail{e}:
              Fail{e}
            case Done{bs}:
              validate(f, env, VLet{bs, inner})
        case VLet{bs, inner}:
          match bs:
            case Nil{}:
              validate(f, env, VTerm{inner})
            case Con{b, rest}:
              match b:
                case Rs.NB{name, val}:
                  do Result<&2, &2, Rs.ResErr, VV>:
                    d : VV <- validate(f, env, VTerm{val})
                    validate(f, Map.set(&2, T.T, env, name, vt(d)), VLet{rest, inner})
        case VList{xs}:
          match xs:
            case Nil{}:
              Done{VTs{[]}}
            case Con{x, rest}:
              do Result<&2, &2, Rs.ResErr, VV>:
                x2 : VV <- validate(f, env, VTerm{x})
                r2 : VV <- validate(f, env, VList{rest})
                return VTs{vt(x2) <> vts(r2)}
        case VTerm{t}:
          match t:
            case S.SLet{loc, binds, inner}:
              validate(f, env, VOrdered{let.order(binds), inner})
            case S.SLam{loc, v, body}:
              do Result<&2, &2, Rs.ResErr, VV>:
                b2 : VV <- validate(f, Map.set(&2, T.T, env, L.Name.text(v), T.TVar{generated.var(), L.Name.text(v)}), VTerm{body})
                return VT{open.lambda(L.Name.text(v), vt(b2))}
            case S.SLamN{loc, k, v, body}:
              do Result<&2, &2, Rs.ResErr, VV>:
                b2 : VV <- validate(f, Map.set(&2, T.T, env, L.Name.text(v), T.TVar{generated.var(), L.Name.text(v)}), VTerm{body})
                return VT{open.lambda(L.Name.text(v), vt(b2))}
            case S.SVar{+loc, +name}:
              do Result<&2, &2, Rs.ResErr, VV>:
                x : T.T <- var.found(loc, name, env.get(env, name))
                return VT{x}
            case S.SIte{loc, a, b, c}:
              do Result<&2, &2, Rs.ResErr, VV>:
                a2 : VV <- validate(f, env, VTerm{a})
                b2 : VV <- validate(f, env, VTerm{b})
                c2 : VV <- validate(f, env, VTerm{c})
                return VT{T.TIte{loc, vt(a2), vt(b2), vt(c2)}}
            case S.SInt{loc, k}:
              Done{VT{T.ints.i2t(U32.to_nat(k), loc)}}
            case S.SStr{loc, s}:
              Done{VT{T.ints.s2t(s, loc)}}
            case S.SZero{loc}:
              Done{VT{T.TZero{loc}}}
            case S.SPair{loc, a, b}:
              do Result<&2, &2, Rs.ResErr, VV>:
                a2 : VV <- validate(f, env, VTerm{a})
                b2 : VV <- validate(f, env, VTerm{b})
                return VT{T.TPair{loc, vt(a2), vt(b2)}}
            case S.SList{+loc, xs}:
              do Result<&2, &2, Rs.ResErr, VV>:
                x2 : VV <- validate(f, env, VList{xs})
                return VT{pairs(loc, vts(x2))}
            case S.SApp{loc, a, b}:
              do Result<&2, &2, Rs.ResErr, VV>:
                a2 : VV <- validate(f, env, VTerm{a})
                b2 : VV <- validate(f, env, VTerm{b})
                return VT{T.TApp{loc, vt(a2), vt(b2)}}
            case S.SRec{+loc, a, b, c}:
              do Result<&2, &2, Rs.ResErr, VV>:
                a2 : VV <- validate(f, env, VTerm{a})
                b2 : VV <- validate(f, env, VTerm{b})
                c2 : VV <- validate(f, env, VTerm{c})
                return VT{T.TApp{loc, T.TRec{loc, vt(a2), vt(b2), vt(c2)}, T.TRep{loc}}}
            case S.SChurch{loc, k}:
              Done{VT{T.TChurch{loc, k}}}
            case S.SLeft{loc, x}:
              do Result<&2, &2, Rs.ResErr, VV>:
                x2 : VV <- validate(f, env, VTerm{x})
                return VT{T.TLeft{loc, vt(x2)}}
            case S.SRight{loc, x}:
              do Result<&2, &2, Rs.ResErr, VV>:
                x2 : VV <- validate(f, env, VTerm{x})
                return VT{T.TRight{loc, vt(x2)}}
            case S.STrace{loc, x}:
              do Result<&2, &2, Rs.ResErr, VV>:
                x2 : VV <- validate(f, env, VTerm{x})
                return VT{T.TTrace{loc, vt(x2)}}
            case S.SCheck{loc, a, b}:
              do Result<&2, &2, Rs.ResErr, VV>:
                a2 : VV <- validate(f, env, VTerm{a})
                b2 : VV <- validate(f, env, VTerm{b})
                return VT{T.TCheck{loc, vt(a2), vt(b2)}}
            case S.SHash{loc, x}:
              do Result<&2, &2, Rs.ResErr, VV>:
                x2 : VV <- validate(f, env, VTerm{x})
                return VT{T.THash{loc, vt(x2)}}
            case _:
              Fail{not.term()}

# de Bruijn indices (debruijinize, debruijinizeApp)
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

def repeaters(c: Nat, +anno: L.Loc, ix: T.T) -> T.T:
  match c:
    case 0n:
      ix
    case 1n+k:
      repeaters(k, anno, T.TApp{generated.var(), ix, T.TRep{anno}})

# A variable's index; under debruijinizeApp a let-bound one also takes its
# binding's placeholders, fresh at each use.
def index.of(+anno: L.Loc, +n: String, app: Bool, h: Hit) -> R(T.T):
  match app:
    case True{}:
      match h:
        case Miss{}:
          Fail{Rs.MissingDefinitions{["undefined identifier " ++ n]}}
        case Hit{i, k}:
          match k:
            case T.LetB{c}:
              Done{repeaters(c, anno, T.TIdx{generated.var(), i})}
            case _:
              Done{T.TIdx{generated.var(), i}}
    case False{}:
      match h:
        case Miss{}:
          Fail{Rs.MissingDefinitions{["undefined identifier " ++ n]}}
        case Hit{i, k}:
          Done{T.TIdx{generated.var(), i}}

def debruijn(+fuel: Nat, +app: Bool, +ctx: List<&2, Ctx>, t: T.T) -> R(T.T):
  match fuel:
    case 0n:
      Fail{Rs.MissingDefinitions{["(nesting too deep)"]}}
    case 1n+f:
      match t:
        case T.TLam{a, +k, +name, body}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            b2 : T.T <- debruijn(f, app, Ctx{k, name} <> ctx, body)
            return T.TLam{a, conv.kind(k), name, b2}
        case T.TVar{+a, +name}:
          index.of(a, name, app, lookup.at(ctx, name, 0n))
        case T.TApp{a, x, y}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            y2 : T.T <- debruijn(f, app, ctx, y)
            return T.TApp{a, x2, y2}
        case T.TPair{a, x, y}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            y2 : T.T <- debruijn(f, app, ctx, y)
            return T.TPair{a, x2, y2}
        case T.TCheck{a, x, y}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            y2 : T.T <- debruijn(f, app, ctx, y)
            return T.TCheck{a, x2, y2}
        case T.TIte{a, x, y, z}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            y2 : T.T <- debruijn(f, app, ctx, y)
            z2 : T.T <- debruijn(f, app, ctx, z)
            return T.TIte{a, x2, y2, z2}
        case T.TRec{a, x, y, z}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            y2 : T.T <- debruijn(f, app, ctx, y)
            z2 : T.T <- debruijn(f, app, ctx, z)
            return T.TRec{a, x2, y2, z2}
        case T.TLeft{a, x}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            return T.TLeft{a, x2}
        case T.TRight{a, x}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            return T.TRight{a, x2}
        case T.TTrace{a, x}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            return T.TTrace{a, x2}
        case T.THash{a, x}:
          do Result<&2, &2, Rs.ResErr, T.T>:
            x2 : T.T <- debruijn(f, app, ctx, x)
            return T.THash{a, x2}
        case other:
          Done{other}

def close.lam(naked: Bool, k: T.LamKind, name: String, +body: T.T) -> T.T:
  match naked:
    case True{}:
      T.TLam{T.T.loc(body), T.Closed{}, name, body}
    case False{}:
      T.TLam{T.T.loc(body), k, name, body}

# A lambda outside every lambda is closed; every lambda takes its body's
# annotation (closeLams).
def close.lams(+fuel: Nat, +naked: Bool, t: T.T) -> T.T:
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
        case T.TCheck{a, x, y}:
          T.TCheck{a, close.lams(f, naked, x), close.lams(f, naked, y)}
        case T.TIte{a, x, y, z}:
          T.TIte{a, close.lams(f, naked, x), close.lams(f, naked, y), close.lams(f, naked, z)}
        case T.TRec{a, x, y, z}:
          T.TRec{a, close.lams(f, naked, x), close.lams(f, naked, y), close.lams(f, naked, z)}
        case T.TLeft{a, x}:
          T.TLeft{a, close.lams(f, naked, x)}
        case T.TRight{a, x}:
          T.TRight{a, close.lams(f, naked, x)}
        case T.TTrace{a, x}:
          T.TTrace{a, close.lams(f, naked, x)}
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
def show(t: T.T, +paren: Bool, acc: String) -> String:
  match t:
    case T.TZero{a}:
      lp(paren) ++ "Fix \"ZeroSF\"" ++ rp(paren, acc)
    case T.TPair{a, x, y}:
      lp(paren) ++ "Fix \"PairSF (\"" ++ show(x, False{}, "\", \"" ++ show(y, False{}, "\")\"" ++ rp(paren, acc)))
    case T.TVar{a, name}:
      lp(paren) ++ "Fix VarUPF " ++ Sh.string(name) ++ rp(paren, acc)
    case T.TIdx{a, i}:
      lp(paren) ++ "Fix VarUPF " ++ U32.show(U32.from_nat(i)) ++ rp(paren, acc)
    case T.TApp{a, f, x}:
      lp(paren) ++ "Fix AppUPF " ++ show(f, True{}, " " ++ show(x, True{}, rp(paren, acc)))
    case T.TLam{a, k, name, body}:
      lp(paren) ++ "Fix LamUPF " ++ kind.show(k) ++ " " ++ show(body, True{}, rp(paren, acc))
    case T.TCheck{a, x, y}:
      lp(paren) ++ "Fix CheckUPF " ++ show(x, True{}, " " ++ show(y, True{}, rp(paren, acc)))
    case T.TIte{a, x, y, z}:
      lp(paren) ++ "Fix ITEUPF " ++ show(x, True{}, " " ++ show(y, True{}, " " ++ show(z, True{}, rp(paren, acc))))
    case T.TLeft{a, x}:
      lp(paren) ++ "Fix LeftUPF " ++ show(x, True{}, rp(paren, acc))
    case T.TRight{a, x}:
      lp(paren) ++ "Fix RightUPF " ++ show(x, True{}, rp(paren, acc))
    case T.TTrace{a, x}:
      lp(paren) ++ "Fix TraceUPF " ++ show(x, True{}, rp(paren, acc))
    case T.THash{a, x}:
      lp(paren) ++ "Fix HashUPF " ++ show(x, True{}, rp(paren, acc))
    case T.TChurch{a, n}:
      lp(paren) ++ "Fix ChurchUPF " ++ U32.show(n) ++ rp(paren, acc)
    case T.TRec{a, x, y, z}:
      lp(paren) ++ "Fix UnsizedRecursionUPF " ++ show(x, True{}, " " ++ show(y, True{}, " " ++ show(z, True{}, rp(paren, acc))))
    case T.TRep{a}:
      lp(paren) ++ "Fix TUnsizedRepeaterF" ++ rp(paren, acc)

# ints2t
def ints(bs: List<&2, U32>, +loc: L.Loc) -> T.T:
  match bs:
    case Nil{}:
      T.TZero{loc}
    case Con{b, rest}:
      T.TPair{loc, T.ints.i2t(U32.to_nat(b), loc), ints(rest, loc)}

# generateAllHashes: every `#` (HashF), innermost first, becomes a number
# for its term: the last 8 bytes of the SHA-256 of the term's `show`, as a
# list, at the whole term's location.
def hashes(t: T.T, +loc: L.Loc) -> T.T:
  match t:
    case T.THash{a, x}:
      ints(List.drop(&2, U32, Sha.raw(show(hashes(x, loc), False{}, "")), 24n), loc)
    case T.TPair{a, x, y}:
      T.TPair{a, hashes(x, loc), hashes(y, loc)}
    case T.TApp{a, f, x}:
      T.TApp{a, hashes(f, loc), hashes(x, loc)}
    case T.TLam{a, k, name, body}:
      T.TLam{a, k, name, hashes(body, loc)}
    case T.TCheck{a, x, y}:
      T.TCheck{a, hashes(x, loc), hashes(y, loc)}
    case T.TIte{a, x, y, z}:
      T.TIte{a, hashes(x, loc), hashes(y, loc), hashes(z, loc)}
    case T.TLeft{a, x}:
      T.TLeft{a, hashes(x, loc)}
    case T.TRight{a, x}:
      T.TRight{a, hashes(x, loc)}
    case T.TTrace{a, x}:
      T.TTrace{a, hashes(x, loc)}
    case T.TRec{a, x, y, z}:
      T.TRec{a, hashes(x, loc), hashes(y, loc), hashes(z, loc)}
    case other:
      other

def hashed(+t: T.T) -> T.T:
  hashes(t, T.T.loc(t))

# main2Term3's Term2.
def process(t: S.Surf) -> R(T.T):
  do Result<&2, &2, Rs.ResErr, T.T>:
    v : VV <- validate(fuel(), Map.new(&2, T.T), VTerm{t})
    t2 : T.T <- debruijn(fuel(), False{}, [], vt(v))
    return hashed(t2)

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

def avt(v: AV) -> S.Surf:
  match v:
    case AVT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def avbs(v: AV) -> List<&2, S.Bind>:
  match v:
    case AVBs{bs}:
      bs
    case _:
      []

def site.name(n: Nat) -> String:
  ":" ++ Nat.show(n)

# \:0 -> \:1 -> ... x, one placeholder lambda per recursion site the
# binding's value holds, each knowing how many there are (cap).
def cap.lams(+i: Nat, +k: Nat, +anno: L.Loc, x: S.Surf) -> S.Surf:
  match i:
    case 0n:
      x
    case 1n+j:
      cap.lams(j, k, anno, S.SLamN{anno, k, L.Name{anno, site.name(j)}, x})

def cap.with(+k: Nat, +x: S.Surf) -> S.Surf:
  cap.lams(k, k, S.loc(x), x)

def cap.bind(name: L.Name, r: AV & Nat) -> S.Bind:
  (v, +k) = r
  S.Bind{name, cap.with(k, avt(v))}

# (\:0 -> (\:1 -> x) :1) :0 for the sites outside every binding (capTop).
def top.apps(+i: Nat, +anno: L.Loc, x: S.Surf) -> S.Surf:
  match i:
    case 0n:
      x
    case 1n+j:
      top.apps(j, anno, S.SApp{anno, S.SLam{anno, L.Name{anno, site.name(j)}, x}, S.SVar{anno, site.name(j)}})

def cap.top.with(k: Nat, +x: S.Surf) -> S.Surf:
  top.apps(k, S.loc(x), x)

def cap.top(r: AV & Nat) -> S.Surf:
  (v, k) = r
  cap.top.with(k, avt(v))

def list.items(t: S.Surf) -> List<&2, S.Surf>:
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
            case S.SCheck{loc, a, b}:
              do St<AV>:
                a2 : AV <- annotate(f, AT{a})
                b2 : AV <- annotate(f, AT{b})
                return AVT{S.SCheck{loc, avt(a2), avt(b2)}}
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
            case S.STrace{loc, x}:
              do St<AV>:
                x2 : AV <- annotate(f, AT{x})
                return AVT{S.STrace{loc, avt(x2)}}
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
            case other:
              St.pure(AV, AVT{other})

def lv.t(v: LV) -> T.T:
  match v:
    case LVT{t, refs}:
      t
    case _:
      T.TZero{L.Unknown{}}

def lv.refs(v: LV) -> Set():
  match v:
    case LVT{t, refs}:
      refs
    case LVTs{ts, refs}:
      refs
    case _:
      Set.new()

def lv.ts(v: LV) -> List<&2, T.T>:
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
def count.of(t: S.Surf) -> Nat:
  match t:
    case S.SLamN{loc, k, v, body}:
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
          lb.deps(rest, Map.set(&2, Set(), acc, name, refs))

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

def make.binding(name: String, d: T.T, c: Nat, +body: T.T) -> T.T:
  T.TApp{T.T.loc(body), T.TLam{T.T.loc(body), T.LetB{c}, name, body}, d}

# (\n -> body) value, the lambda a let binding with c placeholders
# (makeBinding).
def bindings.wrap(bs: List<&2, LB>, body: T.T) -> T.T:
  match bs:
    case Nil{}:
      body
    case Con{b, rest}:
      match b:
        case LB{name, t, refs, c}:
          make.binding(name, t, c, bindings.wrap(rest, body))

# A let becomes lambda redexes in dependency order, dropping the bindings
# its body cannot reach; what it still needs from outside is its refs.
def let.build(+inner: LV, +bs: List<&2, LB>, sorted: List<&2, String>) -> LV:
  +deps = lb.deps(bs, Map.new(&2, Set()))
  +trans = transitive(fuel(), deps, TSt{Set.to_list(lv.refs(inner)), Set.new()})
  +live = lb.live(lb.in.order(sorted, bs), trans)
  LVT{bindings.wrap(List.reverse(&2, LB, live), lv.t(inner)), minus(lb.names(live), trans)}

def lb.cons(name: String, +v: LV, c: Nat, r: LV) -> LV:
  LVBs{LB{name, lv.t(v), lv.refs(v), c} <> lv.bs(r)}

def left.mk(a: L.Loc, x: T.T) -> T.T:
  T.TLeft{a, x}

def right.mk(a: L.Loc, x: T.T) -> T.T:
  T.TRight{a, x}

def trace.mk(a: L.Loc, x: T.T) -> T.T:
  T.TTrace{a, x}

def hash.mk(a: L.Loc, x: T.T) -> T.T:
  T.THash{a, x}

def one(~k: L.Loc -> T.T -> T.T, +x: LV, a: L.Loc) -> LV:
  LVT{k(a, lv.t(x)), lv.refs(x)}

def list.lv(+a: L.Loc, +x: LV) -> LV:
  LVT{pairs(a, lv.ts(x)), lv.refs(x)}

def lts.cons(+x: LV, +r: LV) -> LV:
  LVTs{lv.t(x) <> lv.ts(r), union(lv.refs(x), lv.refs(r))}

def app.mk(a: L.Loc, x: T.T, y: T.T) -> T.T:
  T.TApp{a, x, y}

def pair.mk(a: L.Loc, x: T.T, y: T.T) -> T.T:
  T.TPair{a, x, y}

def check.mk(a: L.Loc, x: T.T, y: T.T) -> T.T:
  T.TCheck{a, x, y}

def ite.mk(a: L.Loc, x: T.T, y: T.T, z: T.T) -> T.T:
  T.TIte{a, x, y, z}

def rec.mk(a: L.Loc, x: T.T, y: T.T, z: T.T) -> T.T:
  T.TRec{a, x, y, z}

def two(~k: L.Loc -> T.T -> T.T -> T.T, +x: LV, +y: LV, a: L.Loc) -> LV:
  LVT{k(a, lv.t(x), lv.t(y)), union(lv.refs(x), lv.refs(y))}

def three(~k: L.Loc -> T.T -> T.T -> T.T -> T.T, +x: LV, +y: LV, +z: LV, a: L.Loc) -> LV:
  LVT{k(a, lv.t(x), lv.t(y), lv.t(z)), union(lv.refs(x), union(lv.refs(y), lv.refs(z)))}

def lam.kind.of(+refs: Set(), placeholder: Bool) -> T.LamKind:
  match placeholder:
    case True{}:
      T.Open{}
    case False{}:
      lam.kind(Set.size(refs))

# A lambda is closed when nothing inside refers outside it and it is no
# placeholder lambda.
def lam.done(a: L.Loc, +name: String, +b: LV, placeholder: Bool) -> LV:
  +refs = Set.del(lv.refs(b), name)
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
              Done{LVTs{[], Set.new()}}
            case Con{x, rest}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                r2 : LV <- lta(f, LNTs{rest})
                return lts.cons(x2, r2)
        case LNT{t}:
          match t:
            case S.SVar{a, +name}:
              Done{LVT{T.TVar{a, name}, Set.add(Set.new(), name)}}
            case S.SLam{a, v, body}:
              do Result<&2, &2, Rs.ResErr, LV>:
                b2 : LV <- lta(f, LNT{body})
                return lam.done(a, L.Name.text(v), b2, False{})
            case S.SLamN{a, k, v, body}:
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
            case S.SCheck{a, x, y}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                y2 : LV <- lta(f, LNT{y})
                return two(~check.mk, x2, y2, a)
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
            case S.STrace{a, x}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                return one(~trace.mk, x2, a)
            case S.SHash{a, x}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNT{x})
                return one(~hash.mk, x2, a)
            case S.SList{+a, xs}:
              do Result<&2, &2, Rs.ResErr, LV>:
                x2 : LV <- lta(f, LNTs{xs})
                return list.lv(a, x2)
            case S.SInt{a, k}:
              Done{LVT{T.ints.i2t(U32.to_nat(k), a), Set.new()}}
            case S.SStr{a, s}:
              Done{LVT{T.ints.s2t(s, a), Set.new()}}
            case S.SZero{a}:
              Done{LVT{T.TZero{a}, Set.new()}}
            case S.SChurch{a, k}:
              Done{LVT{T.TChurch{a, k}, Set.new()}}
            case _:
              Fail{not.term()}

# The references left over at the top are the placeholders of recursion
# sites outside every binding, each applied in turn (addRepeaters).
def add.repeaters(fuel: Nat, st: ARS) -> R(T.T):
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
                  add.repeaters(f, ARFound{has(refs, v), a, x, v, refs})
                case _:
                  Fail{Rs.MissingDefinitions{Set.to_list(refs)}}
        case ARFound{found, +a, x, v, +refs}:
          match found:
            case False{}:
              Fail{Rs.MissingDefinitions{Set.to_list(refs)}}
            case True{}:
              +rest = Set.del(refs, v)
              do Result<&2, &2, Rs.ResErr, T.T>:
                x2 : T.T <- add.repeaters(f, ARGo{Nat.is_eq(Set.size(rest), 0n), rest, x})
                return T.TApp{a, x2, T.TRep{a}}

def cleanup(v: LV) -> R(T.T):
  match v:
    case LVT{t, +refs}:
      add.repeaters(fuel(), ARGo{Nat.is_eq(Set.size(refs), 0n), refs, t})
    case _:
      Fail{not.term()}

# main2Term3let's Term2.
def process.let(t: S.Surf) -> R(T.T):
  do Result<&2, &2, Rs.ResErr, T.T>:
    v : LV <- lta(fuel(), LNT{cap.top(annotate(fuel(), AT{t})(0n))})
    t1 : T.T <- cleanup(v)
    t2 : T.T <- debruijn(fuel(), True{}, [], t1)
    return hashed(close.lams(fuel(), True{}, t2))
