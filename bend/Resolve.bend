import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Show.bend as Sh

# Module resolution (haskell-final's Telomare.Resolve, the part before
# desugaring): imports flattened into one binding list, `main` found, and
# the bindings `main` cannot reach pruned away. Names are Base Sets, whose
# order is Haskell's String order.

type ResErr is Data:
  NoMainFunction{+m: String}
  ModuleNotFound{+m: String}
  ImportCycle{+ms: List<&2, String>}
  DefinitionCycle{+ns: List<&2, String>}
  MissingDefinitions{+ns: List<&2, String>}
  MissingDefinitionAt{+loc: L.Loc, +n: String}

# A module and its expanded items; a binding by its plain name.
type Mod is Data:
  Mod{+name: String, +items: List<&2, S.EItem>}

type NB is Data:
  NB{+name: String, +val: S.Surf}

# Over-approximate on purpose, as Haskell's is: a let's binders are not
# removed, and a case adds the helpers its lowering will call.
type FN is Data:
  FT{+t: S.Surf}
  FP{+p: S.Pat}
  FTs{+xs: List<&2, S.Surf>}
  FBs{+bs: List<&2, S.Bind>}
  FAs{+alts: List<&2, S.Alt>}

type QN is Data:
  QT{+t: S.Surf}
  QP{+p: S.Pat}
  QTs{+xs: List<&2, S.Surf>}
  QBs{+bs: List<&2, S.Bind>}
  QAs{+alts: List<&2, S.Alt>}

type QV is Data:
  VT{+t: S.Surf}
  VP{+p: S.Pat}
  VTs{+xs: List<&2, S.Surf>}
  VBs{+bs: List<&2, S.Bind>}
  VAs{+alts: List<&2, S.Alt>}

# What to resolve: a list of items, an imported module, or an import
# already checked.
type RS is Data:
  RItems{+stack: List<&2, String>, +items: List<&2, S.EItem>}
  RModule{+stack: List<&2, String>, +name: String, +found: Maybe<&2, List<&2, S.EItem>>}
  RChecked{+r: Result<&2, &2, ResErr, RS>}

# renderResolverError
def render(e: ResErr) -> String:
  match e:
    case NoMainFunction{m}:
      "NoMainFunction " ++ Sh.string(m)
    case ModuleNotFound{m}:
      "ModuleNotFound " ++ Sh.string(m)
    case ImportCycle{ms}:
      "ImportCycle " ++ Sh.strings(ms)
    case DefinitionCycle{ns}:
      "DefinitionCycle " ++ Sh.strings(ns)
    case MissingDefinitions{ns}:
      "MissingDefinitions " ++ Sh.strings(ns)
    case MissingDefinitionAt{loc, n}:
      "missing definition " ++ Sh.string(n) ++ " at " ++ L.render_verbose(loc)

def R(-A: Data) -> Data:
  Result<&2, &2, ResErr, A>

# Name sets
# ---------

def union(a: Set(), b: Set()) -> Set():
  Map.union(&2, Unit, a, b)

def one(+n: String) -> Set():
  Set.add(Set.new(), n)

def has(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

# Free variables (freeVarsDeep)
# -----------------------------

def case.refs() -> Set():
  Set.from_list(["and", "listEqual", "foldl", "abort"])

def fv(+fuel: Nat, n: FN) -> Set():
  match fuel:
    case 0n:
      Set.new()
    case 1n+f:
      match n:
        case FT{t}:
          match t:
            case S.SVar{loc, name}:
              one(name)
            case S.SApp{loc, a, b}:
              union(fv(f, FT{a}), fv(f, FT{b}))
            case S.SLam{loc, v, body}:
              Set.del(fv(f, FT{body}), L.Name.text(v))
            case S.SPair{loc, a, b}:
              union(fv(f, FT{a}), fv(f, FT{b}))
            case S.SCheck{loc, a, b}:
              union(fv(f, FT{a}), fv(f, FT{b}))
            case S.SIte{loc, a, b, c}:
              union(fv(f, FT{a}), union(fv(f, FT{b}), fv(f, FT{c})))
            case S.SLeft{loc, x}:
              fv(f, FT{x})
            case S.SRight{loc, x}:
              fv(f, FT{x})
            case S.STrace{loc, x}:
              fv(f, FT{x})
            case S.SHash{loc, x}:
              fv(f, FT{x})
            case S.SRec{loc, a, b, c}:
              union(fv(f, FT{a}), union(fv(f, FT{b}), fv(f, FT{c})))
            case S.SLet{loc, binds, body}:
              union(fv(f, FBs{binds}), fv(f, FT{body}))
            case S.SList{loc, xs}:
              fv(f, FTs{xs})
            case S.SCase{loc, scrut, alts}:
              union(fv(f, FT{scrut}), union(fv(f, FAs{alts}), case.refs()))
            case _:
              Set.new()
        case FP{p}:
          match p:
            case S.PAnn{q, t}:
              union(fv(f, FP{q}), fv(f, FT{t}))
            case S.PPair{a, b}:
              union(fv(f, FP{a}), fv(f, FP{b}))
            case _:
              Set.new()
        case FTs{xs}:
          match xs:
            case Nil{}:
              Set.new()
            case Con{x, rest}:
              union(fv(f, FT{x}), fv(f, FTs{rest}))
        case FBs{bs}:
          match bs:
            case Nil{}:
              Set.new()
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  union(fv(f, FT{val}), fv(f, FBs{rest}))
        case FAs{alts}:
          match alts:
            case Nil{}:
              Set.new()
            case Con{alt, rest}:
              match alt:
                case S.Alt{p, body}:
                  union(fv(f, FP{p}), union(fv(f, FT{body}), fv(f, FAs{rest})))

def fuel() -> Nat:
  U32.to_nat(4294967295)

def free(t: S.Surf) -> Set():
  fv(fuel(), FT{t})

# Pruning (pruneBindings)
# -----------------------

# name -> free variables of its value; a later binding of a name wins, as
# in Map.fromList.
def deps(bs: List<&2, NB>, acc: Map<&2, Set()>) -> Map<&2, Set()>:
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case NB{name, val}:
          deps(rest, Map.set(&2, Set(), acc, name, free(val)))

# r plus the free variables of every binding r names.
def grow(ks: List<&2, String>, +m: Map<&2, Set()>, acc: Set()) -> Set():
  match ks:
    case Nil{}:
      acc
    case Con{k, rest}:
      grow(rest, m, union(acc, Pair.snd(Map<&2, Set()>, Set(), Map.get(Set(), Set.new(), m, k))))

# Grow r until it stops growing.
def reach(fuel: Nat, +m: Map<&2, Set()>, same: Bool, +r: Set()) -> Set():
  match fuel:
    case 0n:
      r
    case 1n+f:
      match same:
        case True{}:
          r
        case False{}:
          +g = grow(Set.to_list(r), m, r)
          reach(f, m, Nat.is_eq(Set.size(r), Set.size(g)), g)

def keep.if(yes: Bool, b: NB, rest: List<&2, NB>) -> List<&2, NB>:
  match yes:
    case True{}:
      b <> rest
    case False{}:
      rest

def keep(bs: List<&2, NB>, +live: Set()) -> List<&2, NB>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case NB{+name, val}:
          keep.if(has(live, name), NB{name, val}, keep(rest, live))

# Keep the bindings main can reach, through other bindings (pruneBindings).
def prune(root: S.Surf, +bs: List<&2, NB>) -> List<&2, NB>:
  keep(bs, reach(fuel(), deps(bs, Map.new(&2, Set())), False{}, free(root)))

# Qualified imports (qualifyBindings)
# ----------------------------------

def vt(v: QV) -> S.Surf:
  match v:
    case VT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def vp(v: QV) -> S.Pat:
  match v:
    case VP{p}:
      p
    case _:
      S.PIgnore{}

def vts(v: QV) -> List<&2, S.Surf>:
  match v:
    case VTs{xs}:
      xs
    case _:
      []

def vbs(v: QV) -> List<&2, S.Bind>:
  match v:
    case VBs{bs}:
      bs
    case _:
      []

def vas(v: QV) -> List<&2, S.Alt>:
  match v:
    case VAs{alts}:
      alts
    case _:
      []

def bind.names(bs: List<&2, S.Bind>, acc: Set()) -> Set():
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          bind.names(rest, Set.add(acc, L.Name.text(name)))

# The variables a pattern binds (patternBinders).
def pat.binders(p: S.Pat, acc: Set()) -> Set():
  match p:
    case S.PVar{name}:
      Set.add(acc, L.Name.text(name))
    case S.PAnn{q, t}:
      pat.binders(q, acc)
    case S.PPair{a, b}:
      pat.binders(b, pat.binders(a, acc))
    case _:
      acc

def qualify.var(+loc: L.Loc, +name: String, q: String, rename: Bool) -> S.Surf:
  match rename:
    case True{}:
      S.SVar{loc, q ++ "." ++ name}
    case False{}:
      S.SVar{loc, name}

# Rename a module's own names to Q.name wherever they are not shadowed
# (qualifyTerm).
def qualify(+fuel: Nat, +names: Set(), +q: String, +bound: Set(), n: QN) -> QV:
  match fuel:
    case 0n:
      VT{S.SZero{L.Unknown{}}}
    case 1n+f:
      match n:
        case QT{t}:
          match t:
            case S.SVar{loc, +name}:
              VT{qualify.var(loc, name, q, has(names, name) && Bool.not(has(bound, name)))}
            case S.SApp{loc, a, b}:
              VT{S.SApp{loc, vt(qualify(f, names, q, bound, QT{a})), vt(qualify(f, names, q, bound, QT{b}))}}
            case S.SLam{loc, v, body}:
              VT{S.SLam{loc, v, vt(qualify(f, names, q, Set.add(bound, L.Name.text(v)), QT{body}))}}
            case S.SPair{loc, a, b}:
              VT{S.SPair{loc, vt(qualify(f, names, q, bound, QT{a})), vt(qualify(f, names, q, bound, QT{b}))}}
            case S.SCheck{loc, a, b}:
              VT{S.SCheck{loc, vt(qualify(f, names, q, bound, QT{a})), vt(qualify(f, names, q, bound, QT{b}))}}
            case S.SIte{loc, a, b, c}:
              VT{S.SIte{loc, vt(qualify(f, names, q, bound, QT{a})), vt(qualify(f, names, q, bound, QT{b})),
                         vt(qualify(f, names, q, bound, QT{c}))}}
            case S.SLeft{loc, x}:
              VT{S.SLeft{loc, vt(qualify(f, names, q, bound, QT{x}))}}
            case S.SRight{loc, x}:
              VT{S.SRight{loc, vt(qualify(f, names, q, bound, QT{x}))}}
            case S.STrace{loc, x}:
              VT{S.STrace{loc, vt(qualify(f, names, q, bound, QT{x}))}}
            case S.SHash{loc, x}:
              VT{S.SHash{loc, vt(qualify(f, names, q, bound, QT{x}))}}
            case S.SRec{loc, a, b, c}:
              VT{S.SRec{loc, vt(qualify(f, names, q, bound, QT{a})), vt(qualify(f, names, q, bound, QT{b})),
                         vt(qualify(f, names, q, bound, QT{c}))}}
            case S.SLet{loc, +binds, body}:
              +inner = union(bound, bind.names(binds, Set.new()))
              VT{S.SLet{loc, vbs(qualify(f, names, q, inner, QBs{binds})), vt(qualify(f, names, q, inner, QT{body}))}}
            case S.SList{loc, xs}:
              VT{S.SList{loc, vts(qualify(f, names, q, bound, QTs{xs}))}}
            case S.SCase{loc, scrut, alts}:
              VT{S.SCase{loc, vt(qualify(f, names, q, bound, QT{scrut})), vas(qualify(f, names, q, bound, QAs{alts}))}}
            case other:
              VT{other}
        case QP{p}:
          match p:
            case S.PAnn{r, t}:
              VP{S.PAnn{vp(qualify(f, names, q, bound, QP{r})), vt(qualify(f, names, q, bound, QT{t}))}}
            case S.PPair{a, b}:
              VP{S.PPair{vp(qualify(f, names, q, bound, QP{a})), vp(qualify(f, names, q, bound, QP{b}))}}
            case other:
              VP{other}
        case QTs{xs}:
          match xs:
            case Nil{}:
              VTs{[]}
            case Con{x, rest}:
              VTs{vt(qualify(f, names, q, bound, QT{x})) <> vts(qualify(f, names, q, bound, QTs{rest}))}
        case QBs{bs}:
          match bs:
            case Nil{}:
              VBs{[]}
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  VBs{S.Bind{name, vt(qualify(f, names, q, bound, QT{val}))}
                      <> vbs(qualify(f, names, q, bound, QBs{rest}))}
        case QAs{alts}:
          match alts:
            case Nil{}:
              VAs{[]}
            case Con{alt, rest}:
              match alt:
                case S.Alt{+p, body}:
                  VAs{S.Alt{vp(qualify(f, names, q, bound, QP{p})),
                            vt(qualify(f, names, q, pat.binders(p, bound), QT{body}))}
                      <> vas(qualify(f, names, q, bound, QAs{rest}))}

def nb.names(bs: List<&2, NB>, acc: Set()) -> Set():
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case NB{name, val}:
          nb.names(rest, Set.add(acc, name))

def qualify.all(bs: List<&2, NB>, +names: Set(), +q: String) -> List<&2, NB>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case NB{name, val}:
          NB{q ++ "." ++ name, vt(qualify(fuel(), names, q, Set.new(), QT{val}))}
            <> qualify.all(rest, names, q)

def qualified(qual: Maybe<&2, L.Name>, +bs: List<&2, NB>) -> List<&2, NB>:
  match qual:
    case None{}:
      bs
    case Some{q}:
      qualify.all(bs, nb.names(bs, Set.new()), L.Name.text(q))

# Imports (resolveModule, resolveItems)
# -------------------------------------

def find.mod.if(hit: Bool, items: List<&2, S.EItem>, later: Maybe<&2, List<&2, S.EItem>>) ->
  Maybe<&2, List<&2, S.EItem>>:
  match hit:
    case True{}:
      Some{items}
    case False{}:
      later

def find.mod(mods: List<&2, Mod>, +name: String) -> Maybe<&2, List<&2, S.EItem>>:
  match mods:
    case Nil{}:
      None{}
    case Con{m, rest}:
      match m:
        case Mod{n, items}:
          find.mod.if(String.eq(n, name), items, find.mod(rest, name))

def drop.until.if(hit: Bool, x: String, rest: List<&2, String>, later: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      x <> rest
    case False{}:
      later

def drop.until(xs: List<&2, String>, +m: String) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      drop.until.if(String.eq(x, m), x, rest, drop.until(rest, m))

def in.stack(xs: List<&2, String>, +m: String) -> Bool:
  List.contains(~String, ~String.eq, xs, m)

def import.check(+stack: List<&2, String>, +name: String, cyc: Bool,
                 found: Maybe<&2, List<&2, S.EItem>>) -> Result<&2, &2, ResErr, RS>:
  match cyc:
    case True{}:
      Fail{ImportCycle{List.append(&2, String, drop.until(stack, name), [name])}}
    case False{}:
      match found:
        case None{}:
          Fail{ModuleNotFound{name}}
        case Some{items}:
          Done{RItems{List.append(&2, String, stack, [name]), items}}

def resolve(+fuel: Nat, +mods: List<&2, Mod>, st: RS) -> R(List<&2, NB>):
  match fuel:
    case 0n:
      Fail{ModuleNotFound{"(imports nested too deeply)"}}
    case 1n+f:
      match st:
        case RModule{+stack, +name, found}:
          resolve(f, mods, RChecked{import.check(stack, name, in.stack(stack, name), found)})
        case RChecked{r}:
          match r:
            case Fail{e}:
              Fail{e}
            case Done{next}:
              resolve(f, mods, next)
        case RItems{+stack, items}:
          match items:
            case Nil{}:
              Done{[]}
            case Con{item, rest}:
              match item:
                case S.EBind{name, val}:
                  do Result<&2, &2, ResErr, List<&2, NB>>:
                    r : List<&2, NB> <- resolve(f, mods, RItems{stack, rest})
                    return NB{L.Name.text(name), val} <> r
                case S.EImport{imp}:
                  match imp:
                    case S.Import{loc, m, qual}:
                      do Result<&2, &2, ResErr, List<&2, NB>>:
                        bs : List<&2, NB> <- resolve(f, mods, RModule{stack, L.Name.text(m), find.mod(mods, L.Name.text(m))})
                        r : List<&2, NB> <- resolve(f, mods, RItems{stack, rest})
                        return List.append(&2, NB, qualified(qual, bs), r)

# main
# ----

def lookup.main.if(hit: Bool, val: S.Surf, later: Maybe<&2, S.Surf>) -> Maybe<&2, S.Surf>:
  match hit:
    case True{}:
      Some{val}
    case False{}:
      later

def lookup.main(bs: List<&2, NB>) -> Maybe<&2, S.Surf>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, rest}:
      match b:
        case NB{name, val}:
          lookup.main.if(String.eq(name, "main"), val, lookup.main(rest))

def located(bs: List<&2, NB>, +loc: L.Loc) -> List<&2, S.Bind>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case NB{name, val}:
          S.Bind{L.Name{L.GenIn{"resolveMain.binding", loc}, name}, val} <> located(rest, loc)

def main.let(x: S.Surf, bs: List<&2, NB>, +loc: L.Loc) -> S.Surf:
  S.SLet{L.GenIn{"resolveMain", loc}, located(bs, loc), x}

def main.found(+m: String, +bs: List<&2, NB>, found: Maybe<&2, S.Surf>) -> R(S.Surf):
  match found:
    case None{}:
      Fail{NoMainFunction{m}}
    case Some{+x}:
      Done{main.let(x, prune(x, bs), S.loc(x))}

# The whole program as one let around main (resolveMain).
def main.of(+m: String, +bs: List<&2, NB>) -> R(S.Surf):
  main.found(m, bs, lookup.main(bs))

def main.in(+mods: List<&2, Mod>, +m: String, found: Maybe<&2, List<&2, S.EItem>>) -> R(S.Surf):
  match found:
    case None{}:
      Fail{ModuleNotFound{m}}
    case Some{items}:
      do Result<&2, &2, ResErr, S.Surf>:
        bs : List<&2, NB> <- resolve(fuel(), mods, RItems{[m], items})
        main.of(m, bs)

def main(+mods: List<&2, Mod>, +m: String) -> R(S.Surf):
  main.in(mods, m, find.mod(mods, m))
