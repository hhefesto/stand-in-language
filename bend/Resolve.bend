import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Show.bend as Sh

# Module resolution (master's Telomare.Resolve and Telomare.Error, the part
# before desugaring): the resolver's errors, and the pruning of the bindings
# `main` cannot reach. The names themselves are bound by bend/Bind.bend
# (master's Telomare.Bind, since 98c963c2), which replaced the import
# flattening that was here. Names are Base Sets, whose order is Haskell's
# String order.

# A definition a requirement was inherited through, and where it is.
type Via is Data:
  Via{+name: String, +loc: L.Loc}

# UnsuppliedRequirement: a requirement that reaches main unsupplied, where it
# occurs, and each definition it was inherited through, innermost first and
# ending with main. DuplicateDefinition: two entries with one key in one let
# block or module.
type ResErr is Data:
  NoMainFunction{+m: String}
  ModuleNotFound{+m: String}
  ImportCycle{+ms: List<&2, String>}
  DefinitionCycle{+ns: List<&2, String>}
  MissingDefinitions{+ns: List<&2, String>}
  MissingDefinitionAt{+loc: L.Loc, +n: String}
  UnsuppliedRequirement{+n: String, +loc: L.Loc, +via: List<&2, Via>}
  UnboundQualifiedName{+loc: L.Loc, +n: String}
  DuplicateDefinition{+loc: L.Loc, +n: String}

# A module and its expanded items; a binding by its plain name.
type Mod is Data:
  Mod{+name: String, +items: List<&2, S.EItem>}

type NB is Data:
  NB{+name: String, +val: S.Expanded()}

# Over-approximate on purpose, as Haskell's is: a let's binders are not
# removed, and a case adds the helpers its lowering will call.
type FN is Data:
  FT{+t: S.Expanded()}
  FP{+p: S.ExpandedPat()}
  FTs{+xs: List<&2, S.Expanded()>}
  FBs{+bs: List<&2, S.ExpandedBind()>}
  FAs{+alts: List<&2, S.ExpandedAlt()>}

# Each definition a requirement passed through, a line each.
def vias(vs: List<&2, Via>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{v, rest}:
      match v:
        case Via{n, l}:
          "\n  is required by " ++ Sh.string(n) ++ " (" ++ L.render_verbose(l) ++ ")" ++ vias(rest)

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
    case UnsuppliedRequirement{n, loc, via}:
      Sh.string(n) ++ " (at " ++ L.render_verbose(loc) ++ ")" ++ vias(via) ++ "\n  and is not defined"
    case UnboundQualifiedName{loc, n}:
      "qualified name " ++ Sh.string(n) ++ " is not defined, at " ++ L.render_verbose(loc)
    case DuplicateDefinition{loc, n}:
      Sh.string(n) ++ " is defined more than once in one block, at " ++ L.render_verbose(loc)

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
            case S.SCheck{loc, k, a, b}:
              union(fv(f, FT{a}), fv(f, FT{b}))
            case S.SIte{loc, a, b, c}:
              union(fv(f, FT{a}), union(fv(f, FT{b}), fv(f, FT{c})))
            case S.SLeft{loc, x}:
              fv(f, FT{x})
            case S.SRight{loc, x}:
              fv(f, FT{x})
            case S.SRec{loc, a, b, c}:
              union(fv(f, FT{a}), union(fv(f, FT{b}), fv(f, FT{c})))
            case S.SLet{loc, binds, body}:
              union(fv(f, FBs{binds}), fv(f, FT{body}))
            case S.SList{loc, xs}:
              fv(f, FTs{xs})
            case S.SCase{loc, scrut, alts, w}:
              union(fv(f, FT{scrut}), fv(f, FAs{alts}))
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

def free(t: S.Expanded()) -> Set():
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
def prune(root: S.Expanded(), +bs: List<&2, NB>) -> List<&2, NB>:
  keep(bs, reach(fuel(), deps(bs, Map.new(&2, Set())), False{}, free(root)))

# Modules
# -------

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

# The REPL's program
# ------------------

def located(bs: List<&2, NB>, +loc: L.Loc) -> List<&2, S.ExpandedBind()>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case NB{name, val}:
          S.Bind{L.Name{L.GenIn{"resolveMain.binding", loc}, name}, val} <> located(rest, loc)

# An expression under a let of the bindings it reaches, as the import
# flattening made one before the name binder (Bind.bend); the REPL, whose
# bindings are its own (master's app/Repl.hs), still builds it.
def main.let(x: S.Expanded(), bs: List<&2, NB>, +loc: L.Loc) -> S.Expanded():
  S.SLet{L.GenIn{"resolveMain", loc}, located(bs, loc), x}
