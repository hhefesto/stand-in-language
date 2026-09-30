import Base
import ./Loc.bend as L
import ./Syntax.bend as S

# Desugaring (haskell-final's Telomare.Desugar, desugarTerm): the builtins
# bound around the program, the case helpers aliased, applications of
# builtins turned into primitives where the builtin is in scope, and every
# `case` lowered to nested ifs over the case helpers.

type ON is Data:
  OT{+t: S.Surf}
  OD{+d: OD}
  OP{+p: S.Pat}
  OTs{+xs: List<&2, S.Surf>}
  OBs{+bs: List<&2, S.Bind>}
  OAs{+alts: List<&2, S.Alt>}

type OV is Data:
  VT{+t: S.Surf}
  VP{+p: S.Pat}
  VTs{+xs: List<&2, S.Surf>}
  VBs{+bs: List<&2, S.Bind>}
  VAs{+alts: List<&2, S.Alt>}

# The walk: children first, then `optimize` at every node. An application
# of an in-scope `pair` or `app` to two arguments is rebuilt at once; the
# decision rides into the next step as ODirect.
type OD is Data:
  ODirect{+anno: L.Loc, +b: L.Loc, +c: L.Loc, +name: String, +x: S.Surf, +y: S.Surf, +yes: Bool}

def has(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

# The builtins
# ------------

def lam1(+name: String, body: S.Surf) -> S.Surf:
  S.SLam{L.Builtin{name}, L.Name{L.Builtin{name}, "x"}, body}

def b.left(+l: L.Loc) -> S.Surf:
  S.SLeft{l, S.SVar{l, "x"}}

def b.right(+l: L.Loc) -> S.Surf:
  S.SRight{l, S.SVar{l, "x"}}

def b.trace(+l: L.Loc) -> S.Surf:
  S.STrace{l, S.SVar{l, "x"}}

def lam2(+name: String, body: S.Surf) -> S.Surf:
  S.SLam{L.Builtin{name}, L.Name{L.Builtin{name}, "x"},
    S.SLam{L.Builtin{name}, L.Name{L.Builtin{name}, "y"}, body}}

def builtin(+name: String, val: S.Surf) -> S.Bind:
  S.Bind{L.Name{L.Builtin{name}, name}, val}

# let zero = 0; left = \x -> left x; ... in t (addBuiltins)
def add.builtins(t: S.Surf) -> S.Surf:
  S.SLet{L.Gen{"addBuiltins"},
    [builtin("zero", S.SInt{L.Builtin{"zero"}, 0}),
     builtin("left", lam1("left", b.left(L.Builtin{"left"}))),
     builtin("right", lam1("right", b.right(L.Builtin{"right"}))),
     builtin("trace", lam1("trace", b.trace(L.Builtin{"trace"}))),
     builtin("pair", lam2("pair", S.SPair{L.Builtin{"pair"}, S.SVar{L.Builtin{"pair"}, "x"}, S.SVar{L.Builtin{"pair"}, "y"}})),
     builtin("app", lam2("app", S.SApp{L.Builtin{"app"}, S.SVar{L.Builtin{"app"}, "x"}, S.SVar{L.Builtin{"app"}, "y"}}))],
    t}

# Case helper aliases
# -------------------

def bound(bs: List<&2, S.Bind>, acc: Set()) -> Set():
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          bound(rest, Set.add(acc, L.Name.text(name)))

def alias.if(yes: Bool, +loc: L.Loc, +name: String, alias: String, rest: List<&2, S.Bind>) -> List<&2, S.Bind>:
  match yes:
    case True{}:
      S.Bind{L.Name{L.GenIn{"case helper " ++ name, loc}, alias}, S.SVar{loc, name}} <> rest
    case False{}:
      rest

def aliases(+names: Set(), +loc: L.Loc) -> List<&2, S.Bind>:
  alias.if(has(names, "and"), loc, "and", "__case_and",
    alias.if(has(names, "foldl"), loc, "foldl", "__case_foldl",
      alias.if(has(names, "listEqual"), loc, "listEqual", "__case_listEqual",
        alias.if(has(names, "abort"), loc, "abort", "__case_abort", []))))

# __case_and = and, ... for the helpers the program binds, ahead of its own
# bindings (addCaseHelperAliases).
def add.aliases(t: S.Surf) -> S.Surf:
  match t:
    case S.SLet{+loc, +binds, body}:
      S.SLet{loc, List.append(&2, S.Bind, aliases(bound(binds, Set.new()), loc), binds), body}
    case other:
      other

# Builtin applications (optimizeBuiltinFunctions)
# -----------------------------------------------

def vt(v: OV) -> S.Surf:
  match v:
    case VT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def vp(v: OV) -> S.Pat:
  match v:
    case VP{p}:
      p
    case _:
      S.PIgnore{}

def vts(v: OV) -> List<&2, S.Surf>:
  match v:
    case VTs{xs}:
      xs
    case _:
      []

def vbs(v: OV) -> List<&2, S.Bind>:
  match v:
    case VBs{bs}:
      bs
    case _:
      []

def vas(v: OV) -> List<&2, S.Alt>:
  match v:
    case VAs{alts}:
      alts
    case _:
      []

def is.builtin(l: L.Loc, +text: String) -> Bool:
  match l:
    case L.Builtin{name}:
      String.eq(name, text)
    case _:
      False{}

def update.if(builtin: Bool, scope: Set(), +text: String) -> Set():
  match builtin:
    case True{}:
      Set.add(scope, text)
    case False{}:
      Set.del(scope, text)

# A let or pattern binder shadows a builtin, unless it is the builtin's own
# binding (updateScope).
def update(+scope: Set(), n: L.Name) -> Set():
  match n:
    case L.Name{loc, +text}:
      update.if(is.builtin(loc, text), scope, text)

# foldr updateScope scope binders: the first binder decides last.
def update.binds(bs: List<&2, S.Bind>, +scope: Set()) -> Set():
  match bs:
    case Nil{}:
      scope
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          update(update.binds(rest, scope), name)

def update.pat(p: S.Pat, +scope: Set()) -> Set():
  match p:
    case S.PVar{name}:
      update(scope, name)
    case S.PAnn{q, t}:
      update.pat(q, scope)
    case S.PPair{a, b}:
      update.pat(a, update.pat(b, scope))
    case _:
      scope

# `\__builtin_arg -> K x __builtin_arg` for a builtin short one argument.
def partial.pair(+a: L.Loc, +x: S.Surf) -> S.Surf:
  S.SLam{a, L.Name{a, "__builtin_arg"}, S.SPair{S.loc(x), x, S.SVar{a, "__builtin_arg"}}}

def partial.app(+a: L.Loc, +x: S.Surf) -> S.Surf:
  S.SLam{a, L.Name{a, "__builtin_arg"}, S.SApp{S.loc(x), x, S.SVar{a, "__builtin_arg"}}}

def optimize.pick(yes: Bool, new: S.Surf, old: S.Surf) -> S.Surf:
  match yes:
    case True{}:
      new
    case False{}:
      old

def optimize.one(+scope: Set(), +a: L.Loc, +name: String, +x: S.Surf, +t: S.Surf) -> S.Surf:
  match name:
    case "left":
      optimize.pick(has(scope, "left"), S.SLeft{S.loc(x), x}, t)
    case "right":
      optimize.pick(has(scope, "right"), S.SRight{S.loc(x), x}, t)
    case "trace":
      optimize.pick(has(scope, "trace"), S.STrace{a, x}, t)
    case "pair":
      optimize.pick(has(scope, "pair"), partial.pair(a, x), t)
    case "app":
      optimize.pick(has(scope, "app"), partial.app(a, x), t)
    case _:
      t

def optimize.two(+scope: Set(), +a: L.Loc, +name: String, +x: S.Surf, +y: S.Surf, +t: S.Surf) -> S.Surf:
  match name:
    case "pair":
      optimize.pick(has(scope, "pair"), S.SPair{a, x, y}, t)
    case "app":
      optimize.pick(has(scope, "app"), S.SApp{a, x, y}, t)
    case _:
      t

# After a node's children: an application of an in-scope builtin becomes
# the primitive (optimize).
def optimize(+scope: Set(), +t: S.Surf) -> S.Surf:
  match t:
    case S.SApp{a, S.SApp{b, S.SVar{c, name}, x}, y}:
      optimize.two(scope, a, name, x, y, t)
    case S.SApp{a, S.SApp{b, f, x}, y}:
      t
    case S.SApp{a, S.SVar{c, name}, x}:
      optimize.one(scope, a, name, x, t)
    case _:
      t

def two.direct.if(yes: Bool, t: S.Surf) -> Maybe<&2, S.Surf>:
  match yes:
    case True{}:
      Some{t}
    case False{}:
      None{}

def two.direct(+scope: Set(), +anno: L.Loc, +name: String, +x: S.Surf, +y: S.Surf) -> Maybe<&2, S.Surf>:
  match name:
    case "pair":
      two.direct.if(has(scope, "pair"), S.SPair{anno, x, y})
    case "app":
      two.direct.if(has(scope, "app"), S.SApp{anno, x, y})
    case _:
      None{}

def direct(+scope: Set(), name: String) -> Bool:
  match name:
    case "pair":
      has(scope, "pair")
    case "app":
      has(scope, "app")
    case _:
      False{}

def direct.build(+anno: L.Loc, name: String, x: S.Surf, y: S.Surf) -> S.Surf:
  match name:
    case "pair":
      S.SPair{anno, x, y}
    case _:
      S.SApp{anno, x, y}

def go(+fuel: Nat, +scope: Set(), n: ON) -> OV:
  match fuel:
    case 0n:
      VT{S.SZero{L.Unknown{}}}
    case 1n+f:
      match n:
        case OT{t}:
          match t:
            case S.SApp{anno, S.SApp{b, S.SVar{c, +name}, x}, y}:
              go(f, scope, OD{ODirect{anno, b, c, name, x, y, direct(scope, name)}})
            case S.SApp{anno, a, y}:
              VT{optimize(scope, S.SApp{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{y}))})}
            case S.SLam{anno, v, body}:
              VT{S.SLam{anno, v, vt(go(f, Set.del(scope, L.Name.text(v)), OT{body}))}}
            case S.SPair{anno, a, b}:
              VT{optimize(scope, S.SPair{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b}))})}
            case S.SCheck{anno, a, b}:
              VT{optimize(scope, S.SCheck{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b}))})}
            case S.SIte{anno, a, b, c}:
              VT{optimize(scope, S.SIte{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b})), vt(go(f, scope, OT{c}))})}
            case S.SLeft{anno, x}:
              VT{optimize(scope, S.SLeft{anno, vt(go(f, scope, OT{x}))})}
            case S.SRight{anno, x}:
              VT{optimize(scope, S.SRight{anno, vt(go(f, scope, OT{x}))})}
            case S.STrace{anno, x}:
              VT{optimize(scope, S.STrace{anno, vt(go(f, scope, OT{x}))})}
            case S.SHash{anno, x}:
              VT{optimize(scope, S.SHash{anno, vt(go(f, scope, OT{x}))})}
            case S.SRec{anno, a, b, c}:
              VT{optimize(scope, S.SRec{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b})), vt(go(f, scope, OT{c}))})}
            case S.SLet{anno, +binds, body}:
              +inner = update.binds(binds, scope)
              VT{optimize(scope, S.SLet{anno, vbs(go(f, inner, OBs{binds})), vt(go(f, inner, OT{body}))})}
            case S.SList{anno, xs}:
              VT{optimize(scope, S.SList{anno, vts(go(f, scope, OTs{xs}))})}
            case S.SCase{anno, scrut, alts}:
              VT{optimize(scope, S.SCase{anno, vt(go(f, scope, OT{scrut})), vas(go(f, scope, OAs{alts}))})}
            case other:
              VT{optimize(scope, other)}
        case OD{d}:
          match d:
            case ODirect{+anno, b, c, +name, x, y, yes}:
              match yes:
                case True{}:
                  VT{optimize(scope, direct.build(anno, name, vt(go(f, scope, OT{x})), vt(go(f, scope, OT{y}))))}
                case False{}:
                  VT{optimize(scope, S.SApp{anno, vt(go(f, scope, OT{S.SApp{b, S.SVar{c, name}, x}})),
                                         vt(go(f, scope, OT{y}))})}
        case OP{p}:
          match p:
            case S.PAnn{q, t}:
              VP{S.PAnn{vp(go(f, scope, OP{q})), vt(go(f, scope, OT{t}))}}
            case S.PPair{a, b}:
              VP{S.PPair{vp(go(f, scope, OP{a})), vp(go(f, scope, OP{b}))}}
            case other:
              VP{other}
        case OTs{xs}:
          match xs:
            case Nil{}:
              VTs{[]}
            case Con{x, rest}:
              VTs{vt(go(f, scope, OT{x})) <> vts(go(f, scope, OTs{rest}))}
        case OBs{bs}:
          match bs:
            case Nil{}:
              VBs{[]}
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  VBs{S.Bind{name, vt(go(f, scope, OT{val}))} <> vbs(go(f, scope, OBs{rest}))}
        case OAs{alts}:
          match alts:
            case Nil{}:
              VAs{[]}
            case Con{alt, rest}:
              match alt:
                case S.Alt{+p, body}:
                  VAs{S.Alt{vp(go(f, scope, OP{p})), vt(go(f, update.pat(p, scope), OT{body}))}
                      <> vas(go(f, scope, OAs{rest}))}

def builtin.names() -> Set():
  Set.from_list(["left", "right", "trace", "pair", "app"])

def fuel() -> Nat:
  U32.to_nat(4294967295)

def optimize.builtins(t: S.Surf) -> S.Surf:
  vt(go(fuel(), builtin.names(), OT{t}))

# Case lowering (lowerCases)
# --------------------------

# Paths into a pattern, each the projections from its root, first taken
# first ("RL" is Left (Right x)): to its number leaves (findInts), string
# leaves (findStrings) and pairs (pairRoute2Dirs), left to right.

def ints.of(p: S.Pat, +path: String) -> List<&2, String>:
  match p:
    case S.PPair{a, b}:
      List.append(&2, String, ints.of(a, path ++ "L"), ints.of(b, path ++ "R"))
    case S.PInt{n}:
      [path]
    case S.PAnn{q, t}:
      ints.of(q, path)
    case _:
      []

def strs.of(p: S.Pat, +path: String) -> List<&2, String>:
  match p:
    case S.PPair{a, b}:
      List.append(&2, String, strs.of(a, path ++ "L"), strs.of(b, path ++ "R"))
    case S.PStr{t}:
      [path]
    case S.PAnn{q, t}:
      strs.of(q, path)
    case _:
      []

def pairs.of(p: S.Pat, +path: String) -> List<&2, String>:
  match p:
    case S.PPair{a, b}:
      path <> List.append(&2, String, pairs.of(a, path ++ "L"), pairs.of(b, path ++ "R"))
    case S.PAnn{q, t}:
      pairs.of(q, path)
    case _:
      []

def var.add(+k: String, +path: String, r: Map<&2, String> & Bool) -> Map<&2, String>:
  (m, has) = r
  match has:
    case True{}:
      m
    case False{}:
      Map.set(&2, String, m, k, path)

# Each pattern variable's path; the leftmost occurrence wins
# (findPatternVars).
def vars.of(p: S.Pat, +path: String, m: Map<&2, String>) -> Map<&2, String>:
  match p:
    case S.PPair{a, b}:
      vars.of(b, path ++ "R", vars.of(a, path ++ "L", m))
    case S.PVar{name}:
      +k = L.Name.text(name)
      var.add(k, path, Map.has(&2, String, m, k))
    case S.PAnn{q, t}:
      vars.of(q, path, m)
    case _:
      m

def at(path: String, +x: S.Surf) -> S.Surf:
  match path:
    case SCon{Chr{76}, rest}:
      at(rest, S.SLeft{S.loc(x), x})
    case SCon{c, rest}:
      at(rest, S.SRight{S.loc(x), x})
    case SNil{}:
      x

def ats(paths: List<&2, String>, +x: S.Surf) -> List<&2, S.Surf>:
  match paths:
    case Nil{}:
      []
    case Con{path, rest}:
      at(path, x) <> ats(rest, x)

# A pattern's literal skeleton as a term, variables and ignores as 0
# (patternToTerm).
def pattern.term(+anno: L.Loc, p: S.Pat) -> S.Surf:
  match p:
    case S.PPair{a, b}:
      S.SPair{anno, pattern.term(anno, a), pattern.term(anno, b)}
    case S.PInt{n}:
      S.SInt{anno, n}
    case S.PStr{t}:
      S.SStr{anno, t}
    case S.PAnn{q, t}:
      pattern.term(anno, q)
    case _:
      S.SInt{anno, 0}

# A helper's name, as the generated code refers to it (VarP).
def helper(+name: String) -> S.Surf:
  S.SVar{L.Gen{"LamBase Cofree instance"}, name}

# AppP: at the function's location.
def app(+f: S.Surf, x: S.Surf) -> S.Surf:
  S.SApp{S.loc(f), f, x}

def list.equal(a: S.Surf, b: S.Surf) -> S.Surf:
  app(app(helper("__case_listEqual"), a), b)

def pair.check.at(+a: L.Loc, p: S.Pat, +x: S.Surf) -> S.Surf:
  app(app(app(S.SVar{a, "__case_foldl"}, helper("__case_and")), S.SInt{a, 1}), S.SList{a, ats(pairs.of(p, ""), x)})

# pairStructureCheck: the value has a pair wherever the pattern does.
def pair.check(p: S.Pat, +x: S.Surf) -> S.Surf:
  pair.check.at(L.Gen{"pairStructureCheck"}, p, x)

def none(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      False{}

def matches.pick(noints: Bool, nostrs: Bool, +ra: L.Loc, ieq: S.Surf, seq: S.Surf, pc: S.Surf) -> S.Surf:
  match noints:
    case True{}:
      app(app(S.SVar{ra, "__case_and"}, seq), pc)
    case False{}:
      match nostrs:
        case True{}:
          app(app(S.SVar{ra, "__case_and"}, ieq), pc)
        case False{}:
          app(app(app(S.SVar{ra, "__case_foldl"}, helper("__case_and")), S.SInt{ra, 1}), S.SList{ra, [ieq, seq, pc]})

# Whether the value x matches pattern p: its number and string leaves are
# the pattern's, and it has the pattern's pairs (at the alternative's
# location ra; the leaf lists at the case's, anno).
def matches(+anno: L.Loc, +ra: L.Loc, +p: S.Pat, +x: S.Surf) -> S.Surf:
  +ns = ints.of(p, "")
  +ss = strs.of(p, "")
  matches.pick(none(ns), none(ss), ra,
    list.equal(S.SList{anno, ats(ns, x)}, S.SList{anno, ats(ns, pattern.term(anno, p))}),
    list.equal(S.SList{anno, ats(ss, x)}, S.SList{anno, ats(ss, pattern.term(anno, p))}),
    pair.check(p, x))

# The alternative's result with its pattern's variables bound, in name
# order, to the parts of x they name (mkCaseAlternative).
def alt.bound(ks: List<&2, Sigma<&2, &2, String, _ => String>>, +ra: L.Loc, +x: S.Surf, r: S.Surf) -> S.Surf:
  match ks:
    case Nil{}:
      r
    case Con{kv, rest}:
      match kv:
        case (k, path):
          S.SApp{ra, S.SLam{ra, L.Name{ra, k}, alt.bound(rest, ra, x, r)}, at(path, x)}

# The alternatives as nested ifs, the last else aborting
# (case2annidatedIfs).
def ifs(+anno: L.Loc, +x: S.Surf, alts: List<&2, S.Alt>) -> S.Surf:
  match alts:
    case Nil{}:
      +xa = S.loc(x)
      S.SIte{xa, S.SInt{xa, 1}, app(helper("__case_abort"), S.SStr{xa, "Non-exhaustive patterns in case"}), S.SInt{xa, 0}}
    case Con{alt, rest}:
      match alt:
        case S.Alt{+p, +r}:
          +ra = S.loc(r)
          S.SIte{ra, matches(anno, ra, p, x),
                 alt.bound(Map.to_list(&2, String, vars.of(p, "", Map.new(&2, String))), ra, x, r),
                 ifs(anno, x, rest)}

# Children first, every case lowered.
def lower(+fuel: Nat, n: ON) -> OV:
  match fuel:
    case 0n:
      VT{S.SZero{L.Unknown{}}}
    case 1n+f:
      match n:
        case OT{t}:
          match t:
            case S.SApp{a, x, y}:
              VT{S.SApp{a, vt(lower(f, OT{x})), vt(lower(f, OT{y}))}}
            case S.SLam{a, v, body}:
              VT{S.SLam{a, v, vt(lower(f, OT{body}))}}
            case S.SPair{a, x, y}:
              VT{S.SPair{a, vt(lower(f, OT{x})), vt(lower(f, OT{y}))}}
            case S.SCheck{a, x, y}:
              VT{S.SCheck{a, vt(lower(f, OT{x})), vt(lower(f, OT{y}))}}
            case S.SIte{a, x, y, z}:
              VT{S.SIte{a, vt(lower(f, OT{x})), vt(lower(f, OT{y})), vt(lower(f, OT{z}))}}
            case S.SLeft{a, x}:
              VT{S.SLeft{a, vt(lower(f, OT{x}))}}
            case S.SRight{a, x}:
              VT{S.SRight{a, vt(lower(f, OT{x}))}}
            case S.STrace{a, x}:
              VT{S.STrace{a, vt(lower(f, OT{x}))}}
            case S.SHash{a, x}:
              VT{S.SHash{a, vt(lower(f, OT{x}))}}
            case S.SRec{a, x, y, z}:
              VT{S.SRec{a, vt(lower(f, OT{x})), vt(lower(f, OT{y})), vt(lower(f, OT{z}))}}
            case S.SLet{a, binds, body}:
              VT{S.SLet{a, vbs(lower(f, OBs{binds})), vt(lower(f, OT{body}))}}
            case S.SList{a, xs}:
              VT{S.SList{a, vts(lower(f, OTs{xs}))}}
            case S.SCase{a, x, alts}:
              VT{ifs(a, vt(lower(f, OT{x})), vas(lower(f, OAs{alts})))}
            case other:
              VT{other}
        case OTs{xs}:
          match xs:
            case Nil{}:
              VTs{[]}
            case Con{x, rest}:
              VTs{vt(lower(f, OT{x})) <> vts(lower(f, OTs{rest}))}
        case OBs{bs}:
          match bs:
            case Nil{}:
              VBs{[]}
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  VBs{S.Bind{name, vt(lower(f, OT{val}))} <> vbs(lower(f, OBs{rest}))}
        case OAs{alts}:
          match alts:
            case Nil{}:
              VAs{[]}
            case Con{alt, rest}:
              match alt:
                case S.Alt{p, body}:
                  VAs{S.Alt{p, vt(lower(f, OT{body}))} <> vas(lower(f, OAs{rest}))}
        case OP{p}:
          VP{p}
        case OD{d}:
          VT{S.SZero{L.Unknown{}}}

def lower.cases(t: S.Surf) -> S.Surf:
  vt(lower(fuel(), OT{t}))

# desugarTerm.
def desugar(t: S.Surf) -> S.Surf:
  lower.cases(optimize.builtins(add.builtins(add.aliases(t))))
