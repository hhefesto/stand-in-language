import Base
import ./Loc.bend as L
import ./Syntax.bend as S

# Desugaring (haskell-final's Telomare.Desugar, desugarTerm): the builtins
# bound around the program, the case helpers aliased, and applications of
# builtins turned into primitives where the builtin is in scope. Lowering
# `case` to nested ifs is stage 7's (lowerCases); until then a case reaches
# the resolver as it is and is refused there.

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

# desugarTerm, less lowerCases (stage 7).
def desugar(t: S.Surf) -> S.Surf:
  optimize.builtins(add.builtins(add.aliases(t)))
