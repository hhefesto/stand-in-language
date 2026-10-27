import Base
import ./Loc.bend as L
import ./Syntax.bend as S

# Desugaring (Telomare.Desugar, desugarTerm): the builtins bound around the
# program, the case helpers aliased, applications of builtins turned into
# their direct forms where the builtin is in scope, and every `case`
# lowered to nested ifs over the case helpers.

# An argument of an application, with the location of the application node
# that supplies it.
type Arg is Data:
  Arg{+loc: L.Loc, +x: S.Expanded()}

# An application split into its head and its arguments, first applied
# first (applicationSpine).
type Spine is Data:
  Spine{+h: S.Expanded(), +args: List<&2, Arg>}

type ON is Data:
  OT{+t: S.Expanded()}
  OP{+p: S.ExpandedPat()}
  OTs{+xs: List<&2, S.Expanded()>}
  OBs{+bs: List<&2, S.ExpandedBind()>}
  OAs{+alts: List<&2, S.ExpandedAlt()>}
  OArgs{+args: List<&2, Arg>}
  OSpine{+sp: Spine}

type OV is Data:
  VT{+t: S.Expanded()}
  VP{+p: S.ExpandedPat()}
  VTs{+xs: List<&2, S.Expanded()>}
  VBs{+bs: List<&2, S.ExpandedBind()>}
  VAs{+alts: List<&2, S.ExpandedAlt()>}
  VArgs{+args: List<&2, Arg>}

def has(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

# The builtins
# ------------

def lam1(+name: String, body: S.Expanded()) -> S.Expanded():
  S.SLam{L.Builtin{name}, L.Name{L.Builtin{name}, "x"}, body}

def b.left(+l: L.Loc) -> S.Expanded():
  S.SLeft{l, S.SVar{l, "x"}}

def b.right(+l: L.Loc) -> S.Expanded():
  S.SRight{l, S.SVar{l, "x"}}

def lam2(+name: String, body: S.Expanded()) -> S.Expanded():
  S.SLam{L.Builtin{name}, L.Name{L.Builtin{name}, "x"},
    S.SLam{L.Builtin{name}, L.Name{L.Builtin{name}, "y"}, body}}

def builtin(+name: String, val: S.Expanded()) -> S.ExpandedBind():
  S.Bind{L.Name{L.Builtin{name}, name}, val}

# let zero = 0; left = \x -> left x; ... in t (addBuiltins). Haskell's
# `trace` is not a builtin here (HANDOFF P2).
def add.builtins(t: S.Expanded()) -> S.Expanded():
  S.SLet{L.Gen{"addBuiltins"},
    [builtin("zero", S.SInt{L.Builtin{"zero"}, 0}),
     builtin("left", lam1("left", b.left(L.Builtin{"left"}))),
     builtin("right", lam1("right", b.right(L.Builtin{"right"}))),
     builtin("pair", lam2("pair", S.SPair{L.Builtin{"pair"}, S.SVar{L.Builtin{"pair"}, "x"}, S.SVar{L.Builtin{"pair"}, "y"}})),
     builtin("app", lam2("app", S.SApp{L.Builtin{"app"}, S.SVar{L.Builtin{"app"}, "x"}, S.SVar{L.Builtin{"app"}, "y"}}))],
    t}

# Case helper aliases
# -------------------

def bound(bs: List<&2, S.ExpandedBind()>, acc: Set()) -> Set():
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          bound(rest, Set.add(acc, L.Name.text(name)))

def alias.if(yes: Bool, +loc: L.Loc, +name: String, alias: String, rest: List<&2, S.ExpandedBind()>) -> List<&2, S.ExpandedBind()>:
  match yes:
    case True{}:
      S.Bind{L.Name{L.GenIn{"case helper " ++ name, loc}, alias}, S.SVar{loc, name}} <> rest
    case False{}:
      rest

def aliases(+names: Set(), +loc: L.Loc) -> List<&2, S.ExpandedBind()>:
  alias.if(has(names, "and"), loc, "and", "__case_and",
    alias.if(has(names, "foldl"), loc, "foldl", "__case_foldl",
      alias.if(has(names, "dEqual"), loc, "dEqual", "__case_dEqual",
        alias.if(has(names, "listEqual"), loc, "listEqual", "__case_listEqual",
          alias.if(has(names, "abort"), loc, "abort", "__case_abort", [])))))

# __case_and = and, ... for the helpers the program binds, ahead of its own
# bindings (addCaseHelperAliases).
def add.aliases(t: S.Expanded()) -> S.Expanded():
  match t:
    case S.SLet{+loc, +binds, body}:
      S.SLet{loc, List.append(&2, S.ExpandedBind(), aliases(bound(binds, Set.new()), loc), binds), body}
    case other:
      other

# Builtin applications (optimizeBuiltinFunctions)
# -----------------------------------------------

def vt(v: OV) -> S.Expanded():
  match v:
    case VT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def vp(v: OV) -> S.ExpandedPat():
  match v:
    case VP{p}:
      p
    case _:
      S.PIgnore{}

def vts(v: OV) -> List<&2, S.Expanded()>:
  match v:
    case VTs{xs}:
      xs
    case _:
      []

def vbs(v: OV) -> List<&2, S.ExpandedBind()>:
  match v:
    case VBs{bs}:
      bs
    case _:
      []

def vas(v: OV) -> List<&2, S.ExpandedAlt()>:
  match v:
    case VAs{alts}:
      alts
    case _:
      []

def vargs(v: OV) -> List<&2, Arg>:
  match v:
    case VArgs{args}:
      args
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
def update.binds(bs: List<&2, S.ExpandedBind()>, +scope: Set()) -> Set():
  match bs:
    case Nil{}:
      scope
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          update(update.binds(rest, scope), name)

def update.pat(p: S.ExpandedPat(), +scope: Set()) -> Set():
  match p:
    case S.PVar{name}:
      update(scope, name)
    case S.PAnn{q, t}:
      update.pat(q, scope)
    case S.PPair{a, b}:
      update.pat(a, update.pat(b, scope))
    case _:
      scope

# The spine of t, its arguments ahead of acc.
def spine(t: S.Expanded(), acc: List<&2, Arg>) -> Spine:
  match t:
    case S.SApp{a, f, x}:
      spine(f, Arg{a, x} <> acc)
    case other:
      Spine{other, acc}

# The application again, the arguments applied in order.
def rebuild(args: List<&2, Arg>, h: S.Expanded()) -> S.Expanded():
  match args:
    case Nil{}:
      h
    case Con{arg, rest}:
      match arg:
        case Arg{a, x}:
          rebuild(rest, S.SApp{a, h, x})

# A one-argument builtin's direct form, at the location of the application
# that supplies its argument.
def unary(+name: String, +a: L.Loc, x: S.Expanded()) -> S.Expanded():
  match name:
    case "left":
      S.SLeft{a, x}
    case _:
      S.SRight{a, x}

def binary(+name: String, +a: L.Loc, x: S.Expanded(), y: S.Expanded()) -> S.Expanded():
  match name:
    case "pair":
      S.SPair{a, x, y}
    case _:
      S.SApp{a, x, y}

def is.unary(name: String) -> Bool:
  match name:
    case "left":
      True{}
    case "right":
      True{}
    case _:
      False{}

def is.binary(name: String) -> Bool:
  match name:
    case "pair":
      True{}
    case "app":
      True{}
    case _:
      False{}

def unary.applied(+name: String, args: List<&2, Arg>) -> Maybe<&2, Spine>:
  match args:
    case Nil{}:
      None{}
    case Con{arg, rest}:
      match arg:
        case Arg{+a, x}:
          Some{spine(unary(name, a, x), rest)}

# A binary builtin short its second argument awaits it:
# `\__builtin_arg -> pair x __builtin_arg`.
def binary.second(+name: String, +a: L.Loc, x: S.Expanded(), rest: List<&2, Arg>) -> Maybe<&2, Spine>:
  match rest:
    case Nil{}:
      Some{Spine{S.SLam{a, L.Name{a, "__builtin_arg"}, binary(name, a, x, S.SVar{a, "__builtin_arg"})}, []}}
    case Con{arg, more}:
      match arg:
        case Arg{+b, y}:
          Some{spine(binary(name, b, x, y), more)}

def binary.applied(+name: String, args: List<&2, Arg>) -> Maybe<&2, Spine>:
  match args:
    case Nil{}:
      None{}
    case Con{arg, rest}:
      match arg:
        case Arg{+a, x}:
          binary.second(name, a, x, rest)

def builtin.arity(un: Bool, bin: Bool, +name: String, args: List<&2, Arg>) -> Maybe<&2, Spine>:
  match un:
    case True{}:
      unary.applied(name, args)
    case False{}:
      match bin:
        case True{}:
          binary.applied(name, args)
        case False{}:
          None{}

def builtin.in.scope(yes: Bool, +name: String, args: List<&2, Arg>) -> Maybe<&2, Spine>:
  match yes:
    case True{}:
      builtin.arity(is.unary(name), is.binary(name), name, args)
    case False{}:
      None{}

# The spine with an in-scope builtin at its head applied to its arguments
# (applyBuiltin): the direct form's own spine, then the arguments left
# over. None when the head is no builtin, or it has no arguments.
def direct(+scope: Set(), sp: Spine) -> Maybe<&2, Spine>:
  match sp:
    case Spine{h, args}:
      match h:
        case S.SVar{a, +name}:
          builtin.in.scope(has(scope, name), name, args)
        case _:
          None{}

# Rewrite builtin applications at the head until none is left (rewrite);
# the direct form of `app` is an application, so its spine goes round
# again.
def rewrite(+fuel: Nat, +scope: Set(), d: Maybe<&2, Spine>, sp: Spine) -> S.Expanded():
  match fuel:
    case 0n:
      match sp:
        case Spine{h, args}:
          rebuild(args, h)
    case 1n+f:
      match d:
        case None{}:
          match sp:
            case Spine{h, args}:
              rebuild(args, h)
        case Some{+next}:
          rewrite(f, scope, direct(scope, next), next)

def go(+fuel: Nat, +scope: Set(), n: ON) -> OV:
  match fuel:
    case 0n:
      VT{S.SZero{L.Unknown{}}}
    case 1n+f:
      match n:
        case OT{t}:
          match t:
            case S.SApp{anno, a, y}:
              go(f, scope, OSpine{spine(a, [Arg{anno, y}])})
            case S.SLam{anno, v, body}:
              VT{S.SLam{anno, v, vt(go(f, Set.del(scope, L.Name.text(v)), OT{body}))}}
            case S.SPair{anno, a, b}:
              VT{S.SPair{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b}))}}
            case S.SCheck{anno, a, b}:
              VT{S.SCheck{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b}))}}
            case S.SIte{anno, a, b, c}:
              VT{S.SIte{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b})), vt(go(f, scope, OT{c}))}}
            case S.SLeft{anno, x}:
              VT{S.SLeft{anno, vt(go(f, scope, OT{x}))}}
            case S.SRight{anno, x}:
              VT{S.SRight{anno, vt(go(f, scope, OT{x}))}}
            case S.SHash{anno, x}:
              VT{S.SHash{anno, vt(go(f, scope, OT{x}))}}
            case S.SRec{anno, a, b, c}:
              VT{S.SRec{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b})), vt(go(f, scope, OT{c}))}}
            case S.SLet{anno, +binds, body}:
              +inner = update.binds(binds, scope)
              VT{S.SLet{anno, vbs(go(f, inner, OBs{binds})), vt(go(f, inner, OT{body}))}}
            case S.SList{anno, xs}:
              VT{S.SList{anno, vts(go(f, scope, OTs{xs}))}}
            case S.SCase{anno, scrut, alts, w}:
              VT{S.SCase{anno, vt(go(f, scope, OT{scrut})), vas(go(f, scope, OAs{alts})), w}}
            case other:
              VT{other}
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
        case OSpine{sp}:
          match sp:
            case Spine{h, args}:
              +walked = {Spine{vt(go(f, scope, OT{h})), vargs(go(f, scope, OArgs{args}))} : Spine}
              VT{rewrite(fuel, scope, direct(scope, walked), walked)}
        case OArgs{args}:
          match args:
            case Nil{}:
              VArgs{[]}
            case Con{arg, rest}:
              match arg:
                case Arg{a, x}:
                  VArgs{Arg{a, vt(go(f, scope, OT{x}))} <> vargs(go(f, scope, OArgs{rest}))}

def builtin.names() -> Set():
  Set.from_list(["left", "right", "pair", "app"])

def fuel() -> Nat:
  U32.to_nat(4294967295)

def optimize.builtins(t: S.Expanded()) -> S.Expanded():
  vt(go(fuel(), builtin.names(), OT{t}))

# Case lowering (lowerCases)
# --------------------------

# The parts of a pattern case lowering inspects (PatternNode), each with
# the path to it from the root, the projections first taken first ("RL"
# is Left (Right x)).
type Node is Data:
  NPair{+path: String}
  NInt{+path: String, +n: U32}
  NStr{+path: String, +s: String}
  NVar{+path: String, +name: L.Name}

# Every pair, literal and variable of a pattern, in left-to-right preorder,
# ahead of rest (patternNodes).
def nodes.of(p: S.ExpandedPat(), +path: String, rest: List<&2, Node>) -> List<&2, Node>:
  match p:
    case S.PPair{a, b}:
      NPair{path} <> nodes.of(a, path ++ "L", nodes.of(b, path ++ "R", rest))
    case S.PInt{n}:
      NInt{path, n} <> rest
    case S.PStr{t}:
      NStr{path, t} <> rest
    case S.PVar{name}:
      NVar{path, name} <> rest
    case S.PIgnore{}:
      rest
    case S.PAnn{q, t}:
      nodes.of(q, path, rest)

def at(path: String, +x: S.Desugared()) -> S.Desugared():
  match path:
    case SCon{Chr{76}, rest}:
      at(rest, S.SLeft{S.loc(Empty, Empty, Empty, x), x})
    case SCon{c, rest}:
      at(rest, S.SRight{S.loc(Empty, Empty, Empty, x), x})
    case SNil{}:
      x

# A pattern's literal skeleton as a term, variables and ignores as 0
# (patternToTerm).
def pattern.term(+anno: L.Loc, p: S.ExpandedPat()) -> S.Desugared():
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
def helper(+name: String) -> S.Desugared():
  S.SVar{L.Gen{"LamBase Cofree instance"}, name}

# AppP: at the function's location.
def app(+f: S.Desugared(), x: S.Desugared()) -> S.Desugared():
  S.SApp{S.loc(Empty, Empty, Empty, f), f, x}

def equal(+name: String, a: S.Desugared(), b: S.Desugared()) -> S.Desugared():
  app(app(helper(name), a), b)

# Bool-valued checks that x has the pattern's pairs and literals
# (matchChecks): a pair node, any value, is made a Bool before it reaches
# `and`, whose arguments are refined to Bool; numbers are compared with
# dEqual, strings whole with listEqual.
def checks(+anno: L.Loc, +x: S.Desugared(), ns: List<&2, Node>) -> List<&2, S.Desugared()>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      match n:
        case NPair{path}:
          S.SIte{S.loc(Empty, Empty, Empty, x), at(path, x), S.SInt{anno, 1}, S.SInt{anno, 0}} <> checks(anno, x, rest)
        case NInt{path, k}:
          equal("__case_dEqual", at(path, x), S.SInt{anno, k}) <> checks(anno, x, rest)
        case NStr{path, t}:
          equal("__case_listEqual", at(path, x), S.SStr{anno, t}) <> checks(anno, x, rest)
        case NVar{path, name}:
          checks(anno, x, rest)

# The conjunction of non-empty checks (allOf).
def all.of(+anno: L.Loc, cs: List<&2, S.Desugared()>) -> S.Desugared():
  match cs:
    case Nil{}:
      S.SInt{anno, 1}
    case Con{a, more}:
      match more:
        case Nil{}:
          a
        case Con{b, rest}:
          match rest:
            case Nil{}:
              app(app(S.SVar{anno, "__case_and"}, a), b)
            case Con{c, tail}:
              app(app(app(S.SVar{anno, "__case_foldl"}, helper("__case_and")), S.SInt{anno, 1}),
                  S.SList{anno, a <> b <> c <> tail})

def var.keep(dup: Bool, +path: String, +name: L.Name, rest: List<&2, Node>) -> List<&2, Node>:
  match dup:
    case True{}:
      rest
    case False{}:
      NVar{path, name} <> rest

# The pattern's variables, in preorder, each once: the leftmost occurrence
# of a repeated name wins.
def vars(ns: List<&2, Node>, +seen: Set()) -> List<&2, Node>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      match n:
        case NVar{+path, +name}:
          var.keep(has(seen, L.Name.text(name)), path, name, vars(rest, Set.add(seen, L.Name.text(name))))
        case _:
          vars(rest, seen)

# AppP (LamP name body) value: both at the body's location.
def bind.one(name: L.Name, value: S.Desugared(), +body: S.Desugared()) -> S.Desugared():
  S.SApp{S.loc(Empty, Empty, Empty, body), S.SLam{S.loc(Empty, Empty, Empty, body), name, body}, value}

# The variables bound in r, each to its part of x, the first outermost
# (bindPatternVars).
def binds(vs: List<&2, Node>, +x: S.Desugared(), r: S.Desugared()) -> S.Desugared():
  match vs:
    case Nil{}:
      r
    case Con{v, rest}:
      match v:
        case NVar{path, name}:
          bind.one(name, at(path, x), binds(rest, x, r))
        case _:
          binds(rest, x, r)

# ITEP: at the condition's location.
def ite(+i: S.Desugared(), t: S.Desugared(), e: S.Desugared()) -> S.Desugared():
  S.SIte{S.loc(Empty, Empty, Empty, i), i, t, e}

# An alternative with no checks always matches, so the ones after it are
# dropped.
def alternative(+ra: L.Loc, cs: List<&2, S.Desugared()>, bound: S.Desugared(), next: S.Desugared()) -> S.Desugared():
  match cs:
    case Nil{}:
      bound
    case Con{c, more}:
      ite(all.of(ra, c <> more), bound, next)

# A case alternative lowered: its pattern (read for its shape only) and its
# lowered result.
type Arm is Data:
  Arm{+p: S.ExpandedPat(), +body: S.Desugared()}

# What lowering gives back: no case can be written in it.
type LV is Data:
  DT{+t: S.Desugared()}
  DTs{+xs: List<&2, S.Desugared()>}
  DBs{+bs: List<&2, S.DesugaredBind()>}
  DArms{+arms: List<&2, Arm>}

def dt(v: LV) -> S.Desugared():
  match v:
    case DT{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def dts(v: LV) -> List<&2, S.Desugared()>:
  match v:
    case DTs{xs}:
      xs
    case _:
      []

def dbs(v: LV) -> List<&2, S.DesugaredBind()>:
  match v:
    case DBs{bs}:
      bs
    case _:
      []

def darms(v: LV) -> List<&2, Arm>:
  match v:
    case DArms{arms}:
      arms
    case _:
      []

# The alternatives as nested ifs over x, tried in order, the last else
# aborting (caseToNestedIfs); anno is the scrutinee's location.
def ifs(+anno: L.Loc, +x: S.Desugared(), alts: List<&2, Arm>) -> S.Desugared():
  match alts:
    case Nil{}:
      S.SIte{anno, S.SInt{anno, 1}, app(helper("__case_abort"), S.SStr{anno, "Non-exhaustive patterns in case"}), S.SInt{anno, 0}}
    case Con{alt, rest}:
      match alt:
        case Arm{p, +r}:
          +ns = nodes.of(p, "", [])
          alternative(S.loc(Empty, Empty, Empty, r), checks(S.loc(Empty, Empty, Empty, r), x, ns),
                      binds(vars(ns, Set.new()), x, r), ifs(anno, x, rest))

# A scrutinee that is not a variable is bound once, to a name source code
# cannot write, so the checks and bindings refer to it instead of copying
# it.
def case.bind(+anno: L.Loc, scrut: S.Desugared(), arms: List<&2, Arm>) -> S.Desugared():
  +g = {L.GenIn{"case scrutinee", anno} : L.Loc}
  +body = ifs(anno, S.SVar{g, "__case_scrutinee"}, arms)
  S.SApp{S.loc(Empty, Empty, Empty, body), S.SLam{S.loc(Empty, Empty, Empty, body), L.Name{g, "__case_scrutinee"}, body}, scrut}

def case.ifs(+scrut: S.Desugared(), arms: List<&2, Arm>) -> S.Desugared():
  match scrut:
    case S.SVar{+a, +name}:
      ifs(a, S.SVar{a, name}, arms)
    case _:
      case.bind(S.loc(Empty, Empty, Empty, scrut), scrut, arms)

# Children first, every case lowered.
def lower(+fuel: Nat, n: ON) -> LV:
  match fuel:
    case 0n:
      DT{S.SZero{L.Unknown{}}}
    case 1n+f:
      match n:
        case OT{t}:
          match t:
            case S.SApp{a, x, y}:
              DT{S.SApp{a, dt(lower(f, OT{x})), dt(lower(f, OT{y}))}}
            case S.SLam{a, v, body}:
              DT{S.SLam{a, v, dt(lower(f, OT{body}))}}
            case S.SPair{a, x, y}:
              DT{S.SPair{a, dt(lower(f, OT{x})), dt(lower(f, OT{y}))}}
            case S.SCheck{a, x, y}:
              DT{S.SCheck{a, dt(lower(f, OT{x})), dt(lower(f, OT{y}))}}
            case S.SIte{a, x, y, z}:
              DT{S.SIte{a, dt(lower(f, OT{x})), dt(lower(f, OT{y})), dt(lower(f, OT{z}))}}
            case S.SLeft{a, x}:
              DT{S.SLeft{a, dt(lower(f, OT{x}))}}
            case S.SRight{a, x}:
              DT{S.SRight{a, dt(lower(f, OT{x}))}}
            case S.SHash{a, x}:
              DT{S.SHash{a, dt(lower(f, OT{x}))}}
            case S.SRec{a, x, y, z}:
              DT{S.SRec{a, dt(lower(f, OT{x})), dt(lower(f, OT{y})), dt(lower(f, OT{z}))}}
            case S.SLet{a, binds, body}:
              DT{S.SLet{a, dbs(lower(f, OBs{binds})), dt(lower(f, OT{body}))}}
            case S.SList{a, xs}:
              DT{S.SList{a, dts(lower(f, OTs{xs}))}}
            case S.SCase{a, x, alts, w}:
              DT{case.ifs(dt(lower(f, OT{x})), darms(lower(f, OAs{alts})))}
            case S.SVar{a, name}:
              DT{S.SVar{a, name}}
            case S.SZero{a}:
              DT{S.SZero{a}}
            case S.SChurch{a, k}:
              DT{S.SChurch{a, k}}
            case S.SInt{a, k}:
              DT{S.SInt{a, k}}
            case S.SStr{a, str}:
              DT{S.SStr{a, str}}
            case S.SLamPat{a, ps, body, w}:
              Empty.absurd(LV, w)
            case S.SLetSugar{a, ds, body, w}:
              Empty.absurd(LV, w)
            case S.SLamN{a, k, v, body, w}:
              Empty.absurd(LV, w)
        case OTs{xs}:
          match xs:
            case Nil{}:
              DTs{[]}
            case Con{x, rest}:
              DTs{dt(lower(f, OT{x})) <> dts(lower(f, OTs{rest}))}
        case OBs{bs}:
          match bs:
            case Nil{}:
              DBs{[]}
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  DBs{S.Bind{name, dt(lower(f, OT{val}))} <> dbs(lower(f, OBs{rest}))}
        case OAs{alts}:
          match alts:
            case Nil{}:
              DArms{[]}
            case Con{alt, rest}:
              match alt:
                case S.Alt{p, body}:
                  DArms{Arm{p, dt(lower(f, OT{body}))} <> darms(lower(f, OAs{rest}))}
        case OP{p}:
          DT{S.SZero{L.Unknown{}}}
        case OArgs{args}:
          DT{S.SZero{L.Unknown{}}}
        case OSpine{sp}:
          DT{S.SZero{L.Unknown{}}}

def lower.cases(t: S.Expanded()) -> S.Desugared():
  dt(lower(fuel(), OT{t}))

# desugarTerm: what the program is resolved to, with no case left in it.
def desugar(t: S.Expanded()) -> S.Desugared():
  lower.cases(optimize.builtins(add.builtins(add.aliases(t))))
