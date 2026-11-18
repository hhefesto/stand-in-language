import Base
import ./Loc.bend as L
import ./Syntax.bend as S

# Desugaring (Telomare.Desugar, desugarTerm): the builtins and the case
# helpers bound around the program, applications of builtins turned into
# their direct forms where the builtin is in scope, and every `case`
# lowered to nested ifs, its literals compared by the case helpers.

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

# The case helpers (caseHelpers): exact equality with a literal, for case
# matching. Each takes the literal first and recurses on it alone. An
# integer n is encoded as n - 1 paired with zero, so its helper walks the
# left spine of both terms and requires every right of the other to be
# zero; a string is a zero-terminated list of character codes, compared
# code by code.

# 1 when t is 0, else 0 (isZero).
def h.zero(+loc: L.Loc, t: S.Expanded()) -> S.Expanded():
  S.SIte{loc, t, S.SInt{loc, 0}, S.SInt{loc, 1}}

def h.p(+loc: L.Loc) -> S.Expanded():
  S.SVar{loc, "p"}

# Whether the heads match, the literal and the other term paired as p.
def h.head(int: Bool, +loc: L.Loc) -> S.Expanded():
  match int:
    case True{}:
      h.zero(loc, S.SRight{loc, S.SRight{loc, h.p(loc)}})
    case False{}:
      S.SApp{loc, S.SApp{loc, S.SVar{loc, "__case_intEqual"}, S.SLeft{loc, S.SLeft{loc, h.p(loc)}}}, S.SLeft{loc, S.SRight{loc, h.p(loc)}}}

# The next part of t: an integer's left, a string's right.
def h.next(int: Bool, +loc: L.Loc, t: S.Expanded()) -> S.Expanded():
  match int:
    case True{}:
      S.SLeft{loc, t}
    case False{}:
      S.SRight{loc, t}

# While the literal is a pair, the other must be one whose head matches,
# and the walk goes on with the next parts of both; once the literal is
# zero, so must the other be (walkLiteral).
def walk.literal(+name: String, +int: Bool) -> S.Expanded():
  +loc = {L.Gen{"case helper " ++ name} : L.Loc}
  +test: S.Expanded() = S.SLam{loc, L.Name{loc, "p"}, S.SLeft{loc, h.p(loc)}}
  +step: S.Expanded() = S.SLam{loc, L.Name{loc, "recur"}, S.SLam{loc, L.Name{loc, "p"},
    S.SIte{loc, S.SRight{loc, h.p(loc)},
      S.SIte{loc, h.head(int, loc),
        S.SApp{loc, S.SVar{loc, "recur"}, S.SPair{loc, h.next(int, loc, S.SLeft{loc, h.p(loc)}), h.next(int, loc, S.SRight{loc, h.p(loc)})}},
        S.SInt{loc, 0}},
      S.SInt{loc, 0}}}}
  +base: S.Expanded() = S.SLam{loc, L.Name{loc, "p"}, h.zero(loc, S.SRight{loc, h.p(loc)})}
  S.SLam{loc, L.Name{loc, "literal"}, S.SLam{loc, L.Name{loc, "term"},
    S.SApp{loc, S.SRec{loc, test, step, base}, S.SPair{loc, S.SVar{loc, "literal"}, S.SVar{loc, "term"}}}}}

def helper(+name: String, +int: Bool) -> S.ExpandedBind():
  S.Bind{L.Name{L.Gen{"case helper"}, name}, walk.literal(name, int)}

# let zero = 0; left = \x -> left x; ...; __case_intEqual = ... in t
# (addBuiltins). `trace` is the identity: master resolves its direct form
# to its argument.
def add.builtins(t: S.Expanded()) -> S.Expanded():
  S.SLet{L.Gen{"addBuiltins"},
    [builtin("zero", S.SInt{L.Builtin{"zero"}, 0}),
     builtin("left", lam1("left", b.left(L.Builtin{"left"}))),
     builtin("right", lam1("right", b.right(L.Builtin{"right"}))),
     builtin("trace", lam1("trace", S.SVar{L.Builtin{"trace"}, "x"})),
     builtin("abort", lam1("abort", S.abort.term(Empty, Unit, Empty, L.KUser{}, L.Builtin{"abort"}, S.SVar{L.Builtin{"abort"}, "x"}))),
     builtin("pair", lam2("pair", S.SPair{L.Builtin{"pair"}, S.SVar{L.Builtin{"pair"}, "x"}, S.SVar{L.Builtin{"pair"}, "y"}})),
     builtin("app", lam2("app", S.SApp{L.Builtin{"app"}, S.SVar{L.Builtin{"app"}, "x"}, S.SVar{L.Builtin{"app"}, "y"}})),
     helper("__case_intEqual", True{}),
     helper("__case_stringEqual", False{})],
    t}

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
    case "trace":
      x
    case "abort":
      S.abort.term(Empty, Unit, Empty, L.KUser{}, a, x)
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
    case "trace":
      True{}
    case "abort":
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
            case S.SCheck{anno, k, a, b}:
              VT{S.SCheck{anno, k, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b}))}}
            case S.SIte{anno, a, b, c}:
              VT{S.SIte{anno, vt(go(f, scope, OT{a})), vt(go(f, scope, OT{b})), vt(go(f, scope, OT{c}))}}
            case S.SLeft{anno, x}:
              VT{S.SLeft{anno, vt(go(f, scope, OT{x}))}}
            case S.SRight{anno, x}:
              VT{S.SRight{anno, vt(go(f, scope, OT{x}))}}
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
  Set.from_list(["left", "right", "trace", "abort", "pair", "app"])

def fuel() -> Nat:
  U32.to_nat(4294967295)

def optimize.builtins(t: S.Expanded()) -> S.Expanded():
  vt(go(fuel(), builtin.names(), OT{t}))

# Case lowering (lowerCases)
# --------------------------

# A step on the way from a case's scrutinee to a part of it: a projection,
# or a refinement check of the part reached.
type Step is Data:
  StL{}
  StR{}
  StCheck{+g: S.Desugared()}

# The parts of a pattern that bind or test beyond its structure
# (PatternNode), each with the path to it from the root, the last step
# first.
type Node is Data:
  NVar{+path: List<&2, Step>, +name: L.Name}
  NGuard{+path: List<&2, Step>, +g: S.Desugared()}

# Every variable and guard of a pattern, in left-to-right preorder, ahead
# of rest (patternNodes). A guard comes after the nodes of the pattern it
# annotates, and the path to a variable under a guard passes through a
# refinement check of it: the match has tested the guard, so the check
# cannot fail, but it lets sizing bound the variable as a let refinement
# would. vpath leads to the variables, gpath (projections only) to the
# guards.
def nodes.of(p: S.DesugaredPat(), +vpath: List<&2, Step>, +gpath: List<&2, Step>, rest: List<&2, Node>) -> List<&2, Node>:
  match p:
    case S.PPair{a, b}:
      nodes.of(a, StL{} <> vpath, StL{} <> gpath, nodes.of(b, StR{} <> vpath, StR{} <> gpath, rest))
    case S.PVar{name}:
      NVar{vpath, name} <> rest
    case S.PAnn{q, +g}:
      nodes.of(q, StCheck{g} <> vpath, gpath, NGuard{gpath, g} <> rest)
    case _:
      rest

# A step taken from y: a projection at y's location (HLeft, HRight), or a
# check of y there (refined).
def step.at(s: Step, +y: S.Desugared()) -> S.Desugared():
  match s:
    case StL{}:
      S.SLeft{S.loc(Empty, Empty, Empty, y), y}
    case StR{}:
      S.SRight{S.loc(Empty, Empty, Empty, y), y}
    case StCheck{g}:
      S.SCheck{S.loc(Empty, Empty, Empty, y), L.KRefine{}, g, y}

def at(path: List<&2, Step>, +x: S.Desugared()) -> S.Desugared():
  match path:
    case Nil{}:
      x
    case Con{s, rest}:
      step.at(s, at(rest, x))

# A pattern's literal skeleton as a term, variables and ignores as 0
# (patternToTerm).
def pattern.term(+anno: L.Loc, p: S.DesugaredPat()) -> S.Desugared():
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

# 1 when t is 0, else 0 (isZero).
def is.zero(+anno: L.Loc, t: S.Desugared()) -> S.Desugared():
  S.SIte{anno, t, S.SInt{anno, 0}, S.SInt{anno, 1}}

# Exact equality of t with a literal: its helper applied to the literal,
# then to t. Zero and the empty string are both encoded as 0.
def literal.check(zero: Bool, +anno: L.Loc, +helper: String, lit: S.Desugared(), t: S.Desugared()) -> S.Desugared():
  match zero:
    case True{}:
      is.zero(anno, t)
    case False{}:
      S.SApp{anno, S.SApp{anno, S.SVar{anno, helper}, lit}, t}

# The conjunction of non-empty checks, nonzero exactly when all of them
# are: each check guards the rest (allOf).
def all.of(+anno: L.Loc, cs: List<&2, S.Desugared()>) -> S.Desugared():
  match cs:
    case Nil{}:
      S.SInt{anno, 1}
    case Con{c, more}:
      match more:
        case Nil{}:
          c
        case Con{d, rest}:
          S.SIte{anno, c, all.of(anno, d <> rest), S.SInt{anno, 0}}

def some.cons(m: Maybe<&2, S.Desugared()>, rest: List<&2, S.Desugared()>) -> List<&2, S.Desugared()>:
  match m:
    case Some{x}:
      x <> rest
    case None{}:
      rest

# A pair whose parts have no structure to test is t itself; else t, then
# its parts.
def pair.check(+anno: L.Loc, +t: S.Desugared(), parts: List<&2, S.Desugared()>) -> S.Desugared():
  match parts:
    case Nil{}:
      t
    case Con{c, more}:
      S.SIte{anno, t, all.of(anno, c <> more), S.SInt{anno, 0}}

# A check, nonzero when it passes, that t has the pattern's structure, or
# None when any term does (shapeCheck over patternShape). A pair is tested
# before its parts, which are tested left to right. The literal goes first
# to a helper: the helpers recurse on their first argument, and the
# scrutinee may be unbounded input.
def shape.check(p: S.DesugaredPat(), +anno: L.Loc, +t: S.Desugared()) -> Maybe<&2, S.Desugared()>:
  match p:
    case S.PPair{a, b}:
      Some{pair.check(anno, t, some.cons(shape.check(a, anno, S.SLeft{anno, t}), some.cons(shape.check(b, anno, S.SRight{anno, t}), [])))}
    case S.PInt{+n}:
      Some{literal.check(U32.is_eq(n, 0), anno, "__case_intEqual", S.SInt{anno, n}, t)}
    case S.PStr{+s}:
      Some{literal.check(String.eq(s, ""), anno, "__case_stringEqual", S.SStr{anno, s}, t)}
    case S.PAnn{q, g}:
      shape.check(q, anno, t)
    case _:
      None{}

# The guards, each applied to its part of x.
def guards(+anno: L.Loc, +x: S.Desugared(), ns: List<&2, Node>) -> List<&2, S.Desugared()>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      match n:
        case NGuard{path, g}:
          S.SApp{anno, g, at(path, x)} <> guards(anno, x, rest)
        case NVar{path, name}:
          guards(anno, x, rest)

# Checks, each nonzero when it passes, that x has the pattern's structure
# and then that its guards hold (matchChecks): structure first, so a guard
# only sees a term the rest of the pattern matches.
def checks(+anno: L.Loc, +x: S.Desugared(), p: S.DesugaredPat(), ns: List<&2, Node>) -> List<&2, S.Desugared()>:
  some.cons(shape.check(p, anno, x), guards(anno, x, ns))

def var.keep(dup: Bool, +path: List<&2, Step>, +name: L.Name, rest: List<&2, Node>) -> List<&2, Node>:
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

# An alternative with no checks always matches, so the ones after it are
# dropped.
def alternative(+ra: L.Loc, cs: List<&2, S.Desugared()>, bound: S.Desugared(), next: S.Desugared()) -> S.Desugared():
  match cs:
    case Nil{}:
      bound
    case Con{c, more}:
      S.SIte{ra, all.of(ra, c <> more), bound, next}

# A case alternative lowered: its pattern, its guards lowered, and its
# lowered result.
type Arm is Data:
  Arm{+p: S.DesugaredPat(), +body: S.Desugared()}

# What lowering gives back: no case can be written in it.
type LV is Data:
  DT{+t: S.Desugared()}
  DTs{+xs: List<&2, S.Desugared()>}
  DBs{+bs: List<&2, S.DesugaredBind()>}
  DArms{+arms: List<&2, Arm>}
  DP{+p: S.DesugaredPat()}

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

def dp(v: LV) -> S.DesugaredPat():
  match v:
    case DP{p}:
      p
    case _:
      S.PIgnore{}

def darms(v: LV) -> List<&2, Arm>:
  match v:
    case DArms{arms}:
      arms
    case _:
      []

# The alternatives as nested ifs over x, tried in order, the last else
# aborting (caseToNestedIfs); cloc is the case's location. Matching depends
# on no definition from source: literals are compared by the case helpers
# add.builtins binds.
def ifs(+cloc: L.Loc, +x: S.Desugared(), alts: List<&2, Arm>) -> S.Desugared():
  match alts:
    case Nil{}:
      S.SIte{cloc, S.SInt{cloc, 1}, S.abort.term(Empty, Empty, Empty, L.KCase{}, cloc, S.SStr{cloc, "Non-exhaustive patterns in case"}), S.SInt{cloc, 0}}
    case Con{alt, rest}:
      match alt:
        case Arm{+p, +r}:
          +ns = nodes.of(p, [], [], [])
          alternative(S.loc(Empty, Empty, Empty, r), checks(S.loc(Empty, Empty, Empty, r), x, p, ns),
                      binds(vars(ns, Set.new()), x, r), ifs(cloc, x, rest))

# A scrutinee that is not a variable is bound once, to a name source code
# cannot write, so the checks and bindings refer to it instead of copying
# it; anno is the scrutinee's location.
def case.bind(+cloc: L.Loc, +anno: L.Loc, scrut: S.Desugared(), arms: List<&2, Arm>) -> S.Desugared():
  +g = {L.GenIn{"case scrutinee", anno} : L.Loc}
  S.SApp{g, S.SLam{g, L.Name{g, "__case_scrutinee"}, ifs(cloc, S.SVar{g, "__case_scrutinee"}, arms)}, scrut}

def case.ifs(+cloc: L.Loc, +scrut: S.Desugared(), arms: List<&2, Arm>) -> S.Desugared():
  match scrut:
    case S.SVar{+a, +name}:
      ifs(cloc, S.SVar{a, name}, arms)
    case _:
      case.bind(cloc, S.loc(Empty, Empty, Empty, scrut), scrut, arms)

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
            case S.SCheck{a, k, x, y}:
              DT{S.SCheck{a, k, dt(lower(f, OT{x})), dt(lower(f, OT{y}))}}
            case S.SIte{a, x, y, z}:
              DT{S.SIte{a, dt(lower(f, OT{x})), dt(lower(f, OT{y})), dt(lower(f, OT{z}))}}
            case S.SLeft{a, x}:
              DT{S.SLeft{a, dt(lower(f, OT{x}))}}
            case S.SRight{a, x}:
              DT{S.SRight{a, dt(lower(f, OT{x}))}}
            case S.SRec{a, x, y, z}:
              DT{S.SRec{a, dt(lower(f, OT{x})), dt(lower(f, OT{y})), dt(lower(f, OT{z}))}}
            case S.SLet{a, binds, body}:
              DT{S.SLet{a, dbs(lower(f, OBs{binds})), dt(lower(f, OT{body}))}}
            case S.SList{a, xs}:
              DT{S.SList{a, dts(lower(f, OTs{xs}))}}
            case S.SCase{+a, x, alts, w}:
              DT{case.ifs(a, dt(lower(f, OT{x})), darms(lower(f, OAs{alts})))}
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
                  DArms{Arm{dp(lower(f, OP{p})), dt(lower(f, OT{body}))} <> darms(lower(f, OAs{rest}))}
        case OP{p}:
          match p:
            case S.PAnn{q, t}:
              DP{S.PAnn{dp(lower(f, OP{q})), dt(lower(f, OT{t}))}}
            case S.PPair{a, b}:
              DP{S.PPair{dp(lower(f, OP{a})), dp(lower(f, OP{b}))}}
            case S.PVar{name}:
              DP{S.PVar{name}}
            case S.PInt{n}:
              DP{S.PInt{n}}
            case S.PStr{t}:
              DP{S.PStr{t}}
            case S.PIgnore{}:
              DP{S.PIgnore{}}
        case OArgs{args}:
          DT{S.SZero{L.Unknown{}}}
        case OSpine{sp}:
          DT{S.SZero{L.Unknown{}}}

def lower.cases(t: S.Expanded()) -> S.Desugared():
  dt(lower(fuel(), OT{t}))

# desugarTerm: what the program is resolved to, with no case left in it.
def desugar(t: S.Expanded()) -> S.Desugared():
  lower.cases(optimize.builtins(add.builtins(t)))
