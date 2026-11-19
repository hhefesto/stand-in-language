import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Show.bend as Sh
import ./Resolve.bend as Rs

# The name binder (master's Telomare.Bind, 98c963c2; the spec is
# telomare-name-binder-spec.txt): whole-program name resolution with
# requirements, after expansion and before desugaring.
#
# A definition may mention a name that nothing binds where the definition
# is written. That name is a requirement of the definition, supplied by
# whichever binder encloses each place the definition is mentioned. The pass
# elaborates requirements away by lambda lifting: an open entry `k = body`
# with requirements r1 .. rn becomes `k = \__req_r1 -> .. \__req_rn -> body`,
# and each mention of k becomes `k a1 .. an`, every ai being ri resolved
# where k is mentioned. A requirement that reaches main unsupplied is an
# error.
#
# Scopes are lexical. A module's chain, innermost first, is its own
# top-level definitions (one store), then its imports with the last written
# innermost, then the builtins. Imports are not re-exported. Lambda and
# pattern variables never supply a requirement; since every later stage has
# one namespace, a variable that could capture a supplied argument is
# renamed.
#
# The output is one closed term: every module's top-level definitions main
# needs, under names unique to their module (`M::k`), in a let around main's
# body, the shape the import flattening it replaced produced.
#
# Bend has no mutual recursion, so the walk is one function, `go`, over a
# task (BT) giving a value (BV), with the state (St) threaded through.

# What kind of binder a frame is.
type BK is Data:
  KLet{}
  KMod{}
  KBuiltin{}

# What a binder key refers to: an entry, by its number, or a builtin.
type Target is Data:
  TEntry{+i: Nat}
  TBuiltin{}

type Key is Data:
  BKey{+loc: L.Loc, +t: Target}

# Lambda or pattern variables (source name to output name, which keeps the
# source location), or a binder's keys.
type Frame is Data:
  FVar{+vars: Map<&2, L.Name>}
  FBind{+k: BK, +keys: Map<&2, Key>}

# The frames, innermost first; the module's import qualifiers; its name.
type Ctx is Data:
  Ctx{+frames: List<&2, Frame>, +quals: List<&2, String>, +m: String}

# An entry: its key, its name in the output, its body, and its definition
# site, its own binder included.
type EDef is Data:
  EDef{+key: L.Name, +out: String, +body: S.Expanded(), +ctx: Ctx}

# Where a requirement came from: the occurrence, then each entry it was
# inherited through, innermost first.
type Trail is Data:
  Trail{+occ: L.Loc, +via: List<&2, Rs.Via>}

# Requirement names, each with the trail of its first occurrence.
def Req() -> Data:
  Map<&2, Trail>

# One requirement, in a list of them.
type RT is Data:
  RT{+name: String, +trail: Trail}

# An entry elaborated: its requirements and its lifted body.
type Elab is Data:
  Elab{+req: Req(), +t: S.Expanded()}

# Something legal but probably unintended (BindWarning): the name bound at
# loc shadows the same name bound at other; a variable has the name of a
# requirement that passes it by without being captured; a let entry no
# mention resolves to.
type W is Data:
  Shadows{+loc: L.Loc, +name: String, +other: L.Loc}
  ShadowsRequirement{+loc: L.Loc, +name: String}
  UnusedBinding{+loc: L.Loc, +name: String}

# A warning and the module it is about.
type MW is Data:
  MW{+m: String, +w: W}

# The next entry or variable number; the entries by number; those
# elaborated; the entries being elaborated, innermost first; the entries
# mentioned; the warnings, newest first.
type St is Data:
  St{+next: Nat, +defs: Map<&2, EDef>, +done: Map<&2, Elab>, +active: List<&2, Nat>, +used: Set(), +ws: List<&2, MW>}

# The nearest frame binding a name.
type Hit is Data:
  HVar{+out: L.Name}
  HBind{+k: BK, +loc: L.Loc, +t: Target}
  HNone{}

# What `go` does: elaborate a term or terms (elab); an occurrence, given
# what binds it (occurrence); a mention of a key (mention); a mention's
# arguments (one supply each); a supply, given the binder that has the
# requirement (supply); an entry's requirements, given whether it is done
# and whether it is being elaborated (requirementsOf); entries elaborated in
# turn (elaborated); a let, given its first duplicate key (elabLet); a
# case's alternatives; a pattern's guards (elabGuards).
type BT is Data:
  BTerm{+c: Ctx, +t: S.Expanded()}
  BTerms{+c: Ctx, +ts: List<&2, S.Expanded()>}
  BOcc{+c: Ctx, +loc: L.Loc, +name: String, +h: Hit}
  BMention{+c: Ctx, +loc: L.Loc, +name: String, +t: Target}
  BArgs{+c: Ctx, +loc: L.Loc, +via: Rs.Via, +rs: List<&2, RT>}
  BSupply{+c: Ctx, +loc: L.Loc, +name: String, +trail: Trail, +t: Maybe<&2, Target>}
  BReq{+i: Nat, +d: Maybe<&2, Elab>, +cyc: Bool}
  BElabs{+ids: List<&2, Nat>}
  BLet{+c: Ctx, +loc: L.Loc, +binds: List<&2, S.ExpandedBind()>, +body: S.Expanded(), +dup: Maybe<&2, L.Name>}
  BAlts{+c: Ctx, +alts: List<&2, S.ExpandedAlt()>}
  BGuards{+c: Ctx, +p: S.ExpandedPat()}

# What `go` gives back, with the requirements that escape it.
type BV is Data:
  VT{+t: S.Expanded(), +req: Req()}
  VTs{+ts: List<&2, S.Expanded()>, +req: Req()}
  VP{+p: S.ExpandedPat(), +req: Req()}
  VAs{+alts: List<&2, S.ExpandedAlt()>, +req: Req()}
  VR{+req: Req()}

type Out is Data:
  Out{+st: St, +v: BV}

# Variables brought into scope: their names in the output, and the state.
type Vars is Data:
  Vars{+outs: List<&2, L.Name>, +st: St}

# Entry numbers allocated, and the state.
type Ids is Data:
  Ids{+ids: List<&2, Nat>, +st: St}

# A module's top-level definitions (ModuleInfo): its keys, and its bindings
# with their numbers, in order.
type BI is Data:
  BI{+key: L.Name, +i: Nat, +val: S.Expanded()}

type MI is Data:
  MI{+name: String, +keys: Map<&2, Key>, +binds: List<&2, BI>}

type Infos is Data:
  Infos{+mis: List<&2, MI>, +st: St}

# An import layer: where the import is, and the imported module's keys
# (qualified, if the import is).
type Layer is Data:
  Layer{+loc: L.Loc, +keys: Map<&2, Key>}

# The module order's work: visit a module (imports first, then the module
# itself), a visit checked, a module done.
type MA is Data:
  AVisit{+stack: List<&2, String>, +name: String}
  ACheck{+stack: List<&2, String>, +name: String, +cyc: Bool, +seen: Bool, +found: Maybe<&2, List<&2, S.EItem>>}
  AFinish{+name: String}

# The bound program and its warnings, oldest first.
type Bound is Data:
  Bound{+t: S.Expanded(), +ws: List<&2, MW>}

def R(-A: Data) -> Data:
  Result<&2, &2, Rs.ResErr, A>

def fuel() -> Nat:
  U32.to_nat(4294967295)

def okv(-A: Data, x: A) -> R(A):
  Done{x}

# Names
# -----

# The lifted parameter standing for requirement r (requirementParam).
# Generated names start with `_`, which a source identifier cannot.
def req.param(r: String) -> String:
  "__req_" ++ r

# The name a module's top-level definition goes by in the output
# (topLevelName); `::` cannot occur in a source identifier.
def top.name(m: String, k: String) -> String:
  m ++ "::" ++ k

# Generated by an earlier stage, so exempt from shadowing and unused
# warnings, and never renamed.
def generated(s: String) -> Bool:
  match s:
    case SCon{Chr{95}, t}:
      True{}
    case _:
      False{}

def id.key(i: Nat) -> String:
  Nat.show(i)

def mlook(-V: Data, m: Map<&2, V>, +key: String) -> Maybe<&2, V>:
  Pair.snd(Map<&2, V>, Maybe<&2, V>, Map.pop(&2, V, m, key))

def mhas(-V: Data, m: Map<&2, V>, +key: String) -> Bool:
  Pair.snd(Map<&2, V>, Bool, Map.has(&2, V, m, key))

def shas(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

# Requirements
# ------------

def req0() -> Req():
  Map.new(&2, Trail)

def req1(+name: String, trail: Trail) -> Req():
  Map.set(&2, Trail, req0(), name, trail)

# Left-biased, as Haskell's (<>) on maps: a's trail wins.
def ru(a: Req(), b: Req()) -> Req():
  Map.union(&2, Trail, b, a)

def rts.go(kvs: List<&2, Sigma<&2, &2, String, _ => Trail>>) -> List<&2, RT>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      (k, v) = kv
      RT{k, v} <> rts.go(rest)

# In name order (Map.toAscList).
def rts(r: Req()) -> List<&2, RT>:
  rts.go(Map.to_list(&2, Trail, r))

def through(t: Trail, v: Rs.Via) -> Trail:
  match t:
    case Trail{occ, via}:
      Trail{occ, List.append(&2, Rs.Via, via, [v])}

# The state
# ---------

def st0() -> St:
  St{0n, Map.new(&2, EDef), Map.new(&2, Elab), [], Set.new(), []}

def st.ws(st: St) -> List<&2, MW>:
  match st:
    case St{next, defs, done, active, used, ws}:
      ws

def fresh.n(st: St) -> Nat:
  match st:
    case St{next, defs, done, active, used, ws}:
      next

def fresh.st(st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{1n+next, defs, done, active, used, ws}

def warn(+m: String, w: W, st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{next, defs, done, active, used, MW{m, w} <> ws}

def def.put(+i: Nat, d: EDef, st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{next, Map.set(&2, EDef, defs, id.key(i), d), done, active, used, ws}

def def.or(m: Maybe<&2, EDef>) -> EDef:
  match m:
    case Some{d}:
      d
    case None{}:
      EDef{L.Name{L.Unknown{}, ""}, "", S.SZero{L.Unknown{}}, Ctx{[], [], ""}}

def def.get(+i: Nat, st: St) -> EDef:
  match st:
    case St{next, defs, done, active, used, ws}:
      def.or(mlook(EDef, defs, id.key(i)))

def done.get(+i: Nat, st: St) -> Maybe<&2, Elab>:
  match st:
    case St{next, defs, done, active, used, ws}:
      mlook(Elab, done, id.key(i))

def done.put(+i: Nat, e: Elab, st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{next, defs, Map.set(&2, Elab, done, id.key(i), e), active, used, ws}

def active.has(+i: Nat, st: St) -> Bool:
  match st:
    case St{next, defs, done, active, used, ws}:
      List.contains(~Nat, ~Nat.is_eq, active, i)

def active.push(+i: Nat, st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{next, defs, done, i <> active, used, ws}

def active.pop(st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{next, defs, done, List.tail(&2, Nat, active), used, ws}

def use(+i: Nat, st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{next, defs, done, active, Set.add(used, id.key(i)), ws}

def is.used(+i: Nat, st: St) -> Bool:
  match st:
    case St{next, defs, done, active, used, ws}:
      shas(used, id.key(i))

def edef.key(d: EDef) -> L.Name:
  match d:
    case EDef{key, out, body, ctx}:
      key

def edef.out(d: EDef) -> String:
  match d:
    case EDef{key, out, body, ctx}:
      out

def edef.body(d: EDef) -> S.Expanded():
  match d:
    case EDef{key, out, body, ctx}:
      body

def edef.ctx(d: EDef) -> Ctx:
  match d:
    case EDef{key, out, body, ctx}:
      ctx

def elab.t(m: Maybe<&2, Elab>) -> S.Expanded():
  match m:
    case Some{e}:
      match e:
        case Elab{req, t}:
          t
    case None{}:
      S.SZero{L.Unknown{}}

# What requirementsOf needs to know about entry i.
def req.task(+i: Nat, +st: St) -> BT:
  BReq{i, done.get(i, st), active.has(i, st)}

def range.from(n: Nat, +i: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      []
    case 1n+k:
      i <> range.from(k, 1n+i)

def bump(n: Nat, st: St) -> St:
  match st:
    case St{next, defs, done, active, used, ws}:
      St{Nat.add(next, n), defs, done, active, used, ws}

# Allocate a number for each of n entries (fresh, n times).
def alloc(+n: Nat, +st: St) -> Ids:
  Ids{range.from(n, fresh.n(st)), bump(n, st)}

# Values
# ------

def o.st(o: Out) -> St:
  match o:
    case Out{st, v}:
      st

def o.v(o: Out) -> BV:
  match o:
    case Out{st, v}:
      v

def bv.req(v: BV) -> Req():
  match v:
    case VT{t, req}:
      req
    case VTs{ts, req}:
      req
    case VP{p, req}:
      req
    case VAs{alts, req}:
      req
    case VR{req}:
      req

def bv.t(v: BV) -> S.Expanded():
  match v:
    case VT{t, req}:
      t
    case _:
      S.SZero{L.Unknown{}}

def bv.ts(v: BV) -> List<&2, S.Expanded()>:
  match v:
    case VTs{ts, req}:
      ts
    case _:
      []

def bv.p(v: BV) -> S.ExpandedPat():
  match v:
    case VP{p, req}:
      p
    case _:
      S.PIgnore{}

def bv.alts(v: BV) -> List<&2, S.ExpandedAlt()>:
  match v:
    case VAs{alts, req}:
      alts
    case _:
      []

def oreq(o: Out) -> Req():
  bv.req(o.v(o))

def ot(o: Out) -> S.Expanded():
  bv.t(o.v(o))

def ots(o: Out) -> List<&2, S.Expanded()>:
  bv.ts(o.v(o))

def op(o: Out) -> S.ExpandedPat():
  bv.p(o.v(o))

def oas(o: Out) -> List<&2, S.ExpandedAlt()>:
  bv.alts(o.v(o))

def vars.outs(v: Vars) -> List<&2, L.Name>:
  match v:
    case Vars{outs, st}:
      outs

def vars.st(v: Vars) -> St:
  match v:
    case Vars{outs, st}:
      st

def ids.ids(v: Ids) -> List<&2, Nat>:
  match v:
    case Ids{ids, st}:
      ids

def ids.st(v: Ids) -> St:
  match v:
    case Ids{ids, st}:
      st

# Context
# -------

def ctx.frames(c: Ctx) -> List<&2, Frame>:
  match c:
    case Ctx{frames, quals, m}:
      frames

def ctx.quals(c: Ctx) -> List<&2, String>:
  match c:
    case Ctx{frames, quals, m}:
      quals

def ctx.m(c: Ctx) -> String:
  match c:
    case Ctx{frames, quals, m}:
      m

def push(fr: Frame, c: Ctx) -> Ctx:
  match c:
    case Ctx{frames, quals, m}:
      Ctx{fr <> frames, quals, m}

def builtin.names() -> List<&2, String>:
  ["zero", "left", "right", "trace", "abort", "pair", "app"]

def builtin.keys(ns: List<&2, String>, acc: Map<&2, Key>) -> Map<&2, Key>:
  match ns:
    case Nil{}:
      acc
    case Con{+n, rest}:
      builtin.keys(rest, Map.set(&2, Key, acc, n, BKey{L.Builtin{n}, TBuiltin{}}))

# The builtins, outermost in every chain: defined everywhere, so never a
# requirement and never supplied (Desugar's builtins and `zero`).
def builtin.frame() -> Frame:
  FBind{KBuiltin{}, builtin.keys(builtin.names(), Map.new(&2, Key))}

def key.hit(k: BK, m: Maybe<&2, Key>) -> Maybe<&2, Hit>:
  match m:
    case Some{key}:
      match key:
        case BKey{loc, t}:
          Some{HBind{k, loc, t}}
    case None{}:
      None{}

def var.hit(m: Maybe<&2, L.Name>) -> Maybe<&2, Hit>:
  match m:
    case Some{out}:
      Some{HVar{out}}
    case None{}:
      None{}

def frame.hit(fr: Frame, +name: String) -> Maybe<&2, Hit>:
  match fr:
    case FVar{vars}:
      var.hit(mlook(L.Name, vars, name))
    case FBind{k, keys}:
      key.hit(k, mlook(Key, keys, name))

def hit.or(m: Maybe<&2, Hit>, later: Hit) -> Hit:
  match m:
    case Some{h}:
      h
    case None{}:
      later

# The nearest frame binding a name (lookupFrames).
def lookup.frames(fs: List<&2, Frame>, +name: String) -> Hit:
  match fs:
    case Nil{}:
      HNone{}
    case Con{fr, rest}:
      hit.or(frame.hit(fr, name), lookup.frames(rest, name))

def target.or(m: Maybe<&2, Key>, later: Maybe<&2, Target>) -> Maybe<&2, Target>:
  match m:
    case Some{key}:
      match key:
        case BKey{loc, t}:
          Some{t}
    case None{}:
      later

# The innermost binder, variables skipped, with a key (lookupBinders).
def lookup.binders(fs: List<&2, Frame>, +name: String) -> Maybe<&2, Target>:
  match fs:
    case Nil{}:
      None{}
    case Con{fr, rest}:
      match fr:
        case FVar{vars}:
          lookup.binders(rest, name)
        case FBind{k, keys}:
          target.or(mlook(Key, keys, name), lookup.binders(rest, name))

# Whether a let binder among the frames has the key.
def let.key(fs: List<&2, Frame>, +name: String) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{fr, rest}:
      match fr:
        case FBind{k, keys}:
          match k:
            case KLet{}:
              mhas(Key, keys, name) || let.key(rest, name)
            case _:
              let.key(rest, name)
        case FVar{vars}:
          let.key(rest, name)

# Written through one of the module's import qualifiers (isQualified).
def qualified(qs: List<&2, String>, +name: String) -> Bool:
  match qs:
    case Nil{}:
      False{}
    case Con{q, rest}:
      String.starts_with(name, q ++ ".") || qualified(rest, name)

# Variables
# ---------

def shadow.var(h: Hit, +m: String, +loc: L.Loc, +text: String, st: St) -> St:
  match h:
    case HBind{k, kl, t}:
      match k:
        case KBuiltin{}:
          st
        case _:
          warn(m, Shadows{loc, text, kl}, st)
    case _:
      st

def var.out(yes: Bool, +loc: L.Loc, +text: String, st: St) -> L.Name:
  match yes:
    case True{}:
      L.Name{loc, "__var_" ++ text ++ "_" ++ Nat.show(fresh.n(st))}
    case False{}:
      L.Name{loc, text}

def var.st(yes: Bool, st: St) -> St:
  match yes:
    case True{}:
      fresh.st(st)
    case False{}:
      st

# One variable into scope: a shadowing warning, and a new name if a let key
# of the same name encloses it, so that an argument supplied from that key
# below it cannot be captured.
def var.one(gen: Bool, +c: Ctx, +loc: L.Loc, +text: String, st: St) -> Vars:
  match gen:
    case True{}:
      Vars{[L.Name{loc, text}], st}
    case False{}:
      +st1 = shadow.var(lookup.frames(ctx.frames(c), text), ctx.m(c), loc, text, st)
      +yes = let.key(ctx.frames(c), text)
      Vars{[var.out(yes, loc, text, st1)], var.st(yes, st1)}

def vars.then(v: Vars, rest: Vars) -> Vars:
  match v:
    case Vars{outs, st}:
      match rest:
        case Vars{outs2, st2}:
          Vars{List.append(&2, L.Name, outs, outs2), st2}

# Lambda or pattern variables into scope (bindVariables), in order.
def vars(+c: Ctx, ns: List<&2, L.Name>, st: St) -> Vars:
  match ns:
    case Nil{}:
      Vars{[], st}
    case Con{n, rest}:
      match n:
        case L.Name{+loc, +text}:
          +v = var.one(generated(text), c, loc, text, st)
          vars.then(v, vars(c, rest, vars.st(v)))

def var.map(ns: List<&2, L.Name>, outs: List<&2, L.Name>, acc: Map<&2, L.Name>) -> Map<&2, L.Name>:
  match ns:
    case Nil{}:
      acc
    case Con{n, rest}:
      match outs:
        case Nil{}:
          acc
        case Con{o, orest}:
          var.map(rest, orest, Map.set(&2, L.Name, acc, L.Name.text(n), o))

def var.frame(ns: List<&2, L.Name>, outs: List<&2, L.Name>) -> Frame:
  FVar{var.map(ns, outs, Map.new(&2, L.Name))}

def warn.passing.if(yes: Bool, +m: String, loc: L.Loc, text: String, st: St) -> St:
  match yes:
    case True{}:
      warn(m, ShadowsRequirement{loc, text}, st)
    case False{}:
      st

# A warning for each variable named as a requirement that passes it by
# (warnPassingRequirements).
def warn.passing(+m: String, ns: List<&2, L.Name>, +req: Req(), st: St) -> St:
  match ns:
    case Nil{}:
      st
    case Con{n, rest}:
      match n:
        case L.Name{+loc, +text}:
          warn.passing(m, rest, req, warn.passing.if(mhas(Trail, req, text), m, loc, text, st))

def name.or(m: Maybe<&2, L.Name>, n: L.Name) -> L.Name:
  match m:
    case Some{o}:
      o
    case None{}:
      n

def rename.pat(+rn: Map<&2, L.Name>, p: S.ExpandedPat()) -> S.ExpandedPat():
  match p:
    case S.PVar{+name}:
      S.PVar{name.or(mlook(L.Name, rn, L.Name.text(name)), name)}
    case S.PAnn{q, t}:
      S.PAnn{rename.pat(rn, q), t}
    case S.PPair{a, b}:
      S.PPair{rename.pat(rn, a), rename.pat(rn, b)}
    case other:
      other

# The variables a pattern binds, left to right (patternBinders).
def pat.names(p: S.ExpandedPat(), acc: List<&2, L.Name>) -> List<&2, L.Name>:
  match p:
    case S.PVar{name}:
      name <> acc
    case S.PAnn{q, t}:
      pat.names(q, acc)
    case S.PPair{a, b}:
      pat.names(a, pat.names(b, acc))
    case _:
      acc

# Lets
# ----

def bind.keys(bs: List<&2, S.ExpandedBind()>) -> List<&2, L.Name>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          name <> bind.keys(rest)

def dup.if(seen: Bool, n: L.Name, later: Maybe<&2, L.Name>) -> Maybe<&2, L.Name>:
  match seen:
    case True{}:
      Some{n}
    case False{}:
      later

# The first key whose name came before (duplicateKeys).
def dup.key(ns: List<&2, L.Name>, +seen: Set()) -> Maybe<&2, L.Name>:
  match ns:
    case Nil{}:
      None{}
    case Con{+n, rest}:
      dup.if(shas(seen, L.Name.text(n)), n, dup.key(rest, Set.add(seen, L.Name.text(n))))

def let.shadow(h: Hit, +m: String, +loc: L.Loc, +text: String, st: St) -> St:
  match h:
    case HBind{k, other, t}:
      match k:
        case KBuiltin{}:
          st
        case _:
          warn(m, Shadows{loc, text, other}, st)
    case HVar{other}:
      warn(m, Shadows{loc, text, L.Name.loc(other)}, st)
    case HNone{}:
      st

def let.shadow.if(gen: Bool, +fs: List<&2, Frame>, +m: String, +loc: L.Loc, +text: String, st: St) -> St:
  match gen:
    case True{}:
      st
    case False{}:
      let.shadow(lookup.frames(fs, text), m, loc, text, st)

# A let key that shadows an enclosing binder's key or variable.
def let.shadows(+fs: List<&2, Frame>, +m: String, ks: List<&2, L.Name>, st: St) -> St:
  match ks:
    case Nil{}:
      st
    case Con{k, rest}:
      match k:
        case L.Name{+loc, +text}:
          let.shadows(fs, m, rest, let.shadow.if(generated(text), fs, m, loc, text, st))

def let.keys(ks: List<&2, L.Name>, ids: List<&2, Nat>, acc: Map<&2, Key>) -> Map<&2, Key>:
  match ks:
    case Nil{}:
      acc
    case Con{k, rest}:
      match k:
        case L.Name{loc, +text}:
          match ids:
            case Nil{}:
              acc
            case Con{i, irest}:
              let.keys(rest, irest, Map.set(&2, Key, acc, text, BKey{loc, TEntry{i}}))

def let.defs(bs: List<&2, S.ExpandedBind()>, ids: List<&2, Nat>, +c: Ctx, st: St) -> St:
  match bs:
    case Nil{}:
      st
    case Con{b, rest}:
      match b:
        case S.Bind{+name, val}:
          match ids:
            case Nil{}:
              st
            case Con{+i, irest}:
              let.defs(rest, irest, c, def.put(i, EDef{name, L.Name.text(name), val, c}, st))

def unused.if(yes: Bool, +m: String, k: L.Name, st: St) -> St:
  match yes:
    case True{}:
      match k:
        case L.Name{loc, text}:
          warn(m, UnusedBinding{loc, text}, st)
    case False{}:
      st

# A let entry no mention resolved to.
def unused(+m: String, ks: List<&2, L.Name>, ids: List<&2, Nat>, +st: St) -> St:
  match ks:
    case Nil{}:
      st
    case Con{+k, rest}:
      match ids:
        case Nil{}:
          st
        case Con{+i, irest}:
          unused(m, rest, irest,
            unused.if(Bool.not(generated(L.Name.text(k))) && Bool.not(is.used(i, st)), m, k, st))

def rebind(ks: List<&2, L.Name>, ts: List<&2, S.Expanded()>) -> List<&2, S.ExpandedBind()>:
  match ks:
    case Nil{}:
      []
    case Con{k, rest}:
      match ts:
        case Nil{}:
          []
        case Con{t, trest}:
          S.Bind{k, t} <> rebind(rest, trest)

# Entries
# -------

def apps(xs: List<&2, S.Expanded()>, +loc: L.Loc, f: S.Expanded()) -> S.Expanded():
  match xs:
    case Nil{}:
      f
    case Con{x, rest}:
      apps(rest, loc, S.SApp{loc, f, x})

# The body under a lambda for each requirement, the first outermost.
def lift(+loc: L.Loc, rs: List<&2, String>, body: S.Expanded()) -> S.Expanded():
  match rs:
    case Nil{}:
      body
    case Con{r, rest}:
      S.SLam{loc, L.Name{loc, req.param(r)}, lift(loc, rest, body)}

def take.until.if(stop: Bool, x: Nat, later: List<&2, Nat>) -> List<&2, Nat>:
  match stop:
    case True{}:
      []
    case False{}:
      x <> later

def take.until(xs: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      take.until.if(Nat.is_eq(x, i), x, take.until(rest, i))

def drop.before.if(stop: Bool, x: Nat, rest: List<&2, Nat>, later: List<&2, Nat>) -> List<&2, Nat>:
  match stop:
    case True{}:
      x <> rest
    case False{}:
      later

def drop.before(xs: List<&2, Nat>, +i: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      drop.before.if(Nat.is_eq(x, i), x, rest, drop.before(rest, i))

def least(xs: List<&2, Nat>, +m: Nat) -> Nat:
  match xs:
    case Nil{}:
      m
    case Con{+x, rest}:
      least(rest, Nat.min(x, m))

def key.names(ns: List<&2, Nat>, +st: St) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+i, rest}:
      L.Name.text(edef.key(def.get(i, st))) <> key.names(rest, st)

def cycle.close(+ns: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, ns, List.take(&2, String, ns, 1n))

def cycle.at(+members: List<&2, Nat>, +m: Nat, +st: St) -> List<&2, String>:
  cycle.close(key.names(List.append(&2, Nat, drop.before(members, m), take.until(members, m)), st))

def active.of(st: St) -> List<&2, Nat>:
  match st:
    case St{next, defs, done, active, used, ws}:
      active

# The cycle entry i closes, from its earliest-written member, as Lower's
# topological sort reports one.
def cycle.names(+i: Nat, +st: St) -> List<&2, String>:
  +members = List.reverse(&2, Nat, i <> take.until(active.of(st), i))
  cycle.at(members, least(members, i), st)

def unbound(q: Bool, +loc: L.Loc, +name: String, st: St) -> R(Out):
  match q:
    case True{}:
      Fail{Rs.UnboundQualifiedName{loc, name}}
    case False{}:
      Done{Out{st, VT{S.SVar{loc, req.param(name)}, req1(name, Trail{loc, []})}}}

def supplied.at(loc: L.Loc) -> L.Loc:
  L.GenIn{"supplied requirement", loc}

# The walk
# --------

def go(+fuel: Nat, +st: St, task: BT) -> R(Out):
  match fuel:
    case 0n:
      Fail{Rs.MissingDefinitions{["(names nested too deeply)"]}}
    case 1n+f:
      match task:
        # elab
        case BTerm{+c, t}:
          match t:
            case S.SVar{+loc, +name}:
              go(f, st, BOcc{c, loc, name, lookup.frames(ctx.frames(c), name)})
            case S.SLam{loc, +v, body}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +vs : Vars <- okv(Vars, vars(c, [v], st))
                +o : Out <- go(f, vars.st(vs), BTerm{push(var.frame([v], vars.outs(vs)), c), body})
                return Out{warn.passing(ctx.m(c), [v], oreq(o), o.st(o)),
                           VT{S.SLam{loc, name.or(List.head(&2, L.Name, vars.outs(vs)), v), ot(o)}, oreq(o)}}
            case S.SLet{+loc, +binds, body}:
              go(f, st, BLet{c, loc, binds, body, dup.key(bind.keys(binds), Set.new())})
            case S.SCase{loc, scrut, alts, w}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BTerm{c, scrut})
                +o2 : Out <- go(f, o.st(o1), BAlts{c, alts})
                return Out{o.st(o2), VT{S.SCase{loc, ot(o1), oas(o2), w}, ru(oreq(o1), oreq(o2))}}
            case S.SApp{loc, a, b}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BTerm{c, a})
                +o2 : Out <- go(f, o.st(o1), BTerm{c, b})
                return Out{o.st(o2), VT{S.SApp{loc, ot(o1), ot(o2)}, ru(oreq(o1), oreq(o2))}}
            case S.SPair{loc, a, b}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BTerm{c, a})
                +o2 : Out <- go(f, o.st(o1), BTerm{c, b})
                return Out{o.st(o2), VT{S.SPair{loc, ot(o1), ot(o2)}, ru(oreq(o1), oreq(o2))}}
            case S.SCheck{loc, k, a, b}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BTerm{c, a})
                +o2 : Out <- go(f, o.st(o1), BTerm{c, b})
                return Out{o.st(o2), VT{S.SCheck{loc, k, ot(o1), ot(o2)}, ru(oreq(o1), oreq(o2))}}
            case S.SIte{loc, a, b, d}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BTerm{c, a})
                +o2 : Out <- go(f, o.st(o1), BTerm{c, b})
                +o3 : Out <- go(f, o.st(o2), BTerm{c, d})
                return Out{o.st(o3), VT{S.SIte{loc, ot(o1), ot(o2), ot(o3)}, ru(oreq(o1), ru(oreq(o2), oreq(o3)))}}
            case S.SRec{loc, a, b, d}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BTerm{c, a})
                +o2 : Out <- go(f, o.st(o1), BTerm{c, b})
                +o3 : Out <- go(f, o.st(o2), BTerm{c, d})
                return Out{o.st(o3), VT{S.SRec{loc, ot(o1), ot(o2), ot(o3)}, ru(oreq(o1), ru(oreq(o2), oreq(o3)))}}
            case S.SLeft{loc, x}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o : Out <- go(f, st, BTerm{c, x})
                return Out{o.st(o), VT{S.SLeft{loc, ot(o)}, oreq(o)}}
            case S.SRight{loc, x}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o : Out <- go(f, st, BTerm{c, x})
                return Out{o.st(o), VT{S.SRight{loc, ot(o)}, oreq(o)}}
            case S.SList{loc, xs}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o : Out <- go(f, st, BTerms{c, xs})
                return Out{o.st(o), VT{S.SList{loc, ots(o)}, oreq(o)}}
            case S.SZero{loc}:
              Done{Out{st, VT{S.SZero{loc}, req0()}}}
            case S.SChurch{loc, n}:
              Done{Out{st, VT{S.SChurch{loc, n}, req0()}}}
            case S.SInt{loc, n}:
              Done{Out{st, VT{S.SInt{loc, n}, req0()}}}
            case S.SStr{loc, s}:
              Done{Out{st, VT{S.SStr{loc, s}, req0()}}}
            case S.SLamPat{loc, pats, body, w}:
              Empty.absurd(R(Out), w)
            case S.SLetSugar{loc, defs, body, w}:
              Empty.absurd(R(Out), w)
            case S.SLamN{loc, n, v, body, w}:
              Empty.absurd(R(Out), w)
        case BTerms{+c, ts}:
          match ts:
            case Nil{}:
              Done{Out{st, VTs{[], req0()}}}
            case Con{x, rest}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BTerm{c, x})
                +o2 : Out <- go(f, o.st(o1), BTerms{c, rest})
                return Out{o.st(o2), VTs{ot(o1) <> ots(o2), ru(oreq(o1), oreq(o2))}}
        # occurrence
        case BOcc{+c, +loc, +name, h}:
          match h:
            case HVar{out}:
              Done{Out{st, VT{S.SVar{loc, L.Name.text(out)}, req0()}}}
            case HBind{k, kl, t}:
              go(f, st, BMention{c, loc, name, t})
            case HNone{}:
              unbound(qualified(ctx.quals(c), name), loc, name, st)
        # mention: a key applied to its requirements, each resolved here
        case BMention{+c, +loc, +name, t}:
          match t:
            case TBuiltin{}:
              Done{Out{st, VT{S.SVar{loc, name}, req0()}}}
            case TEntry{+i}:
              +st1 = use(i, st)
              +d = def.get(i, st1)
              +al = supplied.at(loc)
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st1, req.task(i, st1))
                +o2 : Out <- go(f, o.st(o1), BArgs{c, al, Rs.Via{L.Name.text(edef.key(d)), L.Name.loc(edef.key(d))}, rts(oreq(o1))})
                return Out{o.st(o2), VT{apps(ots(o2), al, S.SVar{loc, edef.out(d)}), oreq(o2)}}
        case BArgs{+c, +loc, +via, rs}:
          match rs:
            case Nil{}:
              Done{Out{st, VTs{[], req0()}}}
            case Con{x, rest}:
              match x:
                case RT{+r, trail}:
                  do Result<&2, &2, Rs.ResErr, Out>:
                    +o1 : Out <- go(f, st, BSupply{c, loc, r, through(trail, via), lookup.binders(ctx.frames(c), r)})
                    +o2 : Out <- go(f, o.st(o1), BArgs{c, loc, via, rest})
                    return Out{o.st(o2), VTs{ot(o1) <> ots(o2), ru(oreq(o1), oreq(o2))}}
        # supply
        case BSupply{+c, +loc, +name, trail, t}:
          match t:
            case Some{tg}:
              go(f, st, BMention{c, loc, name, tg})
            case None{}:
              Done{Out{st, VT{S.SVar{loc, req.param(name)}, req1(name, trail)}}}
        # requirementsOf: an entry elaborated on first demand
        case BReq{+i, d, cyc}:
          match d:
            case Some{e}:
              match e:
                case Elab{req, t}:
                  Done{Out{st, VR{req}}}
            case None{}:
              match cyc:
                case True{}:
                  Fail{Rs.DefinitionCycle{cycle.names(i, st)}}
                case False{}:
                  +dd = def.get(i, st)
                  do Result<&2, &2, Rs.ResErr, Out>:
                    +o : Out <- go(f, active.push(i, st), BTerm{edef.ctx(dd), edef.body(dd)})
                    return Out{done.put(i, Elab{oreq(o), lift(L.GenIn{"lifted requirement", L.Name.loc(edef.key(dd))},
                                                              Map.keys(&2, Trail, oreq(o)), ot(o))},
                                        active.pop(o.st(o))),
                               VR{oreq(o)}}
        # elaborated, for each entry in turn
        case BElabs{ids}:
          match ids:
            case Nil{}:
              Done{Out{st, VTs{[], req0()}}}
            case Con{+i, rest}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, req.task(i, st))
                +o2 : Out <- go(f, o.st(o1), BElabs{rest})
                return Out{o.st(o2), VTs{elab.t(done.get(i, o.st(o1))) <> ots(o2), req0()}}
        # elabLet
        case BLet{+c, +loc, +binds, body, dup}:
          match dup:
            case Some{+n}:
              Fail{Rs.DuplicateDefinition{L.Name.loc(n), L.Name.text(n)}}
            case None{}:
              +ks = bind.keys(binds)
              +al = alloc(List.length(&2, L.Name, ks), let.shadows(ctx.frames(c), ctx.m(c), ks, st))
              +c2 = push(FBind{KLet{}, let.keys(ks, ids.ids(al), Map.new(&2, Key))}, c)
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, let.defs(binds, ids.ids(al), c2, ids.st(al)), BTerm{c2, body})
                +o2 : Out <- go(f, o.st(o1), BElabs{ids.ids(al)})
                return Out{unused(ctx.m(c), ks, ids.ids(al), o.st(o2)), VT{S.SLet{loc, rebind(ks, ots(o2)), ot(o1)}, oreq(o1)}}
        # a case's alternatives: guards outside the pattern's variables, the
        # body inside them
        case BAlts{+c, alts}:
          match alts:
            case Nil{}:
              Done{Out{st, VAs{[], req0()}}}
            case Con{a, rest}:
              match a:
                case S.Alt{+p, body}:
                  +bs = pat.names(p, [])
                  do Result<&2, &2, Rs.ResErr, Out>:
                    +o1 : Out <- go(f, st, BGuards{c, p})
                    +vs : Vars <- okv(Vars, vars(c, bs, o.st(o1)))
                    +o2 : Out <- go(f, vars.st(vs), BTerm{push(var.frame(bs, vars.outs(vs)), c), body})
                    +o3 : Out <- go(f, warn.passing(ctx.m(c), bs, oreq(o2), o.st(o2)), BAlts{c, rest})
                    return Out{o.st(o3),
                               VAs{S.Alt{rename.pat(var.map(bs, vars.outs(vs), Map.new(&2, L.Name)), op(o1)), ot(o2)} <> oas(o3),
                                   ru(ru(oreq(o1), oreq(o2)), oreq(o3))}}
        # elabGuards
        case BGuards{+c, p}:
          match p:
            case S.PAnn{q, t}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BGuards{c, q})
                +o2 : Out <- go(f, o.st(o1), BTerm{c, t})
                return Out{o.st(o2), VP{S.PAnn{op(o1), ot(o2)}, ru(oreq(o1), oreq(o2))}}
            case S.PPair{a, b}:
              do Result<&2, &2, Rs.ResErr, Out>:
                +o1 : Out <- go(f, st, BGuards{c, a})
                +o2 : Out <- go(f, o.st(o1), BGuards{c, b})
                return Out{o.st(o2), VP{S.PPair{op(o1), op(o2)}, ru(oreq(o1), oreq(o2))}}
            case other:
              Done{Out{st, VP{other, req0()}}}

# Modules
# -------

def import.names(items: List<&2, S.EItem>) -> List<&2, String>:
  match items:
    case Nil{}:
      []
    case Con{it, rest}:
      match it:
        case S.EImport{imp}:
          match imp:
            case S.Import{loc, m, q}:
              L.Name.text(m) <> import.names(rest)
        case S.EBind{n, v}:
          import.names(rest)

def visits(+stack: List<&2, String>, ns: List<&2, String>, rest: List<&2, MA>) -> List<&2, MA>:
  match ns:
    case Nil{}:
      rest
    case Con{n, more}:
      AVisit{stack, n} <> visits(stack, more, rest)

# The reachable modules, in the order the old import flattening listed them:
# imports first, depth first, each module once (moduleOrder).
def order(+fuel: Nat, +mods: List<&2, Rs.Mod>, +seen: List<&2, String>, acc: List<&2, String>, todo: List<&2, MA>) ->
  R(List<&2, String>):
  match fuel:
    case 0n:
      Fail{Rs.ModuleNotFound{"(imports nested too deeply)"}}
    case 1n+f:
      match todo:
        case Nil{}:
          Done{List.reverse(&2, String, acc)}
        case Con{a, rest}:
          match a:
            case AFinish{name}:
              order(f, mods, seen, name <> acc, rest)
            case AVisit{+stack, +name}:
              order(f, mods, seen, acc,
                ACheck{stack, name, Rs.in.stack(stack, name), Rs.in.stack(seen, name), Rs.find.mod(mods, name)} <> rest)
            case ACheck{+stack, +name, cyc, sn, found}:
              match cyc:
                case True{}:
                  Fail{Rs.ImportCycle{List.append(&2, String, Rs.drop.until(stack, name), [name])}}
                case False{}:
                  match sn:
                    case True{}:
                      order(f, mods, seen, acc, rest)
                    case False{}:
                      match found:
                        case None{}:
                          Fail{Rs.ModuleNotFound{name}}
                        case Some{items}:
                          order(f, mods, name <> seen, acc,
                            visits(List.append(&2, String, stack, [name]), import.names(items), AFinish{name} <> rest))

def module.binds(items: List<&2, S.EItem>) -> List<&2, S.ExpandedBind()>:
  match items:
    case Nil{}:
      []
    case Con{it, rest}:
      match it:
        case S.EBind{n, v}:
          S.Bind{n, v} <> module.binds(rest)
        case S.EImport{imp}:
          module.binds(rest)

def items.of(m: Maybe<&2, List<&2, S.EItem>>) -> List<&2, S.EItem>:
  match m:
    case Some{items}:
      items
    case None{}:
      []

def bis(bs: List<&2, S.ExpandedBind()>, ids: List<&2, Nat>) -> List<&2, BI>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{n, v}:
          match ids:
            case Nil{}:
              []
            case Con{i, irest}:
              BI{n, i, v} <> bis(rest, irest)

def mi.of(+name: String, +bs: List<&2, S.ExpandedBind()>, +al: Ids) -> MI:
  MI{name, let.keys(bind.keys(bs), ids.ids(al), Map.new(&2, Key)), bis(bs, ids.ids(al))}

def info.then(mi: MI, rest: Infos) -> Infos:
  match rest:
    case Infos{mis, st}:
      Infos{mi <> mis, st}

def dup.or(dup: Maybe<&2, L.Name>, later: R(Unit)) -> R(Unit):
  match dup:
    case Some{+n}:
      Fail{Rs.DuplicateDefinition{L.Name.loc(n), L.Name.text(n)}}
    case None{}:
      later

# The first module, in order, with two definitions of one name.
def dups(+mods: List<&2, Rs.Mod>, order: List<&2, String>) -> R(Unit):
  match order:
    case Nil{}:
      Done{Unit{}}
    case Con{+name, rest}:
      dup.or(dup.key(bind.keys(module.binds(items.of(Rs.find.mod(mods, name)))), Set.new()), dups(mods, rest))

# Every module's store, numbered before any is elaborated: chains refer
# across modules. Duplicates are found first (dups).
def infos(+mods: List<&2, Rs.Mod>, order: List<&2, String>, st: St) -> Infos:
  match order:
    case Nil{}:
      Infos{[], st}
    case Con{+name, rest}:
      +bs = module.binds(items.of(Rs.find.mod(mods, name)))
      +al = alloc(List.length(&2, S.ExpandedBind(), bs), st)
      info.then(mi.of(name, bs, al), infos(mods, rest, ids.st(al)))

def mi.name(mi: MI) -> String:
  match mi:
    case MI{name, keys, binds}:
      name

def mi.keys(mi: MI) -> Map<&2, Key>:
  match mi:
    case MI{name, keys, binds}:
      keys

def mi.binds(mi: MI) -> List<&2, BI>:
  match mi:
    case MI{name, keys, binds}:
      binds

def mi.find.if(yes: Bool, mi: MI, later: Maybe<&2, MI>) -> Maybe<&2, MI>:
  match yes:
    case True{}:
      Some{mi}
    case False{}:
      later

def mi.find(mis: List<&2, MI>, +name: String) -> Maybe<&2, MI>:
  match mis:
    case Nil{}:
      None{}
    case Con{+mi, rest}:
      mi.find.if(String.eq(mi.name(mi), name), mi, mi.find(rest, name))

def mi.keys.of(m: Maybe<&2, MI>) -> Map<&2, Key>:
  match m:
    case Some{mi}:
      mi.keys(mi)
    case None{}:
      Map.new(&2, Key)

# A module's imports, as (module, qualifier, where), each pair of module and
# qualifier once, at its first (nubOn).
type Imp is Data:
  Imp{+m: String, +q: Maybe<&2, String>, +loc: L.Loc}

def qual.text(q: Maybe<&2, L.Name>) -> Maybe<&2, String>:
  match q:
    case Some{n}:
      Some{L.Name.text(n)}
    case None{}:
      None{}

def qual.key(q: Maybe<&2, String>) -> String:
  match q:
    case Some{s}:
      "Q" ++ s
    case None{}:
      "-"

def imp.key(+i: Imp) -> String:
  match i:
    case Imp{m, q, loc}:
      m ++ " " ++ qual.key(q)

def imps.nub.if(seen: Bool, i: Imp, later: List<&2, Imp>) -> List<&2, Imp>:
  match seen:
    case True{}:
      later
    case False{}:
      i <> later

def imps.nub(xs: List<&2, Imp>, +seen: Set()) -> List<&2, Imp>:
  match xs:
    case Nil{}:
      []
    case Con{+i, rest}:
      imps.nub.if(shas(seen, imp.key(i)), i, imps.nub(rest, Set.add(seen, imp.key(i))))

def imps(items: List<&2, S.EItem>) -> List<&2, Imp>:
  match items:
    case Nil{}:
      []
    case Con{it, rest}:
      match it:
        case S.EImport{imp}:
          match imp:
            case S.Import{loc, m, q}:
              Imp{L.Name.text(m), qual.text(q), loc} <> imps(rest)
        case S.EBind{n, v}:
          imps(rest)

def qual.prefix(q: Maybe<&2, String>) -> String:
  match q:
    case Some{s}:
      s ++ "."
    case None{}:
      ""

def qualify.keys(kvs: List<&2, Sigma<&2, &2, String, _ => Key>>, +q: Maybe<&2, String>, acc: Map<&2, Key>) -> Map<&2, Key>:
  match kvs:
    case Nil{}:
      acc
    case Con{kv, rest}:
      (k, v) = kv
      qualify.keys(rest, q, Map.set(&2, Key, acc, qual.prefix(q) ++ k, v))

def layer(+mis: List<&2, MI>, i: Imp) -> Layer:
  match i:
    case Imp{+m, +q, loc}:
      Layer{loc, qualify.keys(Map.to_list(&2, Key, mi.keys.of(mi.find(mis, m))), q, Map.new(&2, Key))}

def layers(+mis: List<&2, MI>, xs: List<&2, Imp>) -> List<&2, Layer>:
  match xs:
    case Nil{}:
      []
    case Con{i, rest}:
      layer(mis, i) <> layers(mis, rest)

def quals(xs: List<&2, Imp>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{i, rest}:
      match i:
        case Imp{m, q, loc}:
          match q:
            case Some{s}:
              s <> quals(rest)
            case None{}:
              quals(rest)

def layer.frames(ls: List<&2, Layer>, acc: List<&2, Frame>) -> List<&2, Frame>:
  match ls:
    case Nil{}:
      acc
    case Con{l, rest}:
      match l:
        case Layer{loc, keys}:
          layer.frames(rest, FBind{KMod{}, keys} <> acc)

def layer.keys(l: Layer) -> Map<&2, Key>:
  match l:
    case Layer{loc, keys}:
      keys

def key.loc(m: Maybe<&2, Key>) -> L.Loc:
  match m:
    case Some{k}:
      match k:
        case BKey{loc, t}:
          loc
    case None{}:
      L.Unknown{}

def layer.find.if(yes: Bool, +l: Layer, later: Maybe<&2, Layer>) -> Maybe<&2, Layer>:
  match yes:
    case True{}:
      Some{l}
    case False{}:
      later

# The first layer with key k.
def layer.find(ls: List<&2, Layer>, +k: String) -> Maybe<&2, Layer>:
  match ls:
    case Nil{}:
      None{}
    case Con{+l, rest}:
      layer.find.if(mhas(Key, layer.keys(l), k), l, layer.find(rest, k))

def shadow.layer(m: Maybe<&2, Layer>, +mn: String, +loc: L.Loc, +k: String, st: St) -> St:
  match m:
    case Some{l}:
      warn(mn, Shadows{loc, k, key.loc(mlook(Key, layer.keys(l), k))}, st)
    case None{}:
      st

def shadow.keys(ks: List<&2, String>, +earlier: List<&2, Layer>, +mn: String, +loc: L.Loc, st: St) -> St:
  match ks:
    case Nil{}:
      st
    case Con{+k, rest}:
      shadow.keys(rest, earlier, mn, loc, shadow.layer(layer.find(earlier, k), mn, loc, k, st))

# A later import shadows an earlier one: each key of each layer, against
# the nearest earlier layer with it.
def shadow.layers(ls: List<&2, Layer>, +earlier: List<&2, Layer>, +mn: String, st: St) -> St:
  match ls:
    case Nil{}:
      st
    case Con{+l, rest}:
      match l:
        case Layer{+loc, +keys}:
          shadow.layers(rest, Layer{loc, keys} <> earlier, mn,
            shadow.keys(Map.keys(&2, Key, keys), earlier, mn, loc, st))

def shadow.own.if(gen: Bool, m: Maybe<&2, Layer>, +mn: String, +loc: L.Loc, +k: String, st: St) -> St:
  match gen:
    case True{}:
      st
    case False{}:
      shadow.layer(m, mn, loc, k, st)

def shadow.own.kv(+k: String, v: Key, +rev: List<&2, Layer>, +mn: String, st: St) -> St:
  shadow.own.if(generated(k), layer.find(rev, k), mn, key.loc(Some{v}), k, st)

# The module's own definitions shadow every import: each against the last
# import with it.
def shadow.own(kvs: List<&2, Sigma<&2, &2, String, _ => Key>>, +rev: List<&2, Layer>, +mn: String, st: St) -> St:
  match kvs:
    case Nil{}:
      st
    case Con{kv, rest}:
      (k, v) = kv
      shadow.own(rest, rev, mn, shadow.own.kv(k, v, rev, mn, st))

# A module's scope chain, and the shadowing its imports make (moduleCtx).
def module.ctx(+mis: List<&2, MI>, +mi: MI, +items: List<&2, S.EItem>) -> Ctx:
  +firsts = imps.nub(imps(items), Set.new())
  Ctx{FBind{KMod{}, mi.keys(mi)} <> layer.frames(layers(mis, firsts), [builtin.frame()]), quals(firsts), mi.name(mi)}

def module.warn(+mis: List<&2, MI>, +mi: MI, +items: List<&2, S.EItem>, st: St) -> St:
  +ls = layers(mis, imps.nub(imps(items), Set.new()))
  shadow.own(Map.to_list(&2, Key, mi.keys(mi)), List.reverse(&2, Layer, ls), mi.name(mi),
    shadow.layers(ls, [], mi.name(mi), st))

def module.defs(bs: List<&2, BI>, +mn: String, +c: Ctx, st: St) -> St:
  match bs:
    case Nil{}:
      st
    case Con{b, rest}:
      match b:
        case BI{+key, +i, val}:
          module.defs(rest, mn, c, def.put(i, EDef{key, top.name(mn, L.Name.text(key)), val, c}, st))

# Every module's definitions registered at its chain, in order.
def modules(+mods: List<&2, Rs.Mod>, +all: List<&2, MI>, mis: List<&2, MI>, st: St) -> St:
  match mis:
    case Nil{}:
      st
    case Con{+mi, rest}:
      +items = items.of(Rs.find.mod(mods, mi.name(mi)))
      modules(mods, all, rest,
        module.defs(mi.binds(mi), mi.name(mi), module.ctx(all, mi, items), module.warn(all, mi, items, st)))

def out.bind(m: Maybe<&2, Elab>, key: L.Name, +mn: String, rest: List<&2, S.ExpandedBind()>) -> List<&2, S.ExpandedBind()>:
  match m:
    case Some{e}:
      match e:
        case Elab{req, t}:
          match key:
            case L.Name{loc, text}:
              S.Bind{L.Name{loc, top.name(mn, text)}, t} <> rest
    case None{}:
      rest

def out.binds(bs: List<&2, BI>, +mn: String, +st: St) -> List<&2, S.ExpandedBind()>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case BI{key, +i, val}:
          out.bind(done.get(i, st), key, mn, out.binds(rest, mn, st))

def out.all(mis: List<&2, MI>, +st: St) -> List<&2, S.ExpandedBind()>:
  match mis:
    case Nil{}:
      []
    case Con{+mi, rest}:
      List.append(&2, S.ExpandedBind(), out.binds(mi.binds(mi), mi.name(mi), st), out.all(rest, st))

def main.found(+m: String, k: Maybe<&2, Key>) -> R(Key):
  match k:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{Rs.NoMainFunction{m}}

def main.key(+m: String, mi: Maybe<&2, MI>) -> R(Key):
  match mi:
    case None{}:
      Fail{Rs.NoMainFunction{m}}
    case Some{x}:
      main.found(m, mlook(Key, mi.keys(x), "main"))

def main.id(k: Key) -> Nat:
  match k:
    case BKey{loc, t}:
      match t:
        case TEntry{i}:
          i
        case TBuiltin{}:
          0n

def main.loc(k: Key) -> L.Loc:
  match k:
    case BKey{loc, t}:
      loc

# A requirement left at main is an error: unbound in main itself, or
# inherited through definitions.
def main.req(rs: List<&2, RT>, +mainLoc: L.Loc) -> R(Unit):
  match rs:
    case Nil{}:
      Done{Unit{}}
    case Con{x, rest}:
      match x:
        case RT{r, trail}:
          match trail:
            case Trail{occ, via}:
              match via:
                case Nil{}:
                  Fail{Rs.MissingDefinitionAt{occ, r}}
                case Con{v, vs}:
                  Fail{Rs.UnsuppliedRequirement{r, occ, List.append(&2, Rs.Via, v <> vs, [Rs.Via{"main", mainLoc}])}}

def infos.mis(i: Infos) -> List<&2, MI>:
  match i:
    case Infos{mis, st}:
      mis

def infos.st(i: Infos) -> St:
  match i:
    case Infos{mis, st}:
      st

def root(+body: S.Expanded(), +bs: List<&2, S.ExpandedBind()>) -> S.Expanded():
  S.SLet{L.GenIn{"resolveMain", S.loc(Empty, Unit, Empty, body)}, bs, body}

# Resolve, elaborate and diagnose a program (bindProgram). The output is
# closed: one let of every needed top-level definition around main's body.
# Each warning comes with the name of the module it is about.
def program(+mods: List<&2, Rs.Mod>, +m: String) -> R(Bound):
  do Result<&2, &2, Rs.ResErr, Bound>:
    +ord : List<&2, String> <- order(fuel(), mods, [], [], [AVisit{[], m}])
    u0 : Unit <- dups(mods, ord)
    +inf : Infos <- okv(Infos, infos(mods, ord, st0()))
    +k : Key <- main.key(m, mi.find(infos.mis(inf), m))
    +st : St <- okv(St, modules(mods, infos.mis(inf), infos.mis(inf), infos.st(inf)))
    +o : Out <- go(fuel(), st, req.task(main.id(k), st))
    u : Unit <- main.req(rts(oreq(o)), main.loc(k))
    return Bound{root(elab.t(done.get(main.id(k), o.st(o))), out.all(infos.mis(inf), o.st(o))),
                 List.reverse(&2, MW, st.ws(o.st(o)))}

# Pruning (resolveMainWithWarnings)
# ---------------------------------

def nbs(bs: List<&2, S.ExpandedBind()>) -> List<&2, Rs.NB>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{n, v}:
          Rs.NB{L.Name.text(n), v} <> nbs(rest)

def nb.names(bs: List<&2, Rs.NB>, acc: Set()) -> Set():
  match bs:
    case Nil{}:
      acc
    case Con{b, rest}:
      match b:
        case Rs.NB{n, v}:
          nb.names(rest, Set.add(acc, n))

def kept.if(yes: Bool, b: S.ExpandedBind(), rest: List<&2, S.ExpandedBind()>) -> List<&2, S.ExpandedBind()>:
  match yes:
    case True{}:
      b <> rest
    case False{}:
      rest

def kept(bs: List<&2, S.ExpandedBind()>, +live: Set()) -> List<&2, S.ExpandedBind()>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{+n, v}:
          kept.if(shas(live, L.Name.text(n)), S.Bind{n, v}, kept(rest, live))

# Only the top-level definitions main reaches.
def prune.top(t: S.Expanded()) -> S.Expanded():
  match t:
    case S.SLet{loc, +bs, +body}:
      S.SLet{loc, kept(bs, nb.names(Rs.prune(body, nbs(bs)), Set.new())), body}
    case other:
      other

def bound.pruned(b: Bound) -> Bound:
  match b:
    case Bound{t, ws}:
      Bound{prune.top(t), ws}

# Bind names across the whole program and keep only the top-level
# definitions main reaches (resolveMainWithWarnings).
def resolve(+mods: List<&2, Rs.Mod>, +m: String) -> R(Bound):
  do Result<&2, &2, Rs.ResErr, Bound>:
    b : Bound <- program(mods, m)
    return bound.pruned(b)

def bound.t(b: Bound) -> S.Expanded():
  match b:
    case Bound{t, ws}:
      t

# The program as one let around main (resolveMain).
def main(+mods: List<&2, Rs.Mod>, +m: String) -> R(S.Expanded()):
  do Result<&2, &2, Rs.ResErr, S.Expanded()>:
    b : Bound <- resolve(mods, m)
    return bound.t(b)

# Warnings
# --------

def at.loc(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      " at " ++ s
    case None{}:
      ""

def compact.or(m: Maybe<&2, String>, +l: L.Loc) -> String:
  match m:
    case Some{s}:
      s
    case None{}:
      L.render_verbose(l)

# renderBindWarning
def render(w: W) -> String:
  match w:
    case Shadows{loc, name, +other}:
      "warning: " ++ Sh.string(name) ++ " shadows the binding at " ++ compact.or(L.render_compact(other), other)
        ++ at.loc(L.render_compact(loc))
    case ShadowsRequirement{loc, +name}:
      "warning: variable " ++ Sh.string(name) ++ " does not supply the requirement " ++ Sh.string(name)
        ++ " of what its body mentions" ++ at.loc(L.render_compact(loc))
    case UnusedBinding{loc, name}:
      "warning: " ++ Sh.string(name) ++ " is never used" ++ at.loc(L.render_compact(loc))

# bindWarningLoc
def loc(w: W) -> L.Loc:
  match w:
    case Shadows{loc, name, other}:
      loc
    case ShadowsRequirement{loc, name}:
      loc
    case UnusedBinding{loc, name}:
      loc

# The name a warning is about.
def name(w: W) -> String:
  match w:
    case Shadows{loc, name, other}:
      name
    case ShadowsRequirement{loc, name}:
      name
    case UnusedBinding{loc, name}:
      name

def ws.of(r: R(Bound)) -> List<&2, MW>:
  match r:
    case Done{b}:
      match b:
        case Bound{t, ws}:
          ws
    case Fail{e}:
      []

def mw.lines(ws: List<&2, MW>) -> List<&2, String>:
  match ws:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case MW{m, w}:
          render(w) <> mw.lines(rest)

def lines.if(ok: Bool, +mods: List<&2, Rs.Mod>, +m: String) -> List<&2, String>:
  match ok:
    case True{}:
      mw.lines(ws.of(resolve(mods, m)))
    case False{}:
      []

# The binder's warnings about a program, rendered, none when a module does
# not parse or expand or the program does not bind (compiling it reports
# why) (programWarnings).
def warnings(+mods: List<&2, Rs.Mod>, ok: Bool, +m: String) -> List<&2, String>:
  lines.if(ok, mods, m)
