import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Resolve.bend as Rs

# Where each recursion site sits in the program's nesting of recursions, and
# which bindings are used below the level they were bound at (haskell-final's
# Telomare.Levels).
#
# This is a purely structural reading of the expanded source: syntactic
# containment, plus per-parameter offset summaries that let an offset
# compose along a call chain. Nothing is evaluated and nothing is searched,
# so it is cheap where sizing is not; it answers a different question than
# sizing does.
#
# A site at level d has its test, recursion and last read at d + 1. A
# binding used k levels below where it was bound is under duplication
# pressure: every level between the two copies it.
#
# What it is not: a termination proof, a measurement, or a bound of any
# kind. The counts that bound the program are sizing's, reported beside
# these by Certificate.bend. Known approximation: a parameter applied as a
# function whose summary is unknown contributes offset 0, so a recursion
# reached only through such a parameter can be reported one level shallower
# than it is (DESIGN.md §11.8).

# A top-level definition, or a let binding qualified by the definition it
# appears in (DefId).
type Def is Data:
  Def{+m: String, +n: String}

# A definition's body, under the identity it is reported by.
type DI is Data:
  DI{+id: Def, +body: S.Surf}

# A binding in scope: who bound it, its name, and the level it was bound at.
type B is Data:
  B{+owner: Def, +name: String, +level: U32}

def B.level(b: B) -> U32:
  match b:
    case B{owner, name, level}:
      level

# A recursion site as written, and the levels it is observed at, as keys
# (zero-padded, so they sort as numbers) to the levels.
type Site is Data:
  Site{+source: String, +owner: Def, +levels: Map<&2, U32>}

# The deepest a binding is used below its binding, so far.
type Bang is Data:
  Bang{+b: B, +k: U32}

# What the structural pass found (LevelsInfo): every recursion site
# reachable from the entry with its levels, in source order; the bindings
# used below their binding level, deepest first; the maximum nesting depth.
type Info is Data:
  Info{+sites: List<&2, Site>, +bangs: List<&2, Bang>, +depth: U32}

# Keys
# ----
#
# Composite keys as strings that compare as Haskell compares the tuples:
# every string ends in a character below any a name holds, numbers are
# zero-padded, and a Maybe is "0" or "1" and its value.

def end() -> String:
  SCon{Chr{1}, SNil{}}

def key.str(s: String) -> String:
  s ++ end()

def key.pad(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+k:
      key.pad(k, SCon{'0', s})

def key.u32(+n: U32) -> String:
  +s = U32.show(n)
  key.pad(Nat.sub(10n, String.length(s)), s)

def key.def(d: Def) -> String:
  match d:
    case Def{m, n}:
      key.str(m) ++ key.str(n)

def key.visit(+d: Def, +level: U32) -> String:
  key.def(d) ++ key.u32(level)

def key.binding(b: B) -> String:
  match b:
    case B{owner, name, level}:
      key.def(owner) ++ key.str(name)

# Where a site is written (SourceRef): file, line, column and offset, or a
# label for a location that is no source span; its key orders as the
# Haskell record does (file, line, column, offset, label; Nothing first).
# A file of "" is Haskell's Nothing.
def key.file(file: String) -> String:
  match file:
    case SNil{}:
      "0"
    case SCon{c, t}:
      "1" ++ key.str(SCon{c, t})

def key.at(p: L.Pos) -> String:
  match p:
    case L.Pos{line, col, off}:
      "1" ++ key.u32(line) ++ "1" ++ key.u32(col) ++ "1" ++ key.u32(off) ++ "0"

def key.pos(file: String, p: L.Pos) -> String:
  key.file(file) ++ key.at(p)

def key.label(s: String) -> String:
  "0000" ++ "1" ++ key.str(s)

# A location's label when it is no source span (sourceRef's fallbacks).
def label(l: L.Loc) -> String:
  match l:
    case L.Gen{reason}:
      "generated " ++ reason
    case L.Builtin{name}:
      "builtin " ++ name
    case L.RuntimeLoc{}:
      "runtime"
    case L.DecompiledLoc{}:
      "decompiled"
    case _:
      "unknown"

def key.loc(l: L.Loc) -> String:
  match l:
    case L.Src{file, start, stop}:
      key.pos(file, start)
    case L.GenIn{reason, parent}:
      key.loc(parent)
    case other:
      key.label(label(other))

# renderSource
def show.file(file: String) -> String:
  match file:
    case SNil{}:
      "<source>"
    case SCon{c, t}:
      SCon{c, t}

def show.at(p: L.Pos) -> String:
  match p:
    case L.Pos{line, col, off}:
      U32.show(line) ++ ":" ++ U32.show(col)

def show.pos(file: String, p: L.Pos) -> String:
  show.file(file) ++ ":" ++ show.at(p)

def show.loc(l: L.Loc) -> String:
  match l:
    case L.Src{file, start, stop}:
      show.pos(file, start)
    case L.GenIn{reason, parent}:
      show.loc(parent)
    case other:
      label(other)

# renderDef
def show.def(d: Def) -> String:
  match d:
    case Def{m, n}:
      m ++ "." ++ n

# renderBinding
def show.binding(b: B) -> String:
  match b:
    case B{owner, name, level}:
      show.def(owner) ++ "." ++ name

# Name sets and maps
# ------------------

def has(s: Set(), +n: String) -> Bool:
  Pair.snd(Set(), Bool, Set.has(s, n))

def look.got(r: Map<&2, DI> & Maybe<&2, DI>) -> Maybe<&2, DI>:
  (m, v) = r
  v

def look(m: Map<&2, DI>, +n: String) -> Maybe<&2, DI>:
  look.got(Map.pop(&2, DI, m, n))

def bound.got(r: Map<&2, B> & Maybe<&2, B>) -> Maybe<&2, B>:
  (m, v) = r
  v

def bound(m: Map<&2, B>, +n: String) -> Maybe<&2, B>:
  bound.got(Map.pop(&2, B, m, n))

# A name's definition: a local one shadows a global one (auptEnv).
def def.of(+ls: Map<&2, DI>, +gs: Map<&2, DI>, +n: String) -> Maybe<&2, DI>:
  Maybe.or(&2, DI, look(ls, n), look(gs, n))

# The terms' shapes
# -----------------

# A definition's leading parameters and the body under them.
type Lams is Data:
  Lams{+params: List<&2, String>, +body: S.Surf}

def lams.go(t: S.Surf, +ps: List<&2, String>) -> Lams:
  match t:
    case S.SLam{loc, v, body}:
      lams.go(body, L.Name.text(v) <> ps)
    case other:
      Lams{List.reverse(&2, String, ps), other}

# collectLams
def lams(t: S.Surf) -> Lams:
  lams.go(t, [])

# An application's head and its arguments, first first.
type Sp is Data:
  Sp{+head: S.Surf, +args: List<&2, S.Surf>}

def spine.go(t: S.Surf, +args: List<&2, S.Surf>) -> Sp:
  match t:
    case S.SApp{loc, f, x}:
      spine.go(f, x <> args)
    case other:
      Sp{other, args}

# spine
def spine(t: S.Surf) -> Sp:
  spine.go(t, [])

def bind.names(bs: List<&2, S.Bind>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          L.Name.text(name) <> bind.names(rest)

def alt.bodies(alts: List<&2, S.Alt>) -> List<&2, S.Surf>:
  match alts:
    case Nil{}:
      []
    case Con{a, rest}:
      match a:
        case S.Alt{p, body}:
          body <> alt.bodies(rest)

# The subterms the walks read alike, in Haskell's Foldable order (a case's
# patterns are no subterms). Applications, lambdas, lets, recursions and
# variables are read by each walk its own way.
def kids(t: S.Surf) -> List<&2, S.Surf>:
  match t:
    case S.SPair{loc, a, b}:
      [a, b]
    case S.SCheck{loc, a, b}:
      [a, b]
    case S.SIte{loc, i, a, b}:
      [i, a, b]
    case S.SLeft{loc, x}:
      [x]
    case S.SRight{loc, x}:
      [x]
    case S.STrace{loc, x}:
      [x]
    case S.SHash{loc, x}:
      [x]
    case S.SList{loc, xs}:
      xs
    case S.SCase{loc, scrut, alts}:
      scrut <> alt.bodies(alts)
    case _:
      []

def max(+a: U32, +b: U32) -> U32:
  U32.max(a, b)

# Parameter offsets (paramOffsets, occDepth, headOffsets)
# -------------------------------------------------------
#
# How deep, in levels, a definition's parameter is used inside its own
# body. Passing an argument to a parameter used one level down puts that
# argument one level down. An application's head, when it names a
# definition not already being summarized, gives its arguments these
# offsets; any other head gives none.

# A head's summary: the names being summarized with it, its parameters
# and its body; or none.
type Hd is Data:
  Hd{+guard: Set(), +params: List<&2, String>, +body: S.Surf}
  NoHd{}

def head.lams(+guard: Set(), +v: String, l: Lams) -> Hd:
  match l:
    case Lams{ps, b}:
      Hd{Set.add(guard, v), ps, b}

def head.def(+guard: Set(), +v: String, d: Maybe<&2, DI>) -> Hd:
  match d:
    case Some{DI{id, body}}:
      head.lams(guard, v, lams(body))
    case None{}:
      NoHd{}

def head.var(+ls: Map<&2, DI>, +gs: Map<&2, DI>, +guard: Set(), +v: String, guarded: Bool) -> Hd:
  match guarded:
    case True{}:
      NoHd{}
    case False{}:
      head.def(guard, v, def.of(ls, gs, v))

def head(+ls: Map<&2, DI>, +gs: Map<&2, DI>, +guard: Set(), h: S.Surf) -> Hd:
  match h:
    case S.SVar{loc, +v}:
      head.var(ls, gs, guard, v, has(guard, v))
    case _:
      NoHd{}

# What occ reads: how deep p is used in t at depth d; the same in a
# lambda's or a let's body (unless it binds p), over a list of terms, over
# an application (its head, then its arguments from the j-th on, under the
# head's offsets) or over a let's values; or the offset a head gives its
# j-th argument, which is how deep its j-th parameter is used.
type OQ is Data:
  OT{+p: String, +d: U32, +t: S.Surf}
  OUnder{+binds: Bool, +p: String, +d: U32, +t: S.Surf}
  OLet{+binds: Bool, +p: String, +d: U32, +bs: List<&2, S.Bind>, +t: S.Surf}
  OTs{+p: String, +d: U32, +ts: List<&2, S.Surf>}
  OApp{+p: String, +d: U32, +sp: Sp}
  OArgs{+p: String, +d: U32, +hd: Hd, +j: Nat, +args: List<&2, S.Surf>}
  OBinds{+p: String, +d: U32, +bs: List<&2, S.Bind>}
  OOff{+hd: Hd, +j: Nat}
  OParam{+pj: Maybe<&2, String>, +t: S.Surf}

def occ.if(used: Bool, +d: U32) -> U32:
  match used:
    case True{}:
      d
    case False{}:
      0

def occ(+fuel: Nat, +ls: Map<&2, DI>, +gs: Map<&2, DI>, +guard: Set(), q: OQ) -> U32:
  match fuel:
    case 0n:
      0
    case 1n+f:
      match q:
        case OT{+p, +d, t}:
          match t:
            case S.SVar{loc, v}:
              occ.if(String.eq(v, p), d)
            case S.SLam{loc, v, b}:
              occ(f, ls, gs, guard, OUnder{String.eq(L.Name.text(v), p), p, d, b})
            case S.SApp{loc, a, b}:
              occ(f, ls, gs, guard, OApp{p, d, spine(S.SApp{loc, a, b})})
            case S.SRec{loc, a, b, c}:
              occ(f, ls, gs, guard, OTs{p, (d + 1 : U32), [a, b, c]})
            case S.SLet{loc, +bs, body}:
              occ(f, ls, gs, guard, OLet{List.contains(~String, ~String.eq, bind.names(bs), p), p, d, bs, body})
            case other:
              occ(f, ls, gs, guard, OTs{p, d, kids(other)})
        case OUnder{binds, +p, +d, t}:
          match binds:
            case True{}:
              0
            case False{}:
              occ(f, ls, gs, guard, OT{p, d, t})
        case OLet{binds, +p, +d, bs, t}:
          match binds:
            case True{}:
              0
            case False{}:
              max(occ(f, ls, gs, guard, OT{p, d, t}), occ(f, ls, gs, guard, OBinds{p, d, bs}))
        case OApp{+p, +d, sp}:
          match sp:
            case Sp{+h, args}:
              max(occ(f, ls, gs, guard, OT{p, d, h}),
                  occ(f, ls, gs, guard, OArgs{p, d, head(ls, gs, guard, h), 0n, args}))
        case OTs{+p, +d, ts}:
          match ts:
            case Nil{}:
              0
            case Con{t, rest}:
              max(occ(f, ls, gs, guard, OT{p, d, t}), occ(f, ls, gs, guard, OTs{p, d, rest}))
        case OArgs{+p, +d, +hd, +j, args}:
          match args:
            case Nil{}:
              0
            case Con{a, rest}:
              max(occ(f, ls, gs, guard, OT{p, (d + occ(f, ls, gs, guard, OOff{hd, j}) : U32), a}),
                  occ(f, ls, gs, guard, OArgs{p, d, hd, 1n+j, rest}))
        case OBinds{+p, +d, bs}:
          match bs:
            case Nil{}:
              0
            case Con{b, rest}:
              match b:
                case S.Bind{name, val}:
                  max(occ(f, ls, gs, guard, OT{p, d, val}), occ(f, ls, gs, guard, OBinds{p, d, rest}))
        case OOff{hd, +j}:
          match hd:
            case NoHd{}:
              0
            case Hd{g, ps, body}:
              occ(f, ls, gs, g, OParam{List.get(&2, String, ps, j), body})
        case OParam{pj, t}:
          match pj:
            case Some{x}:
              occ(f, ls, gs, guard, OT{x, 0, t})
            case None{}:
              0

def fuel() -> Nat:
  U32.to_nat(4294967295)

# The offset the head h gives its j-th argument where the walk is.
def offset(+ls: Map<&2, DI>, +gs: Map<&2, DI>, +h: S.Surf, +j: Nat) -> U32:
  occ(fuel(), ls, gs, Set.new(), OOff{head(ls, gs, Set.new(), h), j})

# The walk
# --------
#
# From main, through every definition it reaches. A definition is entered
# at most once per level, which is what bounds the traversal. The walk is
# a job machine: each job is a term to read, with the local definitions
# and bindings in scope, the definition it belongs to and its level; its
# subterms go on the stack first first, so the state is threaded in the
# order the Haskell's recursion threads it.

type J is Data:
  J{+ls: Map<&2, DI>, +bn: Map<&2, B>, +owner: Def, +d: U32, +t: S.Surf}

# The visited (definition, level) pairs, the sites by key, the bangs by
# binding, and the maximum nesting depth.
type St is Data:
  St{+seen: Set(), +sites: Map<&2, Site>, +bangs: Map<&2, Bang>, +depth: U32}

def site.got(+source: String, +owner: Def, +level: U32, r: Map<&2, Site> & Maybe<&2, Site>) -> Map<&2, Site> & Site:
  (m, s) = r
  match s:
    case Some{Site{src, o, levels}}:
      (m, Site{src, o, Map.set(&2, U32, levels, key.u32(level), level)})
    case None{}:
      (m, Site{source, owner, Map.set(&2, U32, Map.new(&2, U32), key.u32(level), level)})

def site.put(+k: String, r: Map<&2, Site> & Site) -> Map<&2, Site>:
  (m, s) = r
  Map.set(&2, Site, m, k, s)

# A recursion site seen at a level.
def observe(st: St, +owner: Def, +loc: L.Loc, +d: U32) -> St:
  match st:
    case St{seen, sites, bangs, depth}:
      +k = key.loc(loc) ++ key.def(owner)
      St{seen, site.put(k, site.got(show.loc(loc), owner, d, Map.pop(&2, Site, sites, k))), bangs,
         max(depth, (d + 1 : U32))}

def bang.got(+b: B, +k: U32, r: Map<&2, Bang> & Maybe<&2, Bang>) -> Map<&2, Bang>:
  (m, old) = r
  match old:
    case Some{Bang{ob, ok}}:
      Map.set(&2, Bang, m, key.binding(b), Bang{b, max(ok, k)})
    case None{}:
      Map.set(&2, Bang, m, key.binding(b), Bang{b, k})

def below.if(deeper: Bool, +d: U32, +level: U32) -> U32:
  match deeper:
    case True{}:
      (d - level : U32)
    case False{}:
      0

# How far below its binding a use at d is; a use above it counts as none
# (only bindings used below their level are reported).
def below(+d: U32, +level: U32) -> U32:
  below.if((d > level : U32), d, level)

# A use, at d, of a binding in scope.
def bang.at(used: Maybe<&2, B>, st: St, +d: U32) -> St:
  match used:
    case None{}:
      st
    case Some{+b}:
      match st:
        case St{seen, sites, bangs, depth}:
          St{seen, sites, bang.got(b, below(d, B.level(b)), Map.pop(&2, Bang, bangs, key.binding(b))), depth}

# Enter the definition a variable names, once per level: a local one with
# the scope it is used in, a global one with none.
def enter.with(local: Maybe<&2, DI>, global: Maybe<&2, DI>, st: St, +ls: Map<&2, DI>, +bn: Map<&2, B>, +d: U32, +jobs: List<&2, J>) -> St & List<&2, J>:
  match local:
    case Some{DI{+id, body}}:
      match st:
        case St{seen, sites, bangs, depth}:
          (St{Set.add(seen, key.visit(id, d)), sites, bangs, depth}, J{ls, bn, id, d, body} <> jobs)
    case None{}:
      match global:
        case Some{DI{+id, body}}:
          match st:
            case St{seen, sites, bangs, depth}:
              (St{Set.add(seen, key.visit(id, d)), sites, bangs, depth},
               J{Map.new(&2, DI), Map.new(&2, B), id, d, body} <> jobs)
        case None{}:
          (st, jobs)

def enter.if(st: St, +ls: Map<&2, DI>, +gs: Map<&2, DI>, +bn: Map<&2, B>, +d: U32, +v: String, visited: Bool, +jobs: List<&2, J>) -> St & List<&2, J>:
  match visited:
    case True{}:
      (st, jobs)
    case False{}:
      enter.with(look(ls, v), look(gs, v), st, ls, bn, d, jobs)

# The definition a variable would enter (nextOwner).
def next.owner(+owner: Def, local: Maybe<&2, DI>, global: Maybe<&2, DI>) -> Def:
  match local:
    case Some{DI{id, body}}:
      id
    case None{}:
      match global:
        case Some{DI{id, body}}:
          id
        case None{}:
          owner

def seen(st: St, +k: String) -> Bool:
  match st:
    case St{seen, sites, bangs, depth}:
      has(seen, k)

def enter(+st: St, +ls: Map<&2, DI>, +gs: Map<&2, DI>, +bn: Map<&2, B>, +owner: Def, +d: U32, +v: String, +jobs: List<&2, J>) -> St & List<&2, J>:
  enter.if(st, ls, gs, bn, d, v, seen(st, key.visit(next.owner(owner, look(ls, v), look(gs, v)), d)), jobs)

def jobs.at(+ls: Map<&2, DI>, +bn: Map<&2, B>, +owner: Def, +d: U32, ts: List<&2, S.Surf>, +jobs: List<&2, J>) -> List<&2, J>:
  match ts:
    case Nil{}:
      jobs
    case Con{t, rest}:
      J{ls, bn, owner, d, t} <> jobs.at(ls, bn, owner, d, rest, jobs)

# An application's arguments, each at its head's offset for it.
def jobs.args(args: List<&2, S.Surf>, +ls: Map<&2, DI>, +gs: Map<&2, DI>, +bn: Map<&2, B>, +owner: Def, +d: U32, +h: S.Surf, +j: Nat, +jobs: List<&2, J>) -> List<&2, J>:
  match args:
    case Nil{}:
      jobs
    case Con{a, rest}:
      J{ls, bn, owner, (d + offset(ls, gs, h, j) : U32), a} <> jobs.args(rest, ls, gs, bn, owner, d, h, 1n+j, jobs)

# A let binding's identity, qualified by the definition it appears in
# (localDef).
def local.id(owner: Def, +x: String) -> Def:
  match owner:
    case Def{m, n}:
      Def{m, n ++ "." ++ x}

def let.locals(+owner: Def, bs: List<&2, S.Bind>, +ls: Map<&2, DI>) -> Map<&2, DI>:
  match bs:
    case Nil{}:
      ls
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          +x = L.Name.text(name)
          let.locals(owner, rest, Map.set(&2, DI, ls, x, DI{local.id(owner, x), val}))

def let.binds(+owner: Def, +d: U32, bs: List<&2, S.Bind>, +bn: Map<&2, B>) -> Map<&2, B>:
  match bs:
    case Nil{}:
      bn
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          +x = L.Name.text(name)
          let.binds(owner, d, rest, Map.set(&2, B, bn, x, B{owner, x, d}))

# An application: its head first, then its arguments.
def step.app(+gs: Map<&2, DI>, +ls: Map<&2, DI>, +bn: Map<&2, B>, +owner: Def, +d: U32, sp: Sp, +jobs: List<&2, J>) -> List<&2, J>:
  match sp:
    case Sp{+h, args}:
      J{ls, bn, owner, d, h} <> jobs.args(args, ls, gs, bn, owner, d, h, 0n, jobs)

def walk.step(+gs: Map<&2, DI>, st: St, j: J, +jobs: List<&2, J>) -> St & List<&2, J>:
  match j:
    case J{+ls, +bn, +owner, +d, t}:
      match t:
        case S.SRec{+loc, a, b, c}:
          (observe(st, owner, loc, d), jobs.at(ls, bn, owner, (d + 1 : U32), [a, b, c], jobs))
        case S.SApp{loc, a, b}:
          (st, step.app(gs, ls, bn, owner, d, spine(S.SApp{loc, a, b}), jobs))
        case S.SVar{loc, +v}:
          enter(bang.at(bound(bn, v), st, d), ls, gs, bn, owner, d, v, jobs)
        case S.SLam{loc, v, body}:
          +x = L.Name.text(v)
          (st, J{Map.del(&2, DI, ls, x), Map.set(&2, B, bn, x, B{owner, x, d}), owner, d, body} <> jobs)
        case S.SLet{loc, +bs, body}:
          (st, J{let.locals(owner, bs, ls), let.binds(owner, d, bs, bn), owner, d, body} <> jobs)
        case other:
          (st, jobs.at(ls, bn, owner, d, kids(other), jobs))

def walk(fuel: Nat, +gs: Map<&2, DI>, r: St & List<&2, J>) -> St:
  match fuel:
    case 0n:
      match r:
        case (st, jobs):
          st
    case 1n+f:
      match r:
        case (st, jobs):
          match jobs:
            case Nil{}:
              st
            case Con{j, rest}:
              walk(f, gs, walk.step(gs, st, j, rest))

# The modules
# -----------

def global.add(have: Bool, +gs: Map<&2, DI>, +x: String, +di: DI) -> Map<&2, DI>:
  match have:
    case True{}:
      gs
    case False{}:
      Map.set(&2, DI, gs, x, di)

# Every module's bindings by bare name, the first module to bind a name
# keeping it (globalEnv).
def globals.items(+m: String, items: List<&2, S.EItem>, +gs: Map<&2, DI>) -> Map<&2, DI>:
  match items:
    case Nil{}:
      gs
    case Con{item, rest}:
      match item:
        case S.EBind{name, val}:
          +x = L.Name.text(name)
          globals.items(m, rest, global.add(Pair.snd(Map<&2, DI>, Bool, Map.has(&2, DI, gs, x)), gs, x, DI{Def{m, x}, val}))
        case S.EImport{imp}:
          globals.items(m, rest, gs)

def globals(mods: List<&2, Rs.Mod>, +gs: Map<&2, DI>) -> Map<&2, DI>:
  match mods:
    case Nil{}:
      gs
    case Con{md, rest}:
      match md:
        case Rs.Mod{m, items}:
          globals(rest, globals.items(m, items, gs))

def entry.or(here: Bool, a: Maybe<&2, S.Surf>, b: Maybe<&2, S.Surf>) -> Maybe<&2, S.Surf>:
  match here:
    case True{}:
      Maybe.or(&2, S.Surf, a, b)
    case False{}:
      b

def entry.in(items: List<&2, S.EItem>) -> Maybe<&2, S.Surf>:
  match items:
    case Nil{}:
      None{}
    case Con{item, rest}:
      match item:
        case S.EBind{name, val}:
          entry.or(String.eq(L.Name.text(name), "main"), Some{val}, entry.in(rest))
        case S.EImport{imp}:
          entry.in(rest)

# The entry module's main (lookupEntry).
def entry(mods: List<&2, Rs.Mod>, +m: String) -> Maybe<&2, S.Surf>:
  match mods:
    case Nil{}:
      None{}
    case Con{md, rest}:
      match md:
        case Rs.Mod{name, items}:
          entry.or(String.eq(name, m), entry.in(items), entry(rest, m))

# Summing up (summarize)
# ----------------------

def le(a: Sigma<&2, &2, String, _ => Bang>, b: Sigma<&2, &2, String, _ => Bang>) -> Bool:
  match a:
    case (ka, x):
      match b:
        case (kb, y):
          String.is_le(ka, kb)

def bang.key(+bg: Bang) -> String:
  match bg:
    case Bang{b, k}:
      key.u32((4294967295 - k : U32)) ++ key.binding(b)

def bang.keep(below: Bool, +bg: Bang, rest: List<&2, Sigma<&2, &2, String, _ => Bang>>) -> List<&2, Sigma<&2, &2, String, _ => Bang>>:
  match below:
    case True{}:
      (bang.key(bg), bg) <> rest
    case False{}:
      rest

def bang.k(bg: Bang) -> U32:
  match bg:
    case Bang{b, k}:
      k

# The bangs above zero, keyed in report order.
def bang.keyed(bs: List<&2, Sigma<&2, &2, String, _ => Bang>>) -> List<&2, Sigma<&2, &2, String, _ => Bang>>:
  match bs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (k, +bg):
          bang.keep((bang.k(bg) > 0 : U32), bg, bang.keyed(rest))

def unkey(kvs: List<&2, Sigma<&2, &2, String, _ => Bang>>) -> List<&2, Bang>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (k, v):
          v <> unkey(rest)

def site.le(a: Sigma<&2, &2, String, _ => Site>, b: Sigma<&2, &2, String, _ => Site>) -> Bool:
  match a:
    case (ka, x):
      match b:
        case (kb, y):
          String.is_le(ka, kb)

def sites.of(kvs: List<&2, Sigma<&2, &2, String, _ => Site>>) -> List<&2, Site>:
  match kvs:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (k, v):
          v <> sites.of(rest)

# The sites in source order; the bangs above zero, deepest first, then by
# binding.
def summary(st: St) -> Info:
  match st:
    case St{seen, sites, bangs, depth}:
      Info{sites.of(List.sort(~Sigma<&2, &2, String, _ => Site>, ~site.le, Map.to_list(&2, Site, sites))),
           unkey(List.sort(~Sigma<&2, &2, String, _ => Bang>, ~le, bang.keyed(Map.to_list(&2, Bang, bangs)))),
           depth}

def info.main(+mods: List<&2, Rs.Mod>, +m: String, main: Maybe<&2, S.Surf>) -> Result<&2, &2, String, Info>:
  match main:
    case None{}:
      Fail{"no entry definition " ++ m ++ ".main"}
    case Some{body}:
      +owner = {Def{m, "main"} : Def}
      Done{summary(walk(fuel(), globals(mods, Map.new(&2, DI)),
        (St{Set.new(), Map.new(&2, Site), Map.new(&2, Bang), 0},
         [J{Map.new(&2, DI), Map.new(&2, B), owner, 0, body}])))}

# The structural pass over the expanded modules, from the entry module's
# main (levelsInfo).
def info(+mods: List<&2, Rs.Mod>, +m: String) -> Result<&2, &2, String, Info>:
  info.main(mods, m, entry(mods, m))
