import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Parse.bend as P
import ./Expand.bend as E
import ./Resolve.bend as Rs
import ./Desugar.bend as D
import ./Lower.bend as Lw
import ./Split.bend as Sp
import ./Term.bend as T
import ./Text.bend as Tx

# The front end as the command drives it (haskell-final's app/Main.hs
# getModulesFor and Driver.compileModules, up to Term3): load the modules
# the entry needs, parse and expand each, resolve main, desugar, and lower
# it.

# A module's name and text.

type Src is Data:
  Src{+name: String, +text: String}

# Loading (getModulesFor)
# -----------------------

type LSt is Data:
  LQueue{+queue: List<&2, String>, +srcs: List<&2, Src>}
  LCheck{+seen: Bool, +m: String, +queue: List<&2, String>, +srcs: List<&2, Src>}
  LRead{+m: String, +queue: List<&2, String>, +srcs: List<&2, Src>, +r: Result<&2, &2, String, String>}

# Why the front end refused the program: modules that do not parse or
# expand (every one of them), or a main that does not resolve.
type ModErr is Data:
  NoParse{+name: String, +text: String, +e: P.PErr}
  NoExpand{+name: String, +e: E.ExpErr}

type Err is Data:
  Modules{+errs: List<&2, ModErr>}
  Unresolved{+e: Rs.ResErr}

type Mods is Data:
  Mods{+mods: List<&2, Rs.Mod>, +errs: List<&2, ModErr>}

def import.names(items: List<&2, S.Item>) -> List<&2, String>:
  match items:
    case Nil{}:
      []
    case Con{item, rest}:
      match item:
        case S.IImport{imp}:
          match imp:
            case S.Import{loc, m, qual}:
              L.Name.text(m) <> import.names(rest)
        case S.IDef{d}:
          import.names(rest)

# The modules a module imports, by the real parser; one that does not parse
# imports nothing here (compiling it reports the error).
def imports(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> List<&2, String>:
  match r:
    case Fail{e}:
      []
    case Done{items}:
      import.names(items)

def loaded(srcs: List<&2, Src>, +m: String) -> Bool:
  match srcs:
    case Nil{}:
      False{}
    case Con{s, rest}:
      match s:
        case Src{name, text}:
          String.eq(name, m) || loaded(rest, m)

def as.result(r: Result<&1, &1, String, String>) -> Result<&2, &2, String, String>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Done{s}

# Breadth first from the entry, each module once, newest first.
def load(fuel: Nat, st: LSt) -> IO(Result<&1, &1, String, List<&2, Src>>):
  match fuel:
    case 0n:
      IO.pure(Result<&1, &1, String, List<&2, Src>>, Fail{"too many modules"})
    case 1n+f:
      match st:
        case LQueue{queue, +srcs}:
          match queue:
            case Nil{}:
              IO.pure(Result<&1, &1, String, List<&2, Src>>, Done{srcs})
            case Con{+m, rest}:
              load(f, LCheck{loaded(srcs, m), m, rest, srcs})
        case LCheck{seen, +m, queue, srcs}:
          match seen:
            case True{}:
              load(f, LQueue{queue, srcs})
            case False{}:
              do IO<Result<&1, &1, String, List<&2, Src>>>:
                r : Result<&1, &1, String, String> <- Tx.read_file(m ++ ".tel")
                load(f, LRead{m, queue, srcs, as.result(r)})
        case LRead{+m, queue, srcs, r}:
          match r:
            case Fail{e}:
              IO.pure(Result<&1, &1, String, List<&2, Src>>, Fail{m ++ ".tel: " ++ e})
            case Done{+text}:
              load(f, LQueue{List.append(&2, String, queue, imports(P.module(m, text))), Src{m, text} <> srcs})

# The modules the entry module needs, entry included (getModulesFor).
def modules(+entry: String) -> IO(Result<&1, &1, String, List<&2, Src>>):
  load(U32.to_nat(65536), LQueue{[entry], []})

# Compiling
# ---------

def expanded(+name: String, r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) ->
  Result<&2, &2, ModErr, Rs.Mod>:
  match r:
    case Fail{e}:
      Fail{NoExpand{name, e}}
    case Done{items}:
      Done{Rs.Mod{name, items}}

def parsed(+name: String, +text: String, r: Result<&2, &2, P.PErr, List<&2, S.Item>>) ->
  Result<&2, &2, ModErr, Rs.Mod>:
  match r:
    case Fail{e}:
      Fail{NoParse{name, text, e}}
    case Done{items}:
      expanded(name, E.module(items))

# One module parsed and expanded under its name.
def one(s: Src) -> Result<&2, &2, ModErr, Rs.Mod>:
  match s:
    case Src{+name, +text}:
      parsed(name, text, P.module(name, text))

def all.add(r: Result<&2, &2, ModErr, Rs.Mod>, rest: Mods) -> Mods:
  match r:
    case Fail{e}:
      match rest:
        case Mods{mods, errs}:
          Mods{mods, e <> errs}
    case Done{m}:
      match rest:
        case Mods{mods, errs}:
          Mods{m <> mods, errs}

def all(srcs: List<&2, Src>) -> Mods:
  match srcs:
    case Nil{}:
      Mods{[], []}
    case Con{s, rest}:
      all.add(one(s), all(rest))

def re.or(r: Result<&2, &2, Rs.ResErr, T.Term2()>) -> Result<&2, &2, Err, T.C>:
  match r:
    case Fail{e}:
      Fail{Unresolved{e}}
    case Done{t}:
      Done{Sp.split(t)}

def main.or(r: Result<&2, &2, Rs.ResErr, S.Expanded()>) -> Result<&2, &2, Err, S.Desugared()>:
  match r:
    case Fail{e}:
      Fail{Unresolved{e}}
    case Done{t}:
      Done{D.desugar(t)}

# The session's guard
# -------------------
#
# DESIGN §11.10's convention made a rule: main's input refinements, the
# refined bindings of the let main's body opens with, are checked at the
# session boundary. The session runs them, eagerly, on each line it reads
# and before main; not on the opening call, on 0, which is no input. They
# run as a program of their own, the guard: main with its body replaced by
# the refined values, so running it runs exactly those checks and what
# they need.

type Refined is Data:
  Refined{+name: String, +loc: L.Loc}

def refined.add(+name: String, v: S.Desugared(), rest: List<&2, Refined>) -> List<&2, Refined>:
  match v:
    case S.SCheck{+loc, tc, c}:
      Refined{name, loc} <> rest
    case _:
      rest

# The refined bindings among bs.
def refined(bs: List<&2, S.DesugaredBind()>) -> List<&2, Refined>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      match b:
        case S.Bind{name, val}:
          refined.add(L.Name.text(name), val, refined(rest))

# Main's input refinements. The program is lets around main (Resolve's
# main.let, and Desugar's builtins and aliases), and main is `\input ->
# let ... in body`.
def inputs(t: S.Desugared()) -> List<&2, Refined>:
  match t:
    case S.SLet{l, bs, body}:
      inputs(body)
    case S.SLam{a, v, S.SLet{b, binds, body}}:
      refined(binds)
    case _:
      []

# The refined values, as a tuple ending in 0.
def values(rs: List<&2, Refined>, +loc: L.Loc) -> S.Desugared():
  match rs:
    case Nil{}:
      S.SZero{loc}
    case Con{r, rest}:
      match r:
        case Refined{name, l}:
          S.SPair{loc, S.SVar{l, name}, values(rest, loc)}

# The program with main's body replaced by its refined values.
def guarded(t: S.Desugared()) -> S.Desugared():
  match t:
    case S.SLet{l, bs, body}:
      S.SLet{l, bs, guarded(body)}
    case S.SLam{a, v, S.SLet{+b, +binds, body}}:
      S.SLam{a, v, S.SLet{b, binds, values(refined(binds), L.GenIn{"the session's guard", b})}}
    case other:
      other

def guard.if(none: Bool, t: S.Desugared()) -> Maybe<&2, S.Desugared()>:
  match none:
    case True{}:
      None{}
    case False{}:
      Some{guarded(t)}

# The guard, if main has input refinements.
def guard.of(+t: S.Desugared()) -> Maybe<&2, S.Desugared()>:
  guard.if(List.is_empty(&2, Refined, inputs(t)), t)

def located.at(m: Maybe<&2, String>, acc: Set()) -> Set():
  match m:
    case Some{s}:
      Set.add(acc, s)
    case None{}:
      acc

# Where each refinement is, as rendered.
def located(rs: List<&2, Refined>, acc: Set()) -> Set():
  match rs:
    case Nil{}:
      acc
    case Con{r, rest}:
      match r:
        case Refined{name, loc}:
          located(rest, located.at(L.render_compact(loc), acc))

def at.boundary(+locs: Set(), m: Maybe<&2, String>, +site: U32, +acc: Set()) -> Set():
  match m:
    case Some{s}:
      Bool.pick(Set(), Pair.snd(Set(), Bool, Set.has(locs, s)), Set.add(acc, U32.show(site)), acc)
    case None{}:
      acc

# Main's checks the guard runs, by number: those at a refinement's location.
def boundary(t: T.C, +locs: Set(), acc: Set()) -> Set():
  match t:
    case T.CCheck{a, cloc, +site, x, y}:
      boundary(y, locs, boundary(x, locs, at.boundary(locs, L.render_compact(cloc), site, acc)))
    case T.CPair{a, x, y}:
      boundary(y, locs, boundary(x, locs, acc))
    case T.CSetEnv{a, x}:
      boundary(x, locs, acc)
    case T.CDefer{a, fi, x}:
      boundary(x, locs, acc)
    case T.CLeft{a, x}:
      boundary(x, locs, acc)
    case T.CRight{a, x}:
      boundary(x, locs, acc)
    case _:
      acc

# A program as the session runs it: main's Term3; the guard's, if main has
# input refinements; and main's checks the guard runs, by number.
type Program is Data:
  Program{+run: T.C, +guard: Maybe<&2, T.C>, +boundary: Set()}

def guard.term(m: Maybe<&2, S.Desugared()>) -> Result<&2, &2, Err, Maybe<&2, T.C>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{g}:
      do Result<&2, &2, Err, Maybe<&2, T.C>>:
        t : T.C <- re.or(Lw.process(g))
        return Some{t}

def program.of(+d: S.Desugared()) -> Result<&2, &2, Err, Program>:
  do Result<&2, &2, Err, Program>:
    +run : T.C <- re.or(Lw.process(d))
    guard : Maybe<&2, T.C> <- guard.term(guard.of(d))
    return Program{run, guard, boundary(run, located(inputs(d), Set.new()), Set.new())}

# From the parsed modules to the program as the session runs it.
def program(m: Mods, +entry: String) -> Result<&2, &2, Err, Program>:
  match m:
    case Mods{+mods, errs}:
      match errs:
        case Nil{}:
          do Result<&2, &2, Err, Program>:
            t : S.Surf<Empty, Empty, Empty> <- main.or(Rs.main(mods, entry))
            program.of(t)
        case Con{e, rest}:
          Fail{Modules{e <> rest}}

# From the parsed modules to the program's Term3, which EAL certifies and
# the command sizes and runs (compileModules, up to sizing).
def term(m: Mods, +entry: String) -> Result<&2, &2, Err, T.C>:
  match m:
    case Mods{+mods, errs}:
      match errs:
        case Nil{}:
          do Result<&2, &2, Err, T.C>:
            t : S.Surf<Empty, Empty, Empty> <- main.or(Rs.main(mods, entry))
            re.or(Lw.process(t))
        case Con{e, rest}:
          Fail{Modules{e <> rest}}

# Rendering
# ---------

def in.module(+name: String, err: String) -> String:
  "Error in module " ++ name ++ ":\n" ++ err

def render.mod(e: ModErr) -> String:
  match e:
    case NoParse{+name, text, pe}:
      in.module(name, P.render(name, text, pe))
    case NoExpand{+name, ee}:
      in.module(name, E.render(ee))

def render.mods(es: List<&2, ModErr>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, rest}:
      render.mod(e) ++ "\n" ++ render.mods(rest)

# The text the command prints for a refusal: every module's error, one
# after another, or the resolver's (shown, as Haskell shows it, `RE (...)`).
def render(e: Err) -> String:
  match e:
    case Modules{es}:
      render.mods(es)
    case Unresolved{re}:
      "RE (" ++ Rs.render(re) ++ ")"

def rendered(r: Result<&2, &2, Err, T.C>) -> Result<&2, &2, String, T.C>:
  match r:
    case Fail{e}:
      Fail{render(e)}
    case Done{t}:
      Done{t}

# From the modules' texts to Term3, every problem as the text the command
# prints.
def compile(srcs: List<&2, Src>, +entry: String) -> Result<&2, &2, String, T.C>:
  rendered(term(all(srcs), entry))

def rendered.program(r: Result<&2, &2, Err, Program>) -> Result<&2, &2, String, Program>:
  match r:
    case Fail{e}:
      Fail{render(e)}
    case Done{p}:
      Done{p}

# From the modules' texts to the program as the session runs it.
def compile.program(srcs: List<&2, Src>, +entry: String) -> Result<&2, &2, String, Program>:
  rendered.program(program(all(srcs), entry))
