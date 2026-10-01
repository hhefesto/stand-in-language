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
# it both ways.

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

# The program's two Term3s: main2Term3's, which EAL certifies, and
# main2Term3let's, which is sized and run.
type Terms is Data:
  Terms{+cert: T.C, +run: T.C}

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

def re.or(r: Result<&2, &2, Rs.ResErr, T.T>) -> Result<&2, &2, Err, T.C>:
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

def lowered(+t: S.Desugared()) -> Result<&2, &2, Err, Terms>:
  do Result<&2, &2, Err, Terms>:
    cert : T.C <- re.or(Lw.process(t))
    run : T.C <- re.or(Lw.process.let(t))
    return Terms{cert, run}

# From the parsed modules to the program's two Term3s (compileModules, up
# to sizing).
def terms(m: Mods, +entry: String) -> Result<&2, &2, Err, Terms>:
  match m:
    case Mods{+mods, errs}:
      match errs:
        case Nil{}:
          do Result<&2, &2, Err, Terms>:
            t : S.Surf<Empty, Empty, Empty> <- main.or(Rs.main(mods, entry))
            lowered(t)
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

def rendered(r: Result<&2, &2, Err, Terms>) -> Result<&2, &2, String, Terms>:
  match r:
    case Fail{e}:
      Fail{render(e)}
    case Done{ts}:
      Done{ts}

# From the modules' texts to Term3, every problem as the text the command
# prints.
def compile(srcs: List<&2, Src>, +entry: String) -> Result<&2, &2, String, Terms>:
  rendered(terms(all(srcs), entry))
