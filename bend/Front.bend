import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Parse.bend as P
import ./Mega.bend as Mg
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

# A module is read from the entry's directory, or failing that from the
# working directory (LBeside holds the first try); LRead names the file
# it read.
type LSt is Data:
  LQueue{+queue: List<&2, String>, +srcs: List<&2, Src>}
  LCheck{+seen: Bool, +m: String, +queue: List<&2, String>, +srcs: List<&2, Src>}
  LBeside{+m: String, +queue: List<&2, String>, +srcs: List<&2, Src>, +r: Result<&2, &2, String, String>}
  LRead{+path: String, +m: String, +queue: List<&2, String>, +srcs: List<&2, Src>, +r: Result<&2, &2, String, String>}

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

# Breadth first from the entry, each module once, newest first; dir is the
# entry's directory, with its slash ("" for the working directory).
def load(fuel: Nat, +dir: String, st: LSt) -> IO(Result<&1, &1, String, List<&2, Src>>):
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
              load(f, dir, LCheck{loaded(srcs, m), m, rest, srcs})
        case LCheck{seen, +m, queue, srcs}:
          match seen:
            case True{}:
              load(f, dir, LQueue{queue, srcs})
            case False{}:
              do IO<Result<&1, &1, String, List<&2, Src>>>:
                r : Result<&1, &1, String, String> <- Tx.read_file(dir ++ m ++ ".tel")
                load(f, dir, LBeside{m, queue, srcs, as.result(r)})
        case LBeside{+m, queue, srcs, r}:
          match r:
            case Fail{e}:
              do IO<Result<&1, &1, String, List<&2, Src>>>:
                r2 : Result<&1, &1, String, String> <- Tx.read_file(m ++ ".tel")
                load(f, dir, LRead{m ++ ".tel", m, queue, srcs, as.result(r2)})
            case Done{text}:
              load(f, dir, LRead{dir ++ m ++ ".tel", m, queue, srcs, Done{text}})
        case LRead{path, +m, queue, srcs, r}:
          match r:
            case Fail{e}:
              IO.pure(Result<&1, &1, String, List<&2, Src>>, Fail{path ++ ": " ++ e})
            case Done{+text}:
              load(f, dir, LQueue{List.append(&2, String, queue, imports(P.module(m, text))), Src{m, text} <> srcs})

def dir.rev(rev: String) -> String:
  match rev:
    case SNil{}:
      SNil{}
    case SCon{Chr{47}, t}:
      String.reverse(SCon{Chr{47}, t})
    case SCon{c, t}:
      dir.rev(t)

# A file's directory with its trailing slash, "" for a bare name.
def dir.of(file: String) -> String:
  dir.rev(String.reverse(file))

# The modules the entry module needs, entry included (getModulesFor): the
# entry is read from file, and an import from beside it first, then from
# the working directory (where Prelude.tel lives).
def modules.at(+entry: String, +file: String) -> IO(Result<&1, &1, String, List<&2, Src>>):
  do IO<Result<&1, &1, String, List<&2, Src>>>:
    r : Result<&1, &1, String, String> <- Tx.read_file(file)
    load(U32.to_nat(65536), dir.of(file), LRead{file, entry, [], [], as.result(r)})

# The modules of the entry module M.tel in the working directory.
def modules(+entry: String) -> IO(Result<&1, &1, String, List<&2, Src>>):
  modules.at(entry, entry ++ ".tel")

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

# A desugared term's Term3.
def term.of(+d: S.Desugared()) -> Result<&2, &2, Err, T.C>:
  re.or(Lw.process(d))

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
    case NoParse{+name, +text, pe}:
      in.module(name, Mg.message(Mg.MgModule{}, name, text, P.render(name, text, pe)))
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

