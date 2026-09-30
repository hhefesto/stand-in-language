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

type Mods is Data:
  Mods{+mods: List<&2, Rs.Mod>, +errs: List<&2, String>}

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

def in.module(+name: String, err: String) -> String:
  "Error in module " ++ name ++ ":\n" ++ err

def expanded(+name: String, r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) ->
  Result<&2, &2, String, Rs.Mod>:
  match r:
    case Fail{e}:
      Fail{in.module(name, E.render(e))}
    case Done{items}:
      Done{Rs.Mod{name, items}}

def parsed(+name: String, +text: String, r: Result<&2, &2, P.PErr, List<&2, S.Item>>) ->
  Result<&2, &2, String, Rs.Mod>:
  match r:
    case Fail{e}:
      Fail{in.module(name, P.render(name, text, e))}
    case Done{items}:
      expanded(name, E.module(items))

# One module parsed and expanded under its name.
def one(s: Src) -> Result<&2, &2, String, Rs.Mod>:
  match s:
    case Src{+name, +text}:
      parsed(name, text, P.module(name, text))

def all.add(r: Result<&2, &2, String, Rs.Mod>, rest: Mods) -> Mods:
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

# The Haskell shows a resolver error as `RE (...)`.
def re(e: Rs.ResErr) -> String:
  "RE (" ++ Rs.render(e) ++ ")"

def re.or(r: Result<&2, &2, Rs.ResErr, T.T>) -> Result<&2, &2, String, T.C>:
  match r:
    case Fail{e}:
      Fail{re(e)}
    case Done{t}:
      Done{Sp.split(t)}

def main.or(r: Result<&2, &2, Rs.ResErr, S.Surf>) -> Result<&2, &2, String, S.Surf>:
  match r:
    case Fail{e}:
      Fail{re(e)}
    case Done{t}:
      Done{D.desugar(t)}

def terms(+t: S.Surf) -> Result<&2, &2, String, Terms>:
  do Result<&2, &2, String, Terms>:
    cert : T.C <- re.or(Lw.process(t))
    run : T.C <- re.or(Lw.process.let(t))
    return Terms{cert, run}

def unlines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      x ++ "\n" ++ unlines(rest)

def compile.mods(m: Mods, +entry: String) -> Result<&2, &2, String, Terms>:
  match m:
    case Mods{+mods, errs}:
      match errs:
        case Nil{}:
          do Result<&2, &2, String, Terms>:
            t : S.Surf <- main.or(Rs.main(mods, entry))
            terms(t)
        case Con{e, rest}:
          Fail{unlines(e <> rest)}

# From the modules' texts to Term3, every problem as the text the command
# prints (compileModules, up to sizing).
def compile(srcs: List<&2, Src>, +entry: String) -> Result<&2, &2, String, Terms>:
  compile.mods(all(srcs), entry)
