import Base
import ./Text.bend as Tx
import ./Expr.bend as E
import ./Term.bend as T
import ./Front.bend as Fr
import ./Size.bend as Sz
import ./Lift.bend as Lf
import ./EAL.bend as EAL
import ./IC.bend as IC
import ./Session.bend as Ss

# The `telomare` command: `telomare FILE.tel [--ic]` runs the program on the
# IC runtime, as haskell-final's `telomare FILE.tel --ic` did (app/Main.hs
# runSized, Driver.evalLoopIC). IC is the only runtime here, so `--ic` changes
# nothing. The other actions (--certificate, --meter, --compile, .telc
# programs, --draw-net, --fast) are haskell-final's alone. The goldens in
# test/golden check the command (`test/golden/run.sh BIN_DIR check`).

type Arg is Data:
  AFile{+path: String}
  AIc{}
  AOld{+flag: String}
  AUnknown{+flag: String}

# The arguments so far: no program yet, the program, or what is wrong.
type Cmd is Data:
  NoFile{}
  Run{+file: String}
  Bad{+msg: String}

# The loop's state: an iteration to run, its outcome to act on, or the line
# read for the next one (evalSessionCore).
type SS is Type:
  SRun{net: IC.Net, i: Tx.In, input: E.X}
  SOut{net: IC.Net, i: Tx.In, o: Ss.Outcome}
  SLine{net: IC.Net, st: E.X, l: Tx.Line}

def usage() -> String:
  "usage: telomare FILE.tel [--ic]"

# The command line
# ----------------

# haskell-final's options that the port leaves out.
def old.flags() -> List<&2, String>:
  ["--certificate", "--meter", "--compile", "--output", "-o", "--draw-net",
   "--draw-limit", "--fast", "--fuel"]

def arg.flag(+s: String, ic: Bool, old: Bool) -> Arg:
  match ic old:
    case True{} _:
      AIc{}
    case False{} True{}:
      AOld{s}
    case False{} False{}:
      AUnknown{s}

def arg.if(+s: String, flag: Bool) -> Arg:
  match flag:
    case True{}:
      arg.flag(s, String.eq(s, "--ic"), List.contains(~String, ~String.eq, old.flags(), s))
    case False{}:
      AFile{s}

def arg(+s: String) -> Arg:
  arg.if(s, String.starts_with(s, "-"))

def with.file(c: Cmd, +path: String) -> Cmd:
  match c:
    case NoFile{}:
      Run{path}
    case Run{f}:
      Bad{"telomare: one program at a time\n" ++ usage()}
    case Bad{m}:
      Bad{m}

# A compiled program (haskell-final's --compile wrote them) is refused.
def with.path(c: Cmd, +path: String, telc: Bool) -> Cmd:
  match telc:
    case True{}:
      Bad{"telomare: " ++ path ++ " is a compiled program, which only haskell-final runs; run the .tel instead"}
    case False{}:
      with.file(c, path)

def with.arg(c: Cmd, a: Arg) -> Cmd:
  match a:
    case AFile{+path}:
      with.path(c, path, String.ends_with(path, ".telc"))
    case AIc{}:
      c
    case AOld{flag}:
      Bad{"telomare: " ++ flag ++ " is not in the Bend port, which only runs programs; haskell-final has it"}
    case AUnknown{flag}:
      Bad{"telomare: unknown option " ++ flag ++ "\n" ++ usage()}

def args.go(xs: List<String>, c: Cmd) -> Cmd:
  match xs:
    case Nil{}:
      match c:
        case NoFile{}:
          Bad{usage()}
        case other:
          other
    case Con{x, rest}:
      args.go(rest, with.arg(c, arg(x)))

# The module a path names (takeBaseName): its last component, less the
# extension.
def last.part(s: String, cur: String) -> String:
  match s:
    case SNil{}:
      cur
    case SCon{Chr{47}, t}:
      last.part(t, SNil{})
    case SCon{c, t}:
      last.part(t, SCon{c, cur})

def drop.ext(rev: String, +whole: String) -> String:
  match rev:
    case SNil{}:
      whole
    case SCon{Chr{46}, t}:
      String.reverse(t)
    case SCon{c, t}:
      drop.ext(t, whole)

def base.name.rev(+rev: String) -> String:
  drop.ext(rev, String.reverse(rev))

def base.name(file: String) -> String:
  base.name.rev(last.part(file, SNil{}))

# The session
# -----------

def ran(i: Tx.In, r: IC.Run) -> SS:
  match r:
    case IC.Run{net, out, spent}:
      SOut{net, i, Ss.outcome(out)}

def got(net: IC.Net, i: Tx.In, st: E.X, g: Tx.Got) -> IO(SS):
  match g:
    case Tx.GLine{text}:
      IO.pure(SS, SRun{net, i, E.XPair{E.of.string(text), st}})
    case Tx.GEnd{}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: end of file")
    case Tx.GErr{msg}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: " ++ msg)

def session(fuel: Nat, +p: IC.Prog, s: SS) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "telomare: too many iterations")
    case 1n+k:
      match s:
        case SRun{net, i, input}:
          session(k, p, ran(i, IC.run(p, net, input, IC.default.fuel())))
        case SOut{net, i, o}:
          match o:
            case Ss.Continue{display, st}:
              do IO<Unit>:
                IO.print(display)
                l : Tx.Line <- Tx.read_line(i)
                session(k, p, SLine{net, st, l})
            case Ss.Stop{display}:
              IO.print(display)
            case Ss.Crash{msg}:
              IO.die(Unit, 1, "telomare: " ++ msg)
        case SLine{net, st, l}:
          match l:
            case Tx.Line{i, g}:
              do IO<Unit>:
                next : SS <- got(net, i, st, g)
                session(k, p, next)

# The first iteration runs on 0.
def play(+p: IC.Prog) -> IO(Unit):
  session(U32.to_nat(4294967295), p, SRun{IC.net.new(p), Tx.Closed{}, E.XZero{}})

# The pipeline
# ------------

# The program ready to run: sized, then prepared under EAL's guidance.
def ready(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Result<&2, &2, Sz.SizeFail, IC.Prog>:
  match r:
    case Fail{f}:
      Fail{f}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          Done{Ss.prepared(expr)}

def sized(+run: T.C, r: Result<&2, &2, Sz.SizeFail, IC.Prog>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.die(Unit, 1, Sz.render(f, run, 65536))
    case Done{p}:
      play(p)

# certifyMain gates the program before its sizing does (Driver's
# compileMainReporting).
def certified(+run: T.C, c: Maybe<&2, EAL.Err>) -> IO(Unit):
  match c:
    case Some{e}:
      IO.die(Unit, 1, EAL.render(e))
    case None{}:
      sized(run, ready(Sz.size(65536, True{}, E.of.term3(run))))

# The certification, then the sized program. EAL forks over the bodies
# inside each; run side by side, the two would split the lanes between
# them and starve those forks.
def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, +run}:
          certified(run, EAL.certify(Lf.defer.lift(cert)))

def loaded(+entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "telomare: " ++ e)
    case Done{srcs}:
      compiled(Fr.compile(srcs, entry))

def command(c: Cmd) -> IO(Unit):
  match c:
    case Run{file}:
      +entry = base.name(file)
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, r)
    case Bad{msg}:
      IO.die(Unit, 2, msg)
    case NoFile{}:
      IO.die(Unit, 2, usage())

# The command line, program name first (IO.args keeps argv[0]).
def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> rest:
      command(args.go(rest, NoFile{}))
    case _:
      command(NoFile{})

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
