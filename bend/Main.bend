import Base
import ./Text.bend as Tx
import ./Expr.bend as E
import ./Core.bend as Co
import ./Term.bend as T
import ./Front.bend as Fr
import ./Size.bend as Sz
import ./Lift.bend as Lf
import ./EAL.bend as EAL
import ./IC.bend as IC
import ./Session.bend as Ss
import ./Resolve.bend as Rs
import ./Levels.bend as Lv
import ./Certificate.bend as Ct

# The `telomare` command (haskell-final's app/Main.hs runSized):
#
#   telomare FILE.tel                 run the program on the IC runtime
#   telomare FILE.tel --meter         run it, then report what the run cost
#   telomare FILE.tel --certificate   report what is known without running it
#
# The two reports are DESIGN.md's (C3, §9): the static report holds the
# iteration counts sizing inferred and the structural nesting reading; the
# meter, the interactions the session spent. IC is the only runtime here, so
# `--ic` is accepted and changes nothing, except that `--ic --certificate`
# (haskell-final's IC space certificate) is refused. haskell-final's other
# actions (--compile and .telc programs, --draw-net, --fast) are not
# ported. The goldens in test/golden check the command
# (`test/golden/run.sh BIN_DIR check`).

# What to do with the program.
type Act is Data:
  Play{}
  Meter{}
  Report{}

type Arg is Data:
  AFile{+path: String}
  AIc{}
  AAct{+act: Act, +flag: String}
  AOld{+flag: String}
  AUnknown{+flag: String}

# The arguments so far: the action, the flag that chose it ("" for the
# default, a plain run), whether `--ic` was given and, once given, the
# program; or what is wrong.
type Cmd is Data:
  Cmd{+act: Act, +flag: String, +ic: Bool, +file: Maybe<&2, String>}
  Bad{+msg: String}

def usage() -> String:
  "usage: telomare FILE.tel [--ic] [--meter | --certificate]"

# The command line
# ----------------

# haskell-final's options that the port leaves out.
def old.flags() -> List<&2, String>:
  ["--compile", "--output", "-o", "--draw-net", "--draw-limit", "--fast",
   "--fuel"]

def arg.old(+s: String, old: Bool) -> Arg:
  match old:
    case True{}:
      AOld{s}
    case False{}:
      AUnknown{s}

def arg.meter(+s: String, meter: Bool) -> Arg:
  match meter:
    case True{}:
      AAct{Meter{}, s}
    case False{}:
      arg.old(s, List.contains(~String, ~String.eq, old.flags(), s))

def arg.report(+s: String, report: Bool) -> Arg:
  match report:
    case True{}:
      AAct{Report{}, s}
    case False{}:
      arg.meter(s, String.eq(s, "--meter"))

def arg.ic(+s: String, ic: Bool) -> Arg:
  match ic:
    case True{}:
      AIc{}
    case False{}:
      arg.report(s, String.eq(s, "--certificate"))

def arg.if(+s: String, flag: Bool) -> Arg:
  match flag:
    case True{}:
      arg.ic(s, String.eq(s, "--ic"))
    case False{}:
      AFile{s}

def arg(+s: String) -> Arg:
  arg.if(s, String.starts_with(s, "-"))

def with.file(c: Cmd, +path: String) -> Cmd:
  match c:
    case Cmd{act, flag, ic, file}:
      match file:
        case None{}:
          Cmd{act, flag, ic, Some{path}}
        case Some{f}:
          Bad{"telomare: one program at a time\n" ++ usage()}
    case Bad{m}:
      Bad{m}

def act.set(+first: String, +a: Act, +flag: String, +ic: Bool, +file: Maybe<&2, String>, none: Bool) -> Cmd:
  match none:
    case True{}:
      Cmd{a, flag, ic, file}
    case False{}:
      Bad{"telomare: " ++ first ++ " and " ++ flag ++ " are separate actions; give one\n" ++ usage()}

def with.act(c: Cmd, +a: Act, +flag: String) -> Cmd:
  match c:
    case Cmd{act, +first, +ic, +file}:
      act.set(first, a, flag, ic, file, String.is_empty(first))
    case Bad{m}:
      Bad{m}

# A compiled program (haskell-final's --compile wrote them) is refused.
def with.path(c: Cmd, +path: String, telc: Bool) -> Cmd:
  match telc:
    case True{}:
      Bad{"telomare: " ++ path ++ " is a compiled program, which only haskell-final runs; run the .tel instead"}
    case False{}:
      with.file(c, path)

def with.ic(c: Cmd) -> Cmd:
  match c:
    case Cmd{act, flag, ic, file}:
      Cmd{act, flag, True{}, file}
    case Bad{m}:
      Bad{m}

def with.arg(c: Cmd, a: Arg) -> Cmd:
  match a:
    case AFile{+path}:
      with.path(c, path, String.ends_with(path, ".telc"))
    case AIc{}:
      with.ic(c)
    case AAct{act, flag}:
      with.act(c, act, flag)
    case AOld{flag}:
      Bad{"telomare: " ++ flag ++ " is not in the Bend port; haskell-final has it"}
    case AUnknown{flag}:
      Bad{"telomare: unknown option " ++ flag ++ "\n" ++ usage()}

def args.go(xs: List<String>, c: Cmd) -> Cmd:
  match xs:
    case Nil{}:
      c
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

# Main's side of the session (Session.bend has the iterations): the turn to
# act on, or the line read for the next one.
type SS is Type:
  STurn{i: Tx.In, t: Ss.Turn}
  SLine{net: IC.Net, st: Co.D, spent: U32, l: Tx.Line}

# What `--meter` reports once the session is over: what the run cost, as
# measured (the interactions), never a figure the port cannot measure
# honestly.
def metered(meter: Bool, +spent: U32) -> IO(Unit):
  match meter:
    case True{}:
      IO.print_err("IC interactions: " ++ U32.show(spent))
    case False{}:
      IO.pure(Unit, Unit{})

def got(+p: IC.Prog, net: IC.Net, i: Tx.In, st: Co.D, +spent: U32, g: Tx.Got) -> IO(SS):
  match g:
    case Tx.GLine{text}:
      IO.pure(SS, STurn{i, Ss.answer(p, net, text, st, spent)})
    case Tx.GEnd{}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: end of file")
    case Tx.GErr{msg}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: " ++ msg)

def session(fuel: Nat, +p: IC.Prog, +meter: Bool, s: SS) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "telomare: too many iterations")
    case 1n+k:
      match s:
        case STurn{i, t}:
          match t:
            case Ss.Asks{net, display, st, spent}:
              do IO<Unit>:
                IO.print(display)
                l : Tx.Line <- Tx.read_line(i)
                session(k, p, meter, SLine{net, st, spent, l})
            case Ss.Ends{display, spent}:
              do IO<Unit>:
                IO.print(display)
                metered(meter, spent)
            case Ss.Fails{msg, spent}:
              IO.die(Unit, 1, "telomare: " ++ msg)
        case SLine{net, st, spent, l}:
          match l:
            case Tx.Line{i, g}:
              do IO<Unit>:
                next : SS <- got(p, net, i, st, spent, g)
                session(k, p, meter, next)

def play(+p: IC.Prog, meter: Bool) -> IO(Unit):
  session(U32.to_nat(4294967295), p, meter, STurn{Tx.Closed{}, Ss.start(p)})

# The pipeline (compileModules, then the action)
# ----------------------------------------------

# The sizing budget: unrollings per recursion site.
def budget() -> U32:
  65536

# Why a program did not run (EvalError): one case per stage, each rendered
# once, below, as the text the command prints (DESIGN.md §9).
type Failure is Data:
  Unread{+msg: String}
  Refused{+e: Fr.Err}
  Uncertified{+e: EAL.Err}
  Unsized{+f: Sz.SizeFail, +run: T.C}

def failed(f: Failure) -> String:
  match f:
    case Unread{msg}:
      "telomare: " ++ msg
    case Refused{e}:
      Fr.render(e)
    case Uncertified{e}:
      EAL.render(e)
    case Unsized{sf, run}:
      Sz.render(sf, run, budget())

# The program compiled: Term3 as run (for locating its recursion sites)
# and the sized program.
type Compiled is Data:
  Compiled{+run: T.C, +sized: Sz.Sized}

def sized(+run: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Result<&2, &2, Failure, Compiled>:
  match r:
    case Fail{f}:
      Fail{Unsized{f, run}}
    case Done{s}:
      Done{Compiled{run, s}}

# certifyMain gates the program before its sizing does (Driver's
# compileMainReporting), whatever the action. Certification runs first and
# sizing after it, never side by side: EAL forks over the bodies, and run
# alongside sizing the two would split the lanes and starve those forks.
def certified(+run: T.C, c: Maybe<&2, EAL.Err>) -> Result<&2, &2, Failure, Compiled>:
  match c:
    case Some{e}:
      Fail{Uncertified{e}}
    case None{}:
      sized(run, Sz.size(budget(), True{}, E.of.term3(run)))

def resolved(r: Result<&2, &2, Fr.Err, Fr.Terms>) -> Result<&2, &2, Failure, Compiled>:
  match r:
    case Fail{e}:
      Fail{Refused{e}}
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, +run}:
          certified(run, EAL.certify(Lf.defer.lift(cert)))

# The parsed modules compiled: resolved, certified, sized.
def compile(m: Fr.Mods, +entry: String) -> Result<&2, &2, Failure, Compiled>:
  resolved(Fr.terms(m, entry))

# The action, on the compiled program. Running prepares it under the EAL
# capture layouts of the sized term, so closures are copied as EAL
# planned; the static report needs neither, and reads the modules as
# written.
def acted(r: Result<&2, &2, Failure, Compiled>, act: Act, +mods: List<&2, Rs.Mod>, +entry: String) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.die(Unit, 1, failed(f))
    case Done{c}:
      match c:
        case Compiled{run, s}:
          match s:
            case Sz.Sized{counts, expr}:
              match act:
                case Play{}:
                  play(Ss.prepared(expr), False{})
                case Meter{}:
                  play(Ss.prepared(expr), True{})
                case Report{}:
                  IO.write(Ct.report(counts, run, budget(), Lv.info(mods, entry)))

# The modules parsed and expanded once, for both the compiler and the
# static report.
def parsed(act: Act, +entry: String, m: Fr.Mods) -> IO(Unit):
  match m:
    case Fr.Mods{+mods, errs}:
      acted(compile(Fr.Mods{mods, errs}, entry), act, mods, entry)

def loaded(act: Act, +entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, failed(Unread{e}))
    case Done{srcs}:
      parsed(act, entry, Fr.all(srcs))

def run.file(act: Act, file: Maybe<&2, String>) -> IO(Unit):
  match file:
    case Some{f}:
      +entry = base.name(f)
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(act, entry, r)
    case None{}:
      IO.die(Unit, 2, usage())

# haskell-final's `--ic --certificate` was another report, the IC space
# certificate, which the port does not have: refuse it rather than answer
# with the static report.
def run.cmd(act: Act, ic: Bool, file: Maybe<&2, String>) -> IO(Unit):
  match act:
    case Report{}:
      match ic:
        case True{}:
          IO.die(Unit, 2, "telomare: --ic --certificate (the IC space certificate) is not in the Bend port; haskell-final has it. --certificate alone gives the static report")
        case False{}:
          run.file(Report{}, file)
    case other:
      run.file(other, file)

def command(c: Cmd) -> IO(Unit):
  match c:
    case Cmd{act, flag, ic, file}:
      run.cmd(act, ic, file)
    case Bad{msg}:
      IO.die(Unit, 2, msg)

# The command line, program name first (IO.args keeps argv[0]).
def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> rest:
      command(args.go(rest, Cmd{Play{}, "", False{}, None{}}))
    case _:
      command(Cmd{Play{}, "", False{}, None{}})

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
