import Base
import ./Text.bend as Tx
import ./Telc.bend as Tc
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
import ./Meter.bend as Mt
import ./Loc.bend as L

# The `telomare` command (haskell-final's app/Main.hs runSized):
#
#   telomare FILE.tel                 run the program on the IC runtime
#   telomare FILE.tel --meter         run it, then report what the run cost
#   telomare FILE.tel --certificate   report what is known without running it
#   telomare FILE.tel --fast [--fuel N]   run it unsized, each iteration
#                                     capped at N interactions (0: no cap)
#   telomare FILE.tel --compile [-o FILE.telc]   compile it once
#   telomare FILE.telc [--meter | --certificate]   run or report that
#
# The two reports are DESIGN.md's (C3, §9): the static report holds the
# iteration counts sizing inferred and the structural nesting reading; the
# meter, the interactions the session spent. IC is the only runtime here, so
# `--ic` is accepted and changes nothing, except that `--ic --certificate`
# (haskell-final's IC space certificate) is refused. `--fast` skips sizing
# and runs on the IC too (C4), every recursion unbounded: nothing proves it
# terminates, so fuel caps each iteration, and its meter adds each
# recursion site's unrolls. `--compile` writes haskell-final's version 4
# artifact (Telc.bend), less its IC certificate; `--ic --compile` is the
# same. haskell-final's --draw-net is not ported. The goldens in
# test/golden check the command (`test/golden/run.sh BIN_DIR check`).

# What to do with the program.
type Act is Data:
  Play{}
  Meter{}
  Report{}
  Compile{}

type Arg is Data:
  AFile{+path: String}
  AIc{}
  AFast{}
  AFuel{}
  AOut{}
  AAct{+act: Act, +flag: String}
  AOld{+flag: String}
  AUnknown{+flag: String}

# --fuel's cap: not given, the next argument, or given.
type Fuel is Data:
  NoFuel{}
  FuelNext{}
  FuelOf{+n: U32}

# --compile's output (-o, --output): not given, the next argument, or given.
type Out is Data:
  NoOut{}
  OutNext{}
  OutTo{+path: String}

# The arguments so far: the action, the flag that chose it ("" for the
# default, a plain run), whether `--ic` and `--fast` were given, the fuel
# cap, the output and, once given, the program; or what is wrong.
type Cmd is Data:
  Cmd{+act: Act, +flag: String, +ic: Bool, +fast: Bool, +fuel: Fuel, +out: Out, +file: Maybe<&2, String>}
  Bad{+msg: String}

def usage() -> String:
  "usage: telomare FILE.tel [--ic | --fast [--fuel N]] [--meter | --certificate | --compile [-o FILE]]"

# The command line
# ----------------

# haskell-final's options that the port leaves out.
def old.flags() -> List<&2, String>:
  ["--draw-net", "--draw-limit"]

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

def arg.compile(+s: String, compile: Bool) -> Arg:
  match compile:
    case True{}:
      AAct{Compile{}, s}
    case False{}:
      arg.report(s, String.eq(s, "--certificate"))

def arg.out(+s: String, out: Bool) -> Arg:
  match out:
    case True{}:
      AOut{}
    case False{}:
      arg.compile(s, String.eq(s, "--compile"))

def arg.fuel(+s: String, fuel: Bool) -> Arg:
  match fuel:
    case True{}:
      AFuel{}
    case False{}:
      arg.out(s, String.eq(s, "-o") || String.eq(s, "--output"))

def arg.fast(+s: String, fast: Bool) -> Arg:
  match fast:
    case True{}:
      AFast{}
    case False{}:
      arg.fuel(s, String.eq(s, "--fuel"))

def arg.ic(+s: String, ic: Bool) -> Arg:
  match ic:
    case True{}:
      AIc{}
    case False{}:
      arg.fast(s, String.eq(s, "--fast"))

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
    case Cmd{act, flag, ic, fast, fuel, out, file}:
      match file:
        case None{}:
          Cmd{act, flag, ic, fast, fuel, out, Some{path}}
        case Some{f}:
          Bad{"telomare: one program at a time\n" ++ usage()}
    case Bad{m}:
      Bad{m}

def act.set(+first: String, +a: Act, +flag: String, +ic: Bool, +fast: Bool, +fuel: Fuel, +out: Out, +file: Maybe<&2, String>, none: Bool) -> Cmd:
  match none:
    case True{}:
      Cmd{a, flag, ic, fast, fuel, out, file}
    case False{}:
      Bad{"telomare: " ++ first ++ " and " ++ flag ++ " are separate actions; give one\n" ++ usage()}

def with.act(c: Cmd, +a: Act, +flag: String) -> Cmd:
  match c:
    case Cmd{act, +first, +ic, +fast, +fuel, +out, +file}:
      act.set(first, a, flag, ic, fast, fuel, out, file, String.is_empty(first))
    case Bad{m}:
      Bad{m}

def with.ic(c: Cmd) -> Cmd:
  match c:
    case Cmd{act, flag, ic, fast, fuel, out, file}:
      Cmd{act, flag, True{}, fast, fuel, out, file}
    case Bad{m}:
      Bad{m}

def with.fast(c: Cmd) -> Cmd:
  match c:
    case Cmd{act, flag, ic, fast, fuel, out, file}:
      Cmd{act, flag, ic, True{}, fuel, out, file}
    case Bad{m}:
      Bad{m}

def with.fuel(c: Cmd, f: Fuel) -> Cmd:
  match c:
    case Cmd{act, flag, ic, fast, fuel, out, file}:
      Cmd{act, flag, ic, fast, f, out, file}
    case Bad{m}:
      Bad{m}

def with.out(c: Cmd, o: Out) -> Cmd:
  match c:
    case Cmd{act, flag, ic, fast, fuel, out, file}:
      Cmd{act, flag, ic, fast, fuel, o, file}
    case Bad{m}:
      Bad{m}

# The number s writes in decimal, n so far (ok: every character a digit).
def digits(s: String, ok: Bool, +n: U32) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      match ok:
        case True{}:
          Some{n}
        case False{}:
          None{}
    case SCon{Chr{+c}, rest}:
      match ok:
        case True{}:
          digits(rest, U32.is_ge(c, 48) && U32.is_le(c, 57), (n * 10 + c - 48 : U32))
        case False{}:
          None{}

def fuel.of(c: Cmd, m: Maybe<&2, U32>) -> Cmd:
  match m:
    case Some{n}:
      with.fuel(c, FuelOf{n})
    case None{}:
      Bad{"telomare: --fuel takes a number of interactions\n" ++ usage()}

def number(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, rest}:
      digits(SCon{c, rest}, True{}, 0)

# The argument after --fuel is its cap.
def fuel.arg(c: Cmd, a: Arg) -> Cmd:
  match a:
    case AFile{s}:
      fuel.of(c, number(s))
    case _:
      Bad{"telomare: --fuel takes a number of interactions\n" ++ usage()}

# The argument after -o is the file --compile writes.
def out.arg(c: Cmd, a: Arg) -> Cmd:
  match a:
    case AFile{s}:
      with.out(c, OutTo{s})
    case _:
      Bad{"telomare: -o takes the name of the file to write\n" ++ usage()}

def with.arg.at(c: Cmd, a: Arg) -> Cmd:
  match a:
    case AFile{+path}:
      with.file(c, path)
    case AIc{}:
      with.ic(c)
    case AFast{}:
      with.fast(c)
    case AFuel{}:
      with.fuel(c, FuelNext{})
    case AOut{}:
      with.out(c, OutNext{})
    case AAct{act, flag}:
      with.act(c, act, flag)
    case AOld{flag}:
      Bad{"telomare: " ++ flag ++ " is not in the Bend port; haskell-final has it"}
    case AUnknown{flag}:
      Bad{"telomare: unknown option " ++ flag ++ "\n" ++ usage()}

# What the next argument is for: anything, --fuel's cap, or -o's file.
type Next is Data:
  Free{}
  ForFuel{}
  ForOut{}

def next.out(o: Out) -> Next:
  match o:
    case OutNext{}:
      ForOut{}
    case _:
      Free{}

def next.of(c: Cmd) -> Next:
  match c:
    case Cmd{act, flag, ic, fast, fuel, out, file}:
      match fuel:
        case FuelNext{}:
          ForFuel{}
        case _:
          next.out(out)
    case Bad{m}:
      Free{}

def with.arg.for(n: Next, c: Cmd, a: Arg) -> Cmd:
  match n:
    case Free{}:
      with.arg.at(c, a)
    case ForFuel{}:
      fuel.arg(c, a)
    case ForOut{}:
      out.arg(c, a)

def with.arg(+c: Cmd, a: Arg) -> Cmd:
  with.arg.for(next.of(c), c, a)

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
  SLine{net: IC.Net, st: Co.D, cost: Ss.Cost, l: Tx.Line}

# How the session runs, and what its meter reports: sized, the
# interactions; unsized (--fast), each recursion site's unrolls too, which
# needs the sites' locations (by token) and the modules (for the
# definitions they are in).
type Run is Data:
  Sized{}
  Unsized{+fuel: U32, +ls: Map<&2, L.Loc>, +mods: List<&2, Rs.Mod>}

def how(r: Run) -> Ss.How:
  match r:
    case Sized{}:
      Ss.Sized{}
    case Unsized{fuel, ls, mods}:
      Ss.Fast{fuel}

def unrolled(r: Run, us: List<&2, IC.Unroll>) -> IO(Unit):
  match r:
    case Sized{}:
      IO.pure(Unit, Unit{})
    case Unsized{fuel, ls, mods}:
      IO.print_err(Mt.unrolls(us, ls, mods))

# What `--meter` reports once the session is over: what the run cost, as
# measured (the interactions, and unsized the unrolls), never a figure the
# port cannot measure honestly.
def metered(meter: Bool, r: Run, c: Ss.Cost) -> IO(Unit):
  match meter:
    case True{}:
      match c:
        case Ss.Cost{spent, us}:
          do IO<Unit>:
            IO.print_err("IC interactions: " ++ U32.show(spent))
            unrolled(r, us)
    case False{}:
      IO.pure(Unit, Unit{})

def got(+p: IC.Prog, +h: Ss.How, net: IC.Net, i: Tx.In, st: Co.D, c: Ss.Cost, g: Tx.Got) -> IO(SS):
  match g:
    case Tx.GLine{text}:
      IO.pure(SS, STurn{i, Ss.answer(p, h, net, text, st, c)})
    case Tx.GEnd{}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: end of file")
    case Tx.GErr{msg}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: " ++ msg)

def session(fuel: Nat, +p: IC.Prog, +r: Run, +meter: Bool, s: SS) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "telomare: too many iterations")
    case 1n+k:
      match s:
        case STurn{i, t}:
          match t:
            case Ss.Asks{net, display, st, c}:
              do IO<Unit>:
                IO.print(display)
                l : Tx.Line <- Tx.read_line(i)
                session(k, p, r, meter, SLine{net, st, c, l})
            case Ss.Ends{display, c}:
              do IO<Unit>:
                IO.print(display)
                metered(meter, r, c)
            case Ss.Fails{msg, c}:
              IO.die(Unit, 1, "telomare: " ++ msg)
        case SLine{net, st, c, l}:
          match l:
            case Tx.Line{i, g}:
              do IO<Unit>:
                next : SS <- got(p, how(r), net, i, st, c, g)
                session(k, p, r, meter, next)

def play(+p: IC.Prog, +r: Run, meter: Bool) -> IO(Unit):
  session(U32.to_nat(4294967295), p, r, meter, STurn{Tx.Closed{}, Ss.start(p, how(r))})

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
  Unsizable{+f: Sz.SizeFail, +run: T.C}
  Unrunnable{+form: String}

def failed(f: Failure) -> String:
  match f:
    case Unread{msg}:
      "telomare: " ++ msg
    case Refused{e}:
      Fr.render(e)
    case Uncertified{e}:
      EAL.render(e)
    case Unsizable{sf, run}:
      Sz.render(sf, run, budget())
    case Unrunnable{form}:
      "telomare: --fast left " ++ form ++ " in the program (a bug)"

# The program compiled: Term3 as run (for locating its recursion sites)
# and the sized program.
type Compiled is Data:
  Compiled{+run: T.C, +sized: Sz.Sized}

def sized(+run: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Result<&2, &2, Failure, Compiled>:
  match r:
    case Fail{f}:
      Fail{Unsizable{f, run}}
    case Done{s}:
      Done{Compiled{run, s}}

# certifyMain gates the program before its sizing does (Driver's
# compileMainReporting), whatever the action. It certifies the term that is
# sized and run, where haskell-final certified the let-inlined one (DESIGN
# §3, §11.4). Certification runs first and
# sizing after it, never side by side: EAL forks over the bodies, and run
# alongside sizing the two would split the lanes and starve those forks.
def certified(+run: T.C, c: Maybe<&2, EAL.Err>) -> Result<&2, &2, Failure, Compiled>:
  match c:
    case Some{e}:
      Fail{Uncertified{e}}
    case None{}:
      sized(run, Sz.size(budget(), True{}, E.of.term3(run)))

def resolved(r: Result<&2, &2, Fr.Err, T.C>) -> Result<&2, &2, Failure, Compiled>:
  match r:
    case Fail{e}:
      Fail{Refused{e}}
    case Done{+run}:
      certified(run, EAL.certify(Lf.defer.lift(run)))

# The parsed modules compiled: resolved, certified, sized.
def compile(m: Fr.Mods, +entry: String) -> Result<&2, &2, Failure, Compiled>:
  resolved(Fr.term(m, entry))

# Compiling (--compile)
# ---------------------

# Where --compile writes: -o's file, or the program's, .tel made .telc
# (replaceExtension).
def out.path(o: Out, +file: String) -> String:
  match o:
    case OutTo{path}:
      path
    case _:
      Bool.pick(String, String.ends_with(file, ".tel"), file ++ "c", file ++ ".telc")

# The sized program as an artifact: haskell-final's `--ic --compile`, less
# the IC certificate.
def telc.of(+entry: String, srcs: List<&2, Fr.Src>, +counts: List<&2, E.TS>, +run: T.C, +expr: Co.V, info: Result<&2, &2, String, Lv.Info>) -> Tc.Telc:
  Tc.of(entry, srcs, counts, run, expr, Ct.report(counts, run, budget(), info), budget(), Ss.layouts(expr))

def prefix(n: Nat, s: String) -> String:
  match n:
    case 0n:
      ""
    case 1n+k:
      match s:
        case SNil{}:
          ""
        case SCon{c, rest}:
          SCon{c, prefix(k, rest)}

def wrote(+path: String, +n: U32, +hash: String, r: Result<&1, &1, String, Unit>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "telomare: " ++ path ++ ": " ++ e)
    case Done{u}:
      IO.print_err("wrote " ++ path ++ " (" ++ U32.show(n) ++ " nodes, sources " ++ prefix(12n, hash) ++ ")")

def written(+path: String, t: Tc.Telc) -> IO(Unit):
  match t:
    case Tc.Telc{entry, +hash, cert, counts, places, budget, +expr, layouts}:
      do IO<Unit>:
        r : Result<&1, &1, String, Unit> <- Tx.Bytes.write(path, Tc.encode(Tc.Telc{entry, hash, cert, counts, places, budget, expr, layouts}))
        wrote(path, Tc.nodes(expr), hash, r)

# The action, on the compiled program. Running prepares it under the EAL
# capture layouts of the sized term, so closures are copied as EAL
# planned; the static report needs neither, and reads the modules as
# written. Compiling writes the artifact to path.
def acted(r: Result<&2, &2, Failure, Compiled>, act: Act, +mods: List<&2, Rs.Mod>, +entry: String, srcs: List<&2, Fr.Src>, +path: String) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.die(Unit, 1, failed(f))
    case Done{c}:
      match c:
        case Compiled{+run, s}:
          match s:
            case Sz.Sized{+counts, +expr}:
              match act:
                case Play{}:
                  play(Ss.prepared(expr), Sized{}, False{})
                case Meter{}:
                  play(Ss.prepared(expr), Sized{}, True{})
                case Report{}:
                  IO.write(Ct.report(counts, run, budget(), Lv.info(mods, entry)))
                case Compile{}:
                  written(path, telc.of(entry, srcs, counts, run, expr, Lv.info(mods, entry)))

# Unsized (--fast)
# ----------------

# --fast's cap when --fuel is not given: interactions per iteration
# (defaultFastFuel).
def fast.fuel() -> U32:
  16777216

def unrunnable(r: Result<&2, &2, String, Co.V>) -> Result<&2, &2, Failure, Co.V>:
  match r:
    case Fail{form}:
      Fail{Unrunnable{form}}
    case Done{v}:
      Done{v}

# The program to run unsized (compileFast): certified as ever, then, with
# no sizing, every recursion site unbounded.
def unbounded(+run: T.C, c: Maybe<&2, EAL.Err>) -> Result<&2, &2, Failure, Co.V>:
  match c:
    case Some{e}:
      Fail{Uncertified{e}}
    case None{}:
      unrunnable(E.fast(run))

# The program compiled unsized: Term3 as run (for locating its recursion
# sites) and the core to run.
type Unbounded is Data:
  Unbounded{+run: T.C, +expr: Co.V}

def with.run(+run: T.C, r: Result<&2, &2, Failure, Co.V>) -> Result<&2, &2, Failure, Unbounded>:
  match r:
    case Fail{f}:
      Fail{f}
    case Done{v}:
      Done{Unbounded{run, v}}

def fast.resolved(r: Result<&2, &2, Fr.Err, T.C>) -> Result<&2, &2, Failure, Unbounded>:
  match r:
    case Fail{e}:
      Fail{Refused{e}}
    case Done{+run}:
      with.run(run, unbounded(run, EAL.certify(Lf.defer.lift(run))))

# The unsized program run, unguided: EAL's capture layouts are the sized
# term's, and there is none.
def fast.acted(r: Result<&2, &2, Failure, Unbounded>, +meter: Bool, +fuel: U32, +mods: List<&2, Rs.Mod>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.die(Unit, 1, failed(f))
    case Done{u}:
      match u:
        case Unbounded{run, v}:
          play(IC.prepare(v, Map.new(&2, Lf.Shape)), Unsized{fuel, Ct.locs(run, Map.new(&2, L.Loc)), mods}, meter)

def modules.ok(errs: List<&2, Fr.ModErr>) -> Bool:
  match errs:
    case Nil{}:
      True{}
    case Con{e, rest}:
      False{}

# Unsized, the static report has no counts and no EAL check on its path
# (staticReport Nothing Nothing).
def fast.report(+mods: List<&2, Rs.Mod>, errs: List<&2, Fr.ModErr>, +entry: String, ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.write(Ct.report.unsized(Lv.info(mods, entry)))
    case False{}:
      IO.die(Unit, 1, failed(Refused{Fr.Modules{errs}}))

def fast.reported(+entry: String, m: Fr.Mods) -> IO(Unit):
  match m:
    case Fr.Mods{+mods, +errs}:
      fast.report(mods, errs, entry, modules.ok(errs))

def fast.ran(+meter: Bool, +fuel: U32, +entry: String, m: Fr.Mods) -> IO(Unit):
  match m:
    case Fr.Mods{+mods, errs}:
      fast.acted(fast.resolved(Fr.term(Fr.Mods{mods, errs}, entry)), meter, fuel, mods)

def fast.parsed(act: Act, +fuel: U32, +entry: String, m: Fr.Mods) -> IO(Unit):
  match act:
    case Report{}:
      fast.reported(entry, m)
    case Play{}:
      fast.ran(False{}, fuel, entry, m)
    case Meter{}:
      fast.ran(True{}, fuel, entry, m)
    case Compile{}:
      IO.die(Unit, 1, "--compile sizes the program, so it cannot be combined with --fast")

# Compiled programs (.telc)
# -------------------------

def noted(fast: Bool) -> IO(Unit):
  match fast:
    case True{}:
      IO.print_err("note: --fast does not apply to an already-compiled program")
    case False{}:
      IO.pure(Unit, Unit{})

def stale.if(stale: Bool) -> IO(Unit):
  match stale:
    case True{}:
      IO.print_err("note: the sources have changed since this program was compiled; recompile it to pick the changes up")
    case False{}:
      IO.pure(Unit, Unit{})

def stale.of(+hash: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.pure(Unit, Unit{})
    case Done{srcs}:
      stale.if(Bool.not(String.eq(Tc.sources.hash(srcs), hash)))

# An artifact outlives the sources it came from: when they are here and
# hash otherwise now, that is worth saying, never refusing over
# (warnIfStale).
def stale(+entry: String, +hash: String) -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
    stale.of(hash, r)

# A compiled program run, under the capture layouts it stores.
def telc.play(t: Tc.Telc, meter: Bool) -> IO(Unit):
  match t:
    case Tc.Telc{entry, hash, cert, counts, places, budget, +expr, layouts}:
      play(IC.prepare(expr, Tc.shapes(layouts, Map.new(&2, Lf.Shape))), Sized{}, meter)

def telc.cert(t: Tc.Telc) -> IO(Unit):
  match t:
    case Tc.Telc{entry, hash, cert, counts, places, budget, expr, layouts}:
      IO.write(cert)

def telc.acted(act: Act, +path: String, t: Tc.Telc) -> IO(Unit):
  match act:
    case Compile{}:
      IO.die(Unit, 1, path ++ " is already compiled")
    case Report{}:
      telc.cert(t)
    case Play{}:
      telc.play(t, False{})
    case Meter{}:
      telc.play(t, True{})

def telc.decoded(act: Act, +path: String, r: Result<&2, &2, String, Tc.Telc>) -> IO(Unit):
  match r:
    case Fail{msg}:
      IO.die(Unit, 1, path ++ ": " ++ msg)
    case Done{t}:
      match t:
        case Tc.Telc{+entry, +hash, cert, counts, places, budget, expr, layouts}:
          do IO<Unit>:
            stale(entry, hash)
            telc.acted(act, path, Tc.Telc{entry, hash, cert, counts, places, budget, expr, layouts})

def telc.read(act: Act, +path: String, r: Result<&1, &1, String, List<&2, U32>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "telomare: " ++ path ++ ": " ++ e)
    case Done{bs}:
      telc.decoded(act, path, Tc.decode(bs))

# A compiled program: nothing to parse, certify or size (runArtifact).
def telc.run(act: Act, fast: Bool, +path: String) -> IO(Unit):
  do IO<Unit>:
    noted(fast)
    r : Result<&1, &1, String, List<&2, U32>> <- Tx.Bytes.read(path)
    telc.read(act, path, r)

# The source
# ----------

# The modules parsed and expanded once, for both the compiler and the
# static report.
def parsed(act: Act, h: Ss.How, +entry: String, +path: String, srcs: List<&2, Fr.Src>, m: Fr.Mods) -> IO(Unit):
  match h:
    case Ss.Sized{}:
      match m:
        case Fr.Mods{+mods, errs}:
          acted(compile(Fr.Mods{mods, errs}, entry), act, mods, entry, srcs, path)
    case Ss.Fast{fuel}:
      fast.parsed(act, fuel, entry, m)

def loaded(act: Act, h: Ss.How, +entry: String, +path: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, failed(Unread{e}))
    case Done{+srcs}:
      parsed(act, h, entry, path, srcs, Fr.all(srcs))

def source.run(act: Act, h: Ss.How, o: Out, +f: String) -> IO(Unit):
  +entry = base.name(f)
  do IO<Unit>:
    r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
    loaded(act, h, entry, out.path(o, f), r)

def unsized(h: Ss.How) -> Bool:
  match h:
    case Ss.Sized{}:
      False{}
    case Ss.Fast{n}:
      True{}

# A .telc is an artifact, whatever else the command line says.
def file.run(telc: Bool, act: Act, h: Ss.How, o: Out, +f: String) -> IO(Unit):
  match telc:
    case True{}:
      telc.run(act, unsized(h), f)
    case False{}:
      source.run(act, h, o, f)

def run.file(act: Act, h: Ss.How, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  match file:
    case Some{+f}:
      file.run(String.ends_with(f, ".telc"), act, h, o, f)
    case None{}:
      IO.die(Unit, 2, usage())

# haskell-final's `--ic --certificate` was another report, the IC space
# certificate, which the port does not have: refuse it rather than answer
# with the static report.
def run.cmd(act: Act, ic: Bool, h: Ss.How, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  match act:
    case Report{}:
      match ic:
        case True{}:
          IO.die(Unit, 2, "telomare: --ic --certificate (the IC space certificate) is not in the Bend port; haskell-final has it. --certificate alone gives the static report")
        case False{}:
          run.file(Report{}, h, o, file)
    case other:
      run.file(other, h, o, file)

def fast.checked(act: Act, o: Out, file: Maybe<&2, String>, f: Fuel) -> IO(Unit):
  match f:
    case FuelNext{}:
      IO.die(Unit, 2, "telomare: --fuel takes a number of interactions\n" ++ usage())
    case FuelOf{n}:
      run.cmd(act, False{}, Ss.Fast{n}, o, file)
    case NoFuel{}:
      run.cmd(act, False{}, Ss.Fast{fast.fuel()}, o, file)

def sized.checked(act: Act, ic: Bool, o: Out, file: Maybe<&2, String>, f: Fuel) -> IO(Unit):
  match f:
    case NoFuel{}:
      run.cmd(act, ic, Ss.Sized{}, o, file)
    case _:
      IO.die(Unit, 2, "telomare: --fuel caps an unsized run; give it with --fast\n" ++ usage())

def fast.ic(ic: Bool, act: Act, o: Out, file: Maybe<&2, String>, f: Fuel) -> IO(Unit):
  match ic:
    case True{}:
      IO.die(Unit, 2, "telomare: --fast and --ic are separate runtimes; give one\n" ++ usage())
    case False{}:
      fast.checked(act, o, file, f)

# --fast and --ic name two runtimes in haskell-final, --fuel caps only an
# unsized run, and -o names only --compile's output.
def checked(act: Act, ic: Bool, unsized: Bool, f: Fuel, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  match unsized:
    case True{}:
      fast.ic(ic, act, o, file, f)
    case False{}:
      sized.checked(act, ic, o, file, f)

def out.bad(act: Act, o: Out) -> Maybe<&2, String>:
  match act:
    case Compile{}:
      match o:
        case OutNext{}:
          Some{"telomare: -o takes the name of the file to write\n" ++ usage()}
        case _:
          None{}
    case _:
      match o:
        case NoOut{}:
          None{}
        case _:
          Some{"telomare: -o names the file --compile writes; give it with --compile\n" ++ usage()}

def command.out(bad: Maybe<&2, String>, act: Act, ic: Bool, fast: Bool, f: Fuel, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  match bad:
    case Some{msg}:
      IO.die(Unit, 2, msg)
    case None{}:
      checked(act, ic, fast, f, o, file)

def command(c: Cmd) -> IO(Unit):
  match c:
    case Cmd{+act, flag, ic, fast, fuel, +out, file}:
      command.out(out.bad(act, out), act, ic, fast, fuel, out, file)
    case Bad{msg}:
      IO.die(Unit, 2, msg)

# The command line, program name first (IO.args keeps argv[0]).
def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> rest:
      command(args.go(rest, Cmd{Play{}, "", False{}, False{}, NoFuel{}, NoOut{}, None{}}))
    case _:
      command(Cmd{Play{}, "", False{}, False{}, NoFuel{}, NoOut{}, None{}})

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
