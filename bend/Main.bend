import Base
import ./Text.bend as Tx
import ./Telc.bend as Tc
import ./Expr.bend as E
import ./Core.bend as Co
import ./Term.bend as T
import ./Front.bend as Fr
import ./Size.bend as Sz
import ./Lift.bend as Lf
import ./EALm.bend as EM
import ./IC.bend as IC
import ./Session.bend as Ss
import ./Resolve.bend as Rs
import ./Levels.bend as Lv
import ./Certificate.bend as Ct
import ./Meter.bend as Mt
import ./Loc.bend as L
import ./Reference.bend as Rf
import ./Fast.bend as Fs

# The `telomare` command (master's app/Main.hs):
#
#   telomare FILE.tel                 run the program (the reference evaluator)
#   telomare FILE.tel --ic            run it on the interaction-net runtime
#   telomare FILE.tel --meter         run it, then report what the run cost
#   telomare FILE.tel --certificate   report what is known without running it
#   telomare FILE.tel --fast [--fuel N]   run it unsized, each iteration
#                                     capped at N applications and
#                                     unrollings (0: no cap)
#   telomare FILE.tel --compile [-o FILE.telc]   compile it once
#   telomare FILE.telc [--meter | --certificate]   run or report that
#
# The two reports are DESIGN.md's (C3, §9): the static report holds the
# iteration counts sizing inferred and the structural nesting reading; the
# meter, what the session spent: the reference evaluator's steps and nodes
# built, as master counts them, or with `--ic` the net's interactions. A
# plain run evaluates master's program (Bend/Reference.bend), its input
# prologue first; `--ic` runs the port's (the chains' bottoms erased where the
# erasure checker proves it, the same prologue first), under
# the capture layouts master's EAL gives after sizing (EALm.bend); a main
# with none is refused, as master's withICPlan refuses it. `--ic
# --certificate` is the static report and the port's checks section.
# `--fast` skips sizing and runs master's Fast (Fast.bend), every recursion
# unbounded: nothing proves it terminates, so fuel caps each iteration, and
# its meter counts applications, gates and each recursion site's unrolls.
# `--compile` writes haskell-final's version 4 artifact (Telc.bend), less
# its IC certificate; `--ic --compile` is the same. The command line is
# read as master's optparse parser reads it, errors included (`--draw-net`
# is an invalid option there too). The goldens in test/golden check the command
# (`test/golden/run.sh BIN_DIR check`).

# What to do with the program.
type Act is Data:
  Play{}
  Meter{}
  Report{}
  Compile{}

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
  Help{}

def usage() -> String:
  "usage: telomare FILE.tel [--ic | --fast [--fuel N]] [--meter | --certificate | --compile [-o FILE]]"

# The command line
# ----------------
#
# As master's optparse-applicative parser reads it (app/Main.hs's
# telomareOpts): TELOMARE-FILE, then in any order one action
# (`--compile [-o FILE]`, `--certificate` or `--meter`) and one runtime
# (`--fast [--fuel N]` or `--ic`); `-h` or `--help` shows the help. Its
# errors are optparse's, the usage after them, exit 1.

def usage.block() -> String:
  "Usage: telomare TELOMARE-FILE \n                [--compile [-o|--output FILE] | --certificate | --meter] \n                [--fast [--fuel N] | --ic]\n\n  A simple but robust virtual machine"

def help.text() -> String:
  usage.block() ++ "\n\nAvailable options:\n"
    ++ "  --compile                Size the program once and write it to a .telc file,\n"
    ++ "                           which later runs can use directly\n"
    ++ "  -o,--output FILE         Where to write the compiled program\n"
    ++ "  --certificate            Report each recursion site's inferred iteration count\n"
    ++ "                           and nesting level, then exit\n"
    ++ "  --meter                  Run the program, then report what the run cost\n"
    ++ "  --fast                   Run without sizing: starts immediately, but nothing\n"
    ++ "                           proves the program terminates\n"
    ++ "  --fuel N                 Cap on applications and unrollings per iteration\n"
    ++ "                           under --fast (default 16777216; 0 for no cap)\n"
    ++ "  --ic                     Run on the interaction-combinator runtime, gated on\n"
    ++ "                           the program's EAL certificate and guided by its\n"
    ++ "                           capture layouts\n"
    ++ "  -h,--help                Show this help text"

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

def number(s: String) -> Maybe<&2, U32>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, rest}:
      digits(SCon{c, rest}, True{}, 0)

# The action so far: none; --compile's (given: --compile came, not only
# -o), its output if -o came; --certificate; --meter.
type Ac is Data:
  AcNone{}
  AcCompile{+given: Bool, +out: Maybe<&2, String>}
  AcCert{}
  AcMeter{}

# The runtime so far: none; --fast's (given: --fast came, not only
# --fuel), its fuel if --fuel came; --ic.
type Mo is Data:
  MoNone{}
  MoFast{+given: Bool, +fuel: Maybe<&2, U32>}
  MoIc{}

# An option whose value is the next argument: -o (by the name written) or
# --fuel.
type Wa is Data:
  WaNone{}
  WaOut{+name: String}
  WaFuel{}

# The arguments so far (plain: after `--`, each one positional), or the
# first thing wrong, or help asked for.
type Pa is Data:
  Pa{+file: Maybe<&2, String>, +ac: Ac, +mo: Mo, +wa: Wa, +plain: Bool}
  PaErr{+msg: String}
  PaHelp{}

# What an argument is, decided once.
type Ka is Data:
  KDash{}
  KHelp{}
  KCompile{}
  KOut{+name: String, +v: Maybe<&2, String>}
  KCert{}
  KMeter{}
  KFast{}
  KFuel{+v: Maybe<&2, String>}
  KIc{}
  KBad{}
  KPos{}

def ka.of(+s: String) -> Ka:
  Bool.pick(Ka, String.eq(s, "--"), KDash{},
  Bool.pick(Ka, String.eq(s, "-h") || String.eq(s, "--help"), KHelp{},
  Bool.pick(Ka, String.eq(s, "--compile"), KCompile{},
  Bool.pick(Ka, String.eq(s, "-o"), KOut{"-o", None{}},
  Bool.pick(Ka, String.eq(s, "--output"), KOut{"--output", None{}},
  Bool.pick(Ka, String.starts_with(s, "--output="), KOut{"--output", Some{String.drop(s, 9n)}},
  Bool.pick(Ka, String.starts_with(s, "-o") && Bool.not(String.starts_with(s, "--")), KOut{"-o", Some{String.drop(s, 2n)}},
  Bool.pick(Ka, String.eq(s, "--certificate"), KCert{},
  Bool.pick(Ka, String.eq(s, "--meter"), KMeter{},
  Bool.pick(Ka, String.eq(s, "--fast"), KFast{},
  Bool.pick(Ka, String.eq(s, "--fuel"), KFuel{None{}},
  Bool.pick(Ka, String.starts_with(s, "--fuel="), KFuel{Some{String.drop(s, 7n)}},
  Bool.pick(Ka, String.eq(s, "--ic"), KIc{},
  Bool.pick(Ka, String.starts_with(s, "-"), KBad{}, KPos{}))))))))))))))

def invalid(+x: String) -> Pa:
  PaErr{"Invalid option `" ++ x ++ "'"}

def ac.compile(a: Ac) -> Maybe<&2, Ac>:
  match a:
    case AcNone{}:
      Some{AcCompile{True{}, None{}}}
    case AcCompile{given, o}:
      match given:
        case True{}:
          None{}
        case False{}:
          Some{AcCompile{True{}, o}}
    case _:
      None{}

def ac.only(a: Ac, b: Ac) -> Maybe<&2, Ac>:
  match a:
    case AcNone{}:
      Some{b}
    case _:
      None{}

# -o opens --compile's branch, if no other action came and -o did not.
def ac.out.open(a: Ac) -> Maybe<&2, Ac>:
  match a:
    case AcNone{}:
      Some{AcCompile{False{}, None{}}}
    case AcCompile{given, o}:
      match o:
        case None{}:
          Some{AcCompile{given, None{}}}
        case Some{p}:
          None{}
    case _:
      None{}

def ac.out(a: Ac, +p: String) -> Ac:
  match a:
    case AcCompile{given, o}:
      AcCompile{given, Some{p}}
    case other:
      other

def mo.fast(m: Mo) -> Maybe<&2, Mo>:
  match m:
    case MoNone{}:
      Some{MoFast{True{}, None{}}}
    case MoFast{given, f}:
      match given:
        case True{}:
          None{}
        case False{}:
          Some{MoFast{True{}, f}}
    case MoIc{}:
      None{}

def mo.ic(m: Mo) -> Maybe<&2, Mo>:
  match m:
    case MoNone{}:
      Some{MoIc{}}
    case _:
      None{}

def mo.fuel.open(m: Mo) -> Maybe<&2, Mo>:
  match m:
    case MoNone{}:
      Some{MoFast{False{}, None{}}}
    case MoFast{given, f}:
      match f:
        case None{}:
          Some{MoFast{given, None{}}}
        case Some{n}:
          None{}
    case MoIc{}:
      None{}

def mo.fuel(m: Mo, +n: U32) -> Mo:
  match m:
    case MoFast{given, f}:
      MoFast{given, Some{n}}
    case other:
      other

def pa.fuel(m: Maybe<&2, U32>, +file: Maybe<&2, String>, +ac: Ac, +mo: Mo, plain: Bool, +x: String) -> Pa:
  match m:
    case Some{n}:
      Pa{file, ac, mo.fuel(mo, n), WaNone{}, plain}
    case None{}:
      PaErr{"option --fuel: cannot parse value `" ++ x ++ "'"}

def pa.pos(file: Maybe<&2, String>, +ac: Ac, +mo: Mo, plain: Bool, +x: String) -> Pa:
  match file:
    case None{}:
      Pa{Some{x}, ac, mo, WaNone{}, plain}
    case Some{f}:
      Bool.pick(Pa, String.starts_with(x, "-"), invalid(x), PaErr{"Invalid argument `" ++ x ++ "'"})

def pa.ac(m: Maybe<&2, Ac>, +file: Maybe<&2, String>, +mo: Mo, +x: String) -> Pa:
  match m:
    case Some{a}:
      Pa{file, a, mo, WaNone{}, False{}}
    case None{}:
      invalid(x)

def pa.mo(m: Maybe<&2, Mo>, +file: Maybe<&2, String>, +ac: Ac, +x: String) -> Pa:
  match m:
    case Some{n}:
      Pa{file, ac, n, WaNone{}, False{}}
    case None{}:
      invalid(x)

def pa.out(m: Maybe<&2, Ac>, +n: String, v: Maybe<&2, String>, +file: Maybe<&2, String>, +mo: Mo, +x: String) -> Pa:
  match m:
    case Some{a}:
      match v:
        case Some{p}:
          Pa{file, ac.out(a, p), mo, WaNone{}, False{}}
        case None{}:
          Pa{file, a, mo, WaOut{n}, False{}}
    case None{}:
      invalid(x)

def pa.fuel.opt(m: Maybe<&2, Mo>, v: Maybe<&2, String>, +file: Maybe<&2, String>, +ac: Ac, +x: String) -> Pa:
  match m:
    case Some{o}:
      match v:
        case Some{+p}:
          pa.fuel(number(p), file, ac, o, False{}, p)
        case None{}:
          Pa{file, ac, o, WaFuel{}, False{}}
    case None{}:
      invalid(x)

def pa.ka(k: Ka, +file: Maybe<&2, String>, +ac: Ac, +mo: Mo, +x: String) -> Pa:
  match k:
    case KDash{}:
      Pa{file, ac, mo, WaNone{}, True{}}
    case KHelp{}:
      PaHelp{}
    case KCompile{}:
      pa.ac(ac.compile(ac), file, mo, x)
    case KOut{n, v}:
      pa.out(ac.out.open(ac), n, v, file, mo, x)
    case KCert{}:
      pa.ac(ac.only(ac, AcCert{}), file, mo, x)
    case KMeter{}:
      pa.ac(ac.only(ac, AcMeter{}), file, mo, x)
    case KFast{}:
      pa.mo(mo.fast(mo), file, ac, x)
    case KFuel{v}:
      pa.fuel.opt(mo.fuel.open(mo), v, file, ac, x)
    case KIc{}:
      pa.mo(mo.ic(mo), file, ac, x)
    case KBad{}:
      invalid(x)
    case KPos{}:
      pa.pos(file, ac, mo, False{}, x)

def pa.arg(plain: Bool, +file: Maybe<&2, String>, +ac: Ac, +mo: Mo, +x: String) -> Pa:
  match plain:
    case True{}:
      pa.pos(file, ac, mo, True{}, x)
    case False{}:
      pa.ka(ka.of(x), file, ac, mo, x)

def pa.want(wa: Wa, plain: Bool, +file: Maybe<&2, String>, +ac: Ac, +mo: Mo, +x: String) -> Pa:
  match wa:
    case WaOut{n}:
      Pa{file, ac.out(ac, x), mo, WaNone{}, plain}
    case WaFuel{}:
      pa.fuel(number(x), file, ac, mo, plain, x)
    case WaNone{}:
      pa.arg(plain, file, ac, mo, x)

def pa.step(p: Pa, +x: String) -> Pa:
  match p:
    case Pa{+file, +ac, +mo, wa, plain}:
      pa.want(wa, plain, file, ac, mo, x)
    case PaErr{m}:
      PaErr{m}
    case PaHelp{}:
      PaHelp{}

def pa.go(xs: List<String>, p: Pa) -> Pa:
  match xs:
    case Nil{}:
      p
    case Con{+x, rest}:
      pa.go(rest, pa.step(p, x))

# What is missing at the end, as optparse lists it.
def miss.file(m: Maybe<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      ["TELOMARE-FILE"]
    case Some{f}:
      []

def miss.ac(a: Ac) -> List<&2, String>:
  match a:
    case AcCompile{given, o}:
      match given:
        case True{}:
          []
        case False{}:
          ["--compile"]
    case _:
      []

def miss.mo(m: Mo) -> List<&2, String>:
  match m:
    case MoFast{given, f}:
      match given:
        case True{}:
          []
        case False{}:
          ["--fast"]
    case _:
      []

def act.of(a: Ac) -> Act:
  match a:
    case AcNone{}:
      Play{}
    case AcCompile{g, o}:
      Compile{}
    case AcCert{}:
      Report{}
    case AcMeter{}:
      Meter{}

def out.of(a: Ac) -> Out:
  match a:
    case AcCompile{g, o}:
      match o:
        case Some{p}:
          OutTo{p}
        case None{}:
          NoOut{}
    case _:
      NoOut{}

def is.ic(m: Mo) -> Bool:
  match m:
    case MoIc{}:
      True{}
    case _:
      False{}

def is.fast(m: Mo) -> Bool:
  match m:
    case MoFast{g, f}:
      True{}
    case _:
      False{}

# --fuel N's cap (master's toCap gives 0 as no cap, as FuelOf{0} is).
def fuel.from(m: Mo) -> Fuel:
  match m:
    case MoFast{g, f}:
      match f:
        case Some{n}:
          FuelOf{n}
        case None{}:
          NoFuel{}
    case _:
      NoFuel{}

def pa.missing(ms: List<&2, String>, +file: Maybe<&2, String>, +ac: Ac, +mo: Mo) -> Cmd:
  match ms:
    case Nil{}:
      Cmd{act.of(ac), "", is.ic(mo), is.fast(mo), fuel.from(mo), out.of(ac), file}
    case Con{m, rest}:
      Bad{"Missing: " ++ String.join(Con{m, rest}, " ")}

def pa.wanted(wa: Wa, +file: Maybe<&2, String>, +ac: Ac, +mo: Mo) -> Cmd:
  match wa:
    case WaOut{n}:
      Bad{"The option `" ++ n ++ "` expects an argument."}
    case WaFuel{}:
      Bad{"The option `--fuel` expects an argument."}
    case WaNone{}:
      pa.missing(List.append(&2, String, miss.file(file), List.append(&2, String, miss.ac(ac), miss.mo(mo))), file, ac, mo)

def pa.end(p: Pa) -> Cmd:
  match p:
    case Pa{+file, +ac, +mo, wa, plain}:
      pa.wanted(wa, file, ac, mo)
    case PaErr{m}:
      Bad{m}
    case PaHelp{}:
      Help{}

def args.go(xs: List<String>) -> Cmd:
  pa.end(pa.go(xs, Pa{None{}, AcNone{}, MoNone{}, WaNone{}, False{}}))

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

def got(~rt: Ss.Runner(), +p: Ss.Prog, +h: Ss.How, net: IC.Net, i: Tx.In, st: Co.D, c: Ss.Cost, g: Tx.Got) -> IO(SS):
  match g:
    case Tx.GLine{text}:
      do IO<SS>:
        t : Ss.Turn <- Ss.answer.by(~rt, p, h, net, text, st, c)
        return STurn{i, t}
    case Tx.GEnd{}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: end of file")
    case Tx.GErr{msg}:
      IO.die(SS, 1, "telomare: <stdin>: hGetLine: " ++ msg)

def session(~rt: Ss.Runner(), fuel: Nat, +p: Ss.Prog, +r: Run, +meter: Bool, s: SS) -> IO(Unit):
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
                session(~rt, k, p, r, meter, SLine{net, st, c, l})
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
                next : SS <- got(~rt, p, how(r), net, i, st, c, g)
                session(~rt, k, p, r, meter, next)

def play(~rt: Ss.Runner(), +p: Ss.Prog, +r: Run, meter: Bool) -> IO(Unit):
  do IO<Unit>:
    t : Ss.Turn <- Ss.start.by(~rt, p, how(r))
    session(~rt, U32.to_nat(4294967295), p, r, meter, STurn{Tx.Closed{}, t})

# The reference evaluator's session
# ---------------------------------

# evalLoopCore over the reference evaluator (plainEval, and evalMeter for
# `--meter`): main on 0, then on each line read and the state the last
# iteration left, until the state is 0 or the run fails. Its program is
# master's, so what it prints and counts is master's: an iteration runs main's
# input prologue first, if it has one, except the first, which has no input.
type RS is Type:
  RTurn{i: Tx.In, st: Rf.St, cost: Rf.Cost}
  RPro{i: Tx.In, st: Rf.St, input: Co.D, cost: Rf.Cost}
  RLine{state: Co.D, cost: Rf.Cost, l: Tx.Line}
  REnd{cost: Rf.Cost}

def ref.shown(i: Tx.In, +cost: Rf.Cost, o: Ss.Outcome) -> IO(RS):
  match o:
    case Ss.Continue{display, state}:
      do IO<RS>:
        IO.print(display)
        l : Tx.Line <- Tx.read_line(i)
        return RLine{state, cost, l}
    case Ss.Stop{display}:
      do IO<RS>:
        IO.print(display)
        return REnd{cost}
    case Ss.Crash{msg}:
      IO.die(RS, 1, "telomare: " ++ msg)

def ref.turned(i: Tx.In, cost: Rf.Cost, st: Rf.St) -> IO(RS):
  match st:
    case Rf.SDone{+v, c}:
      ref.shown(i, Rf.cost.plus(cost, c), Ss.value(Ss.fired(v), v))
    case Rf.SErr{msg, c}:
      IO.die(RS, 1, "telomare: Telomare.Meter: " ++ msg)
    case _:
      IO.die(RS, 1, "telomare: the reference evaluator stopped early")

# The prologue's run: an abort there ends the iteration before main starts.
def ref.passed(i: Tx.In, +cost: Rf.Cost, +main: Co.V, +input: Co.D, f: Maybe<&2, Ss.Fired>) -> IO(RS):
  match f:
    case Some{x}:
      ref.shown(i, cost, Ss.Stop{"runtime error:\n" ++ Ss.fired.text(x)})
    case None{}:
      IO.pure(RS, RTurn{i, Rf.iteration(main, input), cost})

def ref.checked(i: Tx.In, cost: Rf.Cost, +main: Co.V, +input: Co.D, st: Rf.St) -> IO(RS):
  match st:
    case Rf.SDone{+v, c}:
      ref.passed(i, Rf.cost.plus(cost, c), main, input, Ss.fired(v))
    case Rf.SErr{msg, c}:
      IO.die(RS, 1, "telomare: Telomare.Meter: " ++ msg)
    case _:
      IO.die(RS, 1, "telomare: the reference evaluator stopped early")

def ref.line(+main: Co.V, p: Maybe<&2, Co.V>, i: Tx.In, +input: Co.D, cost: Rf.Cost) -> IO(RS):
  match p:
    case None{}:
      IO.pure(RS, RTurn{i, Rf.iteration(main, input), cost})
    case Some{+v}:
      IO.pure(RS, RPro{i, Rf.iteration(v, input), input, cost})

def ref.got(+main: Co.V, p: Maybe<&2, Co.V>, state: Co.D, cost: Rf.Cost, l: Tx.Line) -> IO(RS):
  match l:
    case Tx.Line{i, g}:
      match g:
        case Tx.GLine{text}:
          ref.line(main, p, i, Co.DPair{Co.of.string(text), state}, cost)
        case Tx.GEnd{}:
          IO.die(RS, 1, "telomare: <stdin>: hGetLine: end of file")
        case Tx.GErr{msg}:
          IO.die(RS, 1, "telomare: <stdin>: hGetLine: " ++ msg)

# What `--meter` reports, once the session is over (renderMeter).
def ref.metered(meter: Bool, c: Rf.Cost) -> IO(Unit):
  match meter:
    case True{}:
      IO.print_err(Rf.render(c))
    case False{}:
      IO.pure(Unit, Unit{})

def ref.session(fuel: Nat, +main: Co.V, +p: Maybe<&2, Co.V>, +meter: Bool, s: RS) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "telomare: too many iterations")
    case 1n+k:
      match s:
        case RTurn{i, st, cost}:
          do IO<Unit>:
            next : RS <- ref.turned(i, cost, st)
            ref.session(k, main, p, meter, next)
        case RPro{i, st, input, cost}:
          do IO<Unit>:
            next : RS <- ref.checked(i, cost, main, input, st)
            ref.session(k, main, p, meter, next)
        case RLine{state, cost, l}:
          do IO<Unit>:
            next : RS <- ref.got(main, p, state, cost, l)
            ref.session(k, main, p, meter, next)
        case REnd{cost}:
          ref.metered(meter, cost)

def ref.play(+main: Co.V, +p: Maybe<&2, Co.V>, +meter: Bool) -> IO(Unit):
  ref.session(U32.to_nat(4294967295), main, p, meter, RTurn{Tx.Closed{}, Rf.iteration(main, Co.DZero{}), Rf.cost.none()})

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
  Uncertified{+e: EM.Err}
  Unsizable{+f: Sz.SizeFail, +run: T.C}
  Unrunnable{+form: String}

def failed(f: Failure) -> String:
  match f:
    case Unread{msg}:
      "telomare: " ++ msg
    case Refused{e}:
      Fr.render(e)
    case Uncertified{e}:
      EM.render(e)
    case Unsizable{sf, run}:
      Sz.render(sf, run, budget())
    case Unrunnable{form}:
      "telomare: --fast left " ++ form ++ " in the program (a bug)"

# The program compiled: main's Term3 as run (for locating its recursion
# sites), and main sized.
type Compiled is Data:
  Compiled{+run: T.C, +sized: Sz.Sized}

def sized(+run: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Result<&2, &2, Failure, Compiled>:
  match r:
    case Fail{f}:
      Fail{Unsizable{f, run}}
    case Done{s}:
      Done{Compiled{run, s}}

# certifyMain gates the program before its sizing does (Driver's
# compileMainProgram), whatever the action. It certifies the term that is
# sized and run, where haskell-final certified the let-inlined one (DESIGN
# §3, §11.4). Certification runs first and sizing after it, never side by
# side: EAL forks over the bodies, and run alongside sizing the two would split
# the lanes and starve those forks.
def certified(+run: T.C, c: Maybe<&2, EM.Err>, +want: Sz.Want) -> Result<&2, &2, Failure, Compiled>:
  match c:
    case Some{e}:
      Fail{Uncertified{e}}
    case None{}:
      sized(run, Sz.size.checked(budget(), True{}, run, want))

def resolved(r: Result<&2, &2, Fr.Err, T.C>, +want: Sz.Want) -> Result<&2, &2, Failure, Compiled>:
  match r:
    case Fail{e}:
      Fail{Refused{e}}
    case Done{+run}:
      certified(run, EM.certify(Lf.defer.lift(run)), want)

# The parsed modules compiled: resolved, certified, sized.
def compile(m: Fr.Mods, +entry: String, +want: Sz.Want) -> Result<&2, &2, Failure, Compiled>:
  resolved(Fr.term(m, entry), want)

# What an action reads of the compile: a run on the net, the net's report and the
# artifact read it all; a plain run or its meter reads master's program; the
# plain report, the counts.
def wants(ic: Bool, act: Act) -> Sz.Want:
  match ic:
    case True{}:
      Sz.WantNet{}
    case False{}:
      match act:
        case Play{}:
          Sz.WantPlain{}
        case Meter{}:
          Sz.WantPlain{}
        case Report{}:
          Sz.WantCounts{}
        case Compile{}:
          Sz.WantNet{}

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

# The sized program as an artifact: master's `--compile`, less the IC
# certificate.
def telc.of(+entry: String, srcs: List<&2, Fr.Src>, +counts: List<&2, E.TS>, +run: T.C, +expr: Co.V, info: Result<&2, &2, String, Lv.Info>, +checks: Sz.Checks, +plain: Co.V, +p: Maybe<&2, Co.V>, ls: Map<&2, Lf.Shape>) -> Tc.Telc:
  Tc.of(entry, srcs, counts, run, expr, Ct.report(counts, run, budget(), info, checks), budget(), ls, plain, p)

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
    case Tc.Telc{entry, +hash, cert, counts, places, budget, expr, layouts, +plain, prologue}:
      do IO<Unit>:
        r : Result<&1, &1, String, Unit> <- Tx.Bytes.write(path, Tc.encode(Tc.Telc{entry, hash, cert, counts, places, budget, expr, layouts, plain, prologue}))
        wrote(path, Tc.nodes(plain), hash, r)

# withICPlan: a session on the net only under the layouts compiling gave
# main; a main that does not certify after sizing is refused, as master's
# `die`s with the refusal.
def admitted(~rt: Ss.Runner(), r: Result<&2, &2, String, Map<&2, Lf.Shape>>, +expr: Co.V, +p: Maybe<&2, Co.V>, +meter: Bool) -> IO(Unit):
  match r:
    case Fail{why}:
      IO.die(Unit, 1, why)
    case Done{+ls}:
      play(~rt, Ss.session(expr, ls, p), Sized{}, meter)

# A run on the reference evaluator, as master runs one, or with `--ic` on the
# net.
def played(~rt: Ss.Runner(), ic: Bool, +run: T.C, +counts: List<&2, E.TS>, +expr: Co.V, +checks: Sz.Checks, +plain: Co.V, +p: Maybe<&2, Co.V>, +meter: Bool) -> IO(Unit):
  match ic:
    case True{}:
      admitted(~rt, Ss.plan.from(run, counts, Sz.checks.keep(checks), plain, p), expr, p, meter)
    case False{}:
      ref.play(plain, p, meter)

# The action, on the compiled program. Running prepares it under the EAL capture
# layouts of the sized term, so closures are copied as EAL planned; the static
# report needs neither, and reads the modules as written. Compiling writes the
# artifact to path.
def acted(~rt: Ss.Runner(), ic: Bool, r: Result<&2, &2, Failure, Compiled>, act: Act, +mods: List<&2, Rs.Mod>, +entry: String, srcs: List<&2, Fr.Src>, +path: String) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.die(Unit, 1, failed(f))
    case Done{c}:
      match c:
        case Compiled{+run, s}:
          match s:
            case Sz.Sized{+counts, +expr, +checks, +pl, +p}:
              match act:
                case Play{}:
                  played(~rt, ic, run, counts, expr, checks, pl, p, False{})
                case Meter{}:
                  played(~rt, ic, run, counts, expr, checks, pl, p, True{})
                case Report{}:
                  IO.write(Ct.report.of(ic, counts, run, budget(), Lv.info(mods, entry), checks))
                case Compile{}:
                  written(path, telc.of(entry, srcs, counts, run, expr, Lv.info(mods, entry), checks, pl, p, Ss.layouts.of(Ss.plan.from(run, counts, Sz.checks.keep(checks), pl, p))))

# Unsized (--fast)
# ----------------

# --fast's cap when --fuel is not given: applications and unrollings per
# iteration (defaultFastFuel).
def fast.fuel() -> U32:
  16777216

# The program to run unsized (compileFast): certified as ever, then, with
# no sizing, its Term3 as Fast.bend runs it.
def unbounded(+run: T.C, c: Maybe<&2, EM.Err>) -> Result<&2, &2, Failure, T.C>:
  match c:
    case Some{e}:
      Fail{Uncertified{e}}
    case None{}:
      Done{run}

def fast.resolved(r: Result<&2, &2, Fr.Err, T.C>) -> Result<&2, &2, Failure, T.C>:
  match r:
    case Fail{e}:
      Fail{Refused{e}}
    case Done{+run}:
      unbounded(run, EM.certify(Lf.defer.lift(run)))

# runFastLoop: main on 0, then on each line read and the state the last
# iteration left, while there is a line to read; a run that breaks says
# why and ends the session. The meter adds up the iterations'.
type FS is Type:
  FTurn{i: Tx.In, st: Fs.St, m: Fs.Meter}
  FLine{state: Fs.FV, m: Fs.Meter, l: Tx.Line}
  FEnd{m: Fs.Meter}

def fast.cap(+fuel: U32) -> Maybe<&2, U32>:
  Bool.pick(Maybe<&2, U32>, U32.is_zero(fuel), None{}, Some{fuel})

def fast.next(i: Tx.In, +m: Fs.Meter, state: Fs.FV) -> IO(FS):
  match state:
    case Fs.VZero{}:
      IO.pure(FS, FEnd{m})
    case other:
      do IO<FS>:
        l : Tx.Line <- Tx.read_line(i)
        return FLine{other, m, l}

# What an iteration's result says (iterateMain): the display and the state
# to go on with, or the end.
def fast.display(i: Tx.In, +m: Fs.Meter, d: Maybe<&2, String>, state: Fs.FV) -> IO(FS):
  match d:
    case Some{text}:
      do IO<FS>:
        IO.print(text)
        fast.next(i, m, state)
    case None{}:
      do IO<FS>:
        IO.print("error converting display value")
        return FEnd{m}

def fast.value(i: Tx.In, +m: Fs.Meter, v: Fs.FV) -> IO(FS):
  match v:
    case Fs.VZero{}:
      do IO<FS>:
        IO.print("aborted")
        return FEnd{m}
    case Fs.VPair{d, state}:
      fast.display(i, m, Co.to.string.of(Fs.data(d)), state)
    case _:
      do IO<FS>:
        IO.print("error converting iteration value")
        return FEnd{m}

def fast.shown(i: Tx.In, +m: Fs.Meter, v: Fs.FV, f: Maybe<&2, Fs.Found>) -> IO(FS):
  match f:
    case Some{x}:
      match x:
        case Fs.Found{o, msg}:
          do IO<FS>:
            IO.print("runtime error:\nAborted, " ++ Ss.abort.text(o, msg))
            return FEnd{m}
    case None{}:
      fast.value(i, m, v)

def fast.turned(i: Tx.In, +fuel: U32, m: Fs.Meter, st: Fs.St) -> IO(FS):
  match st:
    case Fs.SDone{+v, c, left}:
      fast.shown(i, Fs.meter.plus(m, c), v, Fs.find.abort(v))
    case Fs.SErr{f, c}:
      do IO<FS>:
        IO.print(Fs.fault.text(f, fuel, Mt.commas(fuel)))
        return FEnd{Fs.meter.plus(m, c)}
    case _:
      IO.die(FS, 1, "telomare: the unsized run stopped early")

def fast.got(+prog: Fs.FX, +fuel: U32, state: Fs.FV, m: Fs.Meter, l: Tx.Line) -> FS:
  match l:
    case Tx.Line{i, g}:
      match g:
        case Tx.GLine{text}:
          FTurn{i, Fs.iteration(prog, Fs.VPair{Fs.of.string(text), state}, fast.cap(fuel)), m}
        case _:
          FEnd{m}

def fast.ic.unrolls(us: List<&2, Fs.Unroll>) -> List<&2, IC.Unroll>:
  match us:
    case Nil{}:
      []
    case Con{u, rest}:
      match u:
        case Fs.Unroll{t, n}:
          IC.Unroll{t, n} <> fast.ic.unrolls(rest)

# What `--fast --meter` reports (renderFastMeter).
def fast.metered(meter: Bool, m: Fs.Meter, +ls: Map<&2, L.Loc>, +mods: List<&2, Rs.Mod>) -> IO(Unit):
  match meter:
    case True{}:
      match m:
        case Fs.Meter{a, g, us}:
          IO.print_err("function applications (measured): " ++ Mt.commas(a) ++ "\ngate selections (measured):       "
            ++ Mt.commas(g) ++ "\n" ++ Mt.unrolls(fast.ic.unrolls(us), ls, mods))
    case False{}:
      IO.pure(Unit, Unit{})

def fast.session(n: Nat, +prog: Fs.FX, +fuel: U32, +meter: Bool, +ls: Map<&2, L.Loc>, +mods: List<&2, Rs.Mod>, s: FS) -> IO(Unit):
  match n:
    case 0n:
      IO.die(Unit, 1, "telomare: too many iterations")
    case 1n+k:
      match s:
        case FTurn{i, st, m}:
          do IO<Unit>:
            next : FS <- fast.turned(i, fuel, m, st)
            fast.session(k, prog, fuel, meter, ls, mods, next)
        case FLine{state, m, l}:
          fast.session(k, prog, fuel, meter, ls, mods, fast.got(prog, fuel, state, m, l))
        case FEnd{m}:
          fast.metered(meter, m, ls, mods)

def fast.play(+run: T.C, +fuel: U32, +meter: Bool, +mods: List<&2, Rs.Mod>) -> IO(Unit):
  +prog = Fs.of.term3(run)
  fast.session(U32.to_nat(4294967295), prog, fuel, meter, Ct.locs(run, Map.new(&2, L.Loc)), mods,
    FTurn{Tx.Closed{}, Fs.iteration(prog, Fs.VZero{}, fast.cap(fuel)), Fs.meter.none()})

# The unsized program run (runFast).
def fast.acted(~rt: Ss.Runner(), r: Result<&2, &2, Failure, T.C>, +meter: Bool, +fuel: U32, +mods: List<&2, Rs.Mod>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.die(Unit, 1, failed(f))
    case Done{+run}:
      fast.play(run, fuel, meter, mods)

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

def fast.ran(~rt: Ss.Runner(), +meter: Bool, +fuel: U32, +entry: String, m: Fr.Mods) -> IO(Unit):
  match m:
    case Fr.Mods{+mods, errs}:
      fast.acted(~rt, fast.resolved(Fr.term(Fr.Mods{mods, errs}, entry)), meter, fuel, mods)

def fast.parsed(~rt: Ss.Runner(), act: Act, +fuel: U32, +entry: String, m: Fr.Mods) -> IO(Unit):
  match act:
    case Report{}:
      fast.reported(entry, m)
    case Play{}:
      fast.ran(~rt, False{}, fuel, entry, m)
    case Meter{}:
      fast.ran(~rt, True{}, fuel, entry, m)
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

def stale.from(+entry: String, +hash: String, +beside: String, b: Result<&1, &1, String, String>) -> IO(Unit):
  match b:
    case Done{text}:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules.at(entry, beside)
        stale.of(hash, r)
    case Fail{e}:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        stale.of(hash, r)

# An artifact outlives the sources it came from: when they are here and
# hash otherwise now, that is worth saying, never refusing over
# (warnIfStale). The sources are looked for beside the artifact first, then
# in the working directory.
def stale(+entry: String, +hash: String, +path: String) -> IO(Unit):
  +beside = Fr.dir.of(path) ++ entry ++ ".tel"
  do IO<Unit>:
    b : Result<&1, &1, String, String> <- Tx.read_file(beside)
    stale.from(entry, hash, beside, b)

def stored(+expr: Co.V, ls: List<&2, Tc.Layout>) -> IC.Prog:
  IC.prepare(expr, Tc.shapes(ls, Map.new(&2, Lf.Shape)))

# A compiled program on the net, as compiling prepared it: nothing to collect
# or compile.
def telc.ready(~rt: Ss.Runner(), r: Result<&2, &2, String, Tc.Prepared>, +path: String, +meter: Bool) -> IO(Unit):
  match r:
    case Fail{msg}:
      IO.die(Unit, 1, path ++ ": " ++ msg)
    case Done{x}:
      match x:
        case Tc.Prepared{m, g}:
          play(~rt, Ss.Prog{m, g}, Sized{}, meter)

def telc.plain(r: Result<&2, &2, String, Tc.Plain>, +path: String, +meter: Bool) -> IO(Unit):
  match r:
    case Fail{msg}:
      IO.die(Unit, 1, path ++ ": " ++ msg)
    case Done{x}:
      match x:
        case Tc.Plain{+plain, +p}:
          ref.play(plain, p, meter)

def telc.play(~rt: Ss.Runner(), ic: Bool, h: Tc.Head, +path: String, +meter: Bool) -> IO(Unit):
  match ic:
    case True{}:
      telc.ready(~rt, Tc.ready.of(h), path, meter)
    case False{}:
      telc.plain(Tc.plain.of(h), path, meter)

def telc.cert(h: Tc.Head) -> IO(Unit):
  match h:
    case Tc.Head{entry, hash, cert, counts, places, budget, body}:
      IO.write(cert)

def telc.acted(~rt: Ss.Runner(), act: Act, ic: Bool, +path: String, h: Tc.Head) -> IO(Unit):
  match act:
    case Compile{}:
      IO.die(Unit, 1, path ++ " is already compiled")
    case Report{}:
      telc.cert(h)
    case Play{}:
      telc.play(~rt, ic, h, path, False{})
    case Meter{}:
      telc.play(~rt, ic, h, path, True{})

def telc.decoded(~rt: Ss.Runner(), act: Act, ic: Bool, +path: String, r: Result<&2, &2, String, Tc.Head>) -> IO(Unit):
  match r:
    case Fail{msg}:
      IO.die(Unit, 1, path ++ ": " ++ msg)
    case Done{h}:
      match h:
        case Tc.Head{+entry, +hash, cert, counts, places, budget, body}:
          do IO<Unit>:
            stale(entry, hash, path)
            telc.acted(~rt, act, ic, path, Tc.Head{entry, hash, cert, counts, places, budget, body})

def telc.read(~rt: Ss.Runner(), act: Act, ic: Bool, +path: String, r: Result<&1, &1, String, List<&2, U32>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "telomare: " ++ path ++ ": " ++ e)
    case Done{bs}:
      telc.decoded(~rt, act, ic, path, Tc.load(bs))

# A compiled program: nothing to parse, certify or size (runArtifact).
def telc.run(~rt: Ss.Runner(), act: Act, ic: Bool, fast: Bool, +path: String) -> IO(Unit):
  do IO<Unit>:
    noted(fast)
    r : Result<&1, &1, String, List<&2, U32>> <- Tx.Bytes.read(path)
    telc.read(~rt, act, ic, path, r)

# The source
# ----------

# The modules parsed and expanded once, for both the compiler and the
# static report.
def parsed(~rt: Ss.Runner(), +act: Act, +ic: Bool, h: Ss.How, +entry: String, +path: String, srcs: List<&2, Fr.Src>, m: Fr.Mods) -> IO(Unit):
  match h:
    case Ss.Sized{}:
      match m:
        case Fr.Mods{+mods, errs}:
          acted(~rt, ic, compile(Fr.Mods{mods, errs}, entry, wants(ic, act)), act, mods, entry, srcs, path)
    case Ss.Fast{fuel}:
      fast.parsed(~rt, act, fuel, entry, m)

def loaded(~rt: Ss.Runner(), act: Act, ic: Bool, h: Ss.How, +entry: String, +path: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, failed(Unread{e}))
    case Done{+srcs}:
      parsed(~rt, act, ic, h, entry, path, srcs, Fr.all(srcs))

def source.run(~rt: Ss.Runner(), act: Act, ic: Bool, h: Ss.How, o: Out, +f: String) -> IO(Unit):
  +entry = base.name(f)
  do IO<Unit>:
    r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules.at(entry, f)
    loaded(~rt, act, ic, h, entry, out.path(o, f), r)

def unsized(h: Ss.How) -> Bool:
  match h:
    case Ss.Sized{}:
      False{}
    case Ss.Fast{n}:
      True{}

# A .telc is an artifact, whatever else the command line says.
def file.run(~rt: Ss.Runner(), telc: Bool, act: Act, ic: Bool, h: Ss.How, o: Out, +f: String) -> IO(Unit):
  match telc:
    case True{}:
      telc.run(~rt, act, ic, unsized(h), f)
    case False{}:
      source.run(~rt, act, ic, h, o, f)

def run.file(~rt: Ss.Runner(), act: Act, ic: Bool, h: Ss.How, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  match file:
    case Some{+f}:
      file.run(~rt, String.ends_with(f, ".telc"), act, ic, h, o, f)
    case None{}:
      IO.die(Unit, 2, usage())

def run.cmd(~rt: Ss.Runner(), act: Act, ic: Bool, h: Ss.How, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  run.file(~rt, act, ic, h, o, file)

def fast.checked(~rt: Ss.Runner(), act: Act, o: Out, file: Maybe<&2, String>, f: Fuel) -> IO(Unit):
  match f:
    case FuelNext{}:
      IO.die(Unit, 2, "telomare: --fuel takes a number of interactions\n" ++ usage())
    case FuelOf{n}:
      run.cmd(~rt, act, False{}, Ss.Fast{n}, o, file)
    case NoFuel{}:
      run.cmd(~rt, act, False{}, Ss.Fast{fast.fuel()}, o, file)

def sized.checked(~rt: Ss.Runner(), act: Act, ic: Bool, o: Out, file: Maybe<&2, String>, f: Fuel) -> IO(Unit):
  match f:
    case NoFuel{}:
      run.cmd(~rt, act, ic, Ss.Sized{}, o, file)
    case _:
      IO.die(Unit, 2, "telomare: --fuel caps an unsized run; give it with --fast\n" ++ usage())

def fast.ic(~rt: Ss.Runner(), ic: Bool, act: Act, o: Out, file: Maybe<&2, String>, f: Fuel) -> IO(Unit):
  match ic:
    case True{}:
      IO.die(Unit, 2, "telomare: --fast and --ic are separate runtimes; give one\n" ++ usage())
    case False{}:
      fast.checked(~rt, act, o, file, f)

# --fast and --ic name two runtimes in haskell-final, --fuel caps only an
# unsized run, and -o names only --compile's output.
def checked(~rt: Ss.Runner(), act: Act, ic: Bool, unsized: Bool, f: Fuel, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  match unsized:
    case True{}:
      fast.ic(~rt, ic, act, o, file, f)
    case False{}:
      sized.checked(~rt, act, ic, o, file, f)

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

def command.out(~rt: Ss.Runner(), bad: Maybe<&2, String>, act: Act, ic: Bool, fast: Bool, f: Fuel, o: Out, file: Maybe<&2, String>) -> IO(Unit):
  match bad:
    case Some{msg}:
      IO.die(Unit, 2, msg)
    case None{}:
      checked(~rt, act, ic, fast, f, o, file)

def command(~rt: Ss.Runner(), c: Cmd) -> IO(Unit):
  match c:
    case Cmd{+act, flag, ic, fast, fuel, +out, file}:
      command.out(~rt, out.bad(act, out), act, ic, fast, fuel, out, file)
    case Bad{msg}:
      IO.die(Unit, 1, msg ++ "\n\n" ++ usage.block())
    case Help{}:
      IO.print(help.text())

# The command line, program name first (IO.args keeps argv[0]).
def args(~rt: Ss.Runner(), xs: List<String>) -> IO(Unit):
  match xs:
    case self <> rest:
      command(~rt, args.go(rest))
    case _:
      command(~rt, args.go([]))

def app(~rt: Ss.Runner()) -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(~rt, xs)

# The command, its IC run by IC.run itself. bend/Native.bend's main is the
# same command with the IC's loop in C (bend/effs/ic.c), which gives the
# same runs; the telomare binary is built from it.
def main() -> IO(Unit):
  app(~Ss.run.pure)
