import Base
import ./Expr.bend as E
import ./Core.bend as Co

# The meaning of the core (DESIGN.md §2) as the runtime gives it, and as
# LAWS.bend reads it: the IC's evaluation order over the core forms of
# Expr's X. Every value is computed, once, as the IC speculates it (§7),
# except the branches of the strict if: like the IC since P4, only the
# chosen one runs. Aborted and stuck values are values: they end a run
# only by reaching its result (§5 "applying data is tolerated", §6). It is
# what the IC is tested against (tests/sem.bend) and what the erasure
# checker runs; it runs no user program, so the port still has one runtime
# (C4).
#
# Every evaluation spends fuel, so every run ends: running out is a result.
#
# Beyond the core, for the checker and the laws:
# - XVar is an input position nothing has looked at. Projecting it is the
#   position below (sizing's convention: the left of a 0 is 0); anything
#   that needs its shape stops the run, naming the position (Needs).
# - XCheck and XStub are sizing's erasable sites, kept by the witness
#   (Check.bend): a refinement check, and the rest of a recursion past its
#   chain. Pol says what they mean. Watched, a bottom, and an erasable check
#   that does not pass, are a mark: a value that travels as an aborted one
#   does (whatever is computed from it is the mark), and ends the run
#   (Fired) if it reaches the result. Where none does, the result never
#   depended on what was there, so the program that runs, with the check's
#   value or 0 there, answers the same (LAWS.bend). Erased, they are what
#   runs: the check's value, and 0. Limit: the check's value, and the
#   recursion unbounded, as `--fast` runs it.

# A value. WMark is a watched site's mark.
type W is Data:
  WZero{}
  WPair{+a: W, +b: W}
  WCode{+fi: U32, +body: E.X}
  WGate{}
  WAbort{+at: E.Site}
  WAborted{+at: E.Site, +m: O}
  WStuck{}
  WHole{+p: String}
  WMark{+at: E.Site}

# A value as the session reads it back. A closure shows as its function
# index only.
type O is Data:
  OZero{}
  OPair{+a: O, +b: O}
  OCode{+fi: U32}
  OGate{}
  OAbort{}
  OAborted{+at: E.Site, +m: O}
  OStuck{}
  OHole{+p: String}

type Mode is Data:
  Watch{}
  Erase{}
  Limit{}

# What the erasable sites mean: the mode, and which checks, by number, are
# erasable (every bottom is).
type Pol is Data:
  Pol{+mode: Mode, +checks: List<&2, U32>}

type R is Data:
  Val{+w: W}
  Obs{+o: O}
  Fired{+at: E.Site}
  Needs{+p: String}
  Spent{}

# Whether a result is an answer the fuel did not cut short (for the laws).
def answered(r: R) -> Data:
  match r:
    case Spent{}:
      Empty
    case _:
      Unit

# What to evaluate next. Every step of the evaluator is one of these, and
# a helper that needs no evaluation picks the next one: so each step is a
# value, the evaluator on a job, or a function of the evaluator's results.
type Job is Data:
  JE{+x: E.X, +env: W}
  JPair{+a: E.X, +b: E.X, +env: W}
  JSetE{+y: E.X, +env: W}
  JSet{+r: R}
  JIfE{+s: E.X, +l: E.X, +rt: E.X, +env: W}
  JIf{+r: R, +l: E.X, +rt: E.X, +env: W}
  JLeft{+y: E.X, +env: W}
  JRight{+y: E.X, +env: W}
  JWatch{+site: U32, +tc: E.X, +c: E.X, +env: W}
  JDone{+r: R}

# Sites
# -----

def has(xs: List<&2, U32>, +n: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      U32.is_eq(x, n) || has(rest, n)

def pol.mode(p: Pol) -> Mode:
  match p:
    case Pol{mode, checks}:
      mode

def pol.checks(p: Pol) -> List<&2, U32>:
  match p:
    case Pol{mode, checks}:
      checks

def is.watch(m: Mode) -> Bool:
  match m:
    case Watch{}:
      True{}
    case _:
      False{}

# What a check is: kept, as the program runs it; gone, its value (erased);
# or watched, its value where its test gives 0 and a mark where it does not.
type How is Data:
  Kept{}
  Gone{}
  Watched{}

def how.of(m: Mode, erasable: Bool) -> How:
  match m:
    case Watch{}:
      match erasable:
        case True{}:
          Watched{}
        case False{}:
          Kept{}
    case _:
      match erasable:
        case True{}:
          Gone{}
        case False{}:
          Kept{}

def check.how(+pol: Pol, +site: U32) -> How:
  how.of(pol.mode(pol), has(pol.checks(pol), site))

def stub.of(m: Mode, +tok: U32, env: W) -> Job:
  match m:
    case Watch{}:
      JDone{Val{WMark{E.AtRecursion{tok}}}}
    case Erase{}:
      JDone{Val{WZero{}}}
    case Limit{}:
      JE{E.limit(tok), env}

# The rest of recursion tok, past its chain: a watched bottom, 0 (erased),
# or the recursion unbounded.
def stub.job(+pol: Pol, +tok: U32, env: W) -> Job:
  stub.of(pol.mode(pol), tok, env)

# Steps that need no further evaluation
# -------------------------------------

# What is computed from a mark is the mark.
def used(at: E.Site) -> R:
  Val{WMark{at}}

# A mark in an abort's message, if any.
def mark.in(w: W) -> Maybe<&2, E.Site>:
  match w:
    case WMark{at}:
      Some{at}
    case WPair{a, b}:
      Maybe.or(&2, E.Site, mark.in(a), mark.in(b))
    case _:
      None{}

def marked.or(m: Maybe<&2, E.Site>, r: R) -> R:
  match m:
    case Some{at}:
      Val{WMark{at}}
    case None{}:
      r

def left.of(w: W) -> R:
  match w:
    case WPair{a, b}:
      Val{a}
    case WZero{}:
      Val{WZero{}}
    case WAborted{at, m}:
      Val{WAborted{at, m}}
    case WHole{p}:
      Val{WHole{p ++ "L"}}
    case WMark{at}:
      used(at)
    case _:
      Val{WStuck{}}

def right.of(w: W) -> R:
  match w:
    case WPair{a, b}:
      Val{b}
    case WZero{}:
      Val{WZero{}}
    case WAborted{at, m}:
      Val{WAborted{at, m}}
    case WHole{p}:
      Val{WHole{p ++ "R"}}
    case WMark{at}:
      used(at)
    case _:
      Val{WStuck{}}

# A gate applied to w: the branch selector.
def gate.of(w: W) -> R:
  match w:
    case WZero{}:
      Val{WCode{Co.left.gate.ind(), E.XLeft{E.XEnv{}}}}
    case WPair{a, b}:
      Val{WCode{Co.right.gate.ind(), E.XRight{E.XEnv{}}}}
    case WAborted{at, m}:
      Val{WAborted{at, m}}
    case WHole{p}:
      Needs{p}
    case WMark{at}:
      used(at)
    case _:
      Val{WStuck{}}

def only(data: Bool, o: O) -> O:
  match data:
    case True{}:
      OZero{}
    case False{}:
      o

def read.pair(a: R, b: R) -> R:
  match a:
    case Obs{x}:
      match b:
        case Obs{y}:
          Obs{OPair{x, y}}
        case other:
          other
    case other:
      other

# A value read back in full; under an abort (data) only data counts, and
# anything else reads as 0. A mark that reaches the result fires.
def read(+data: Bool, w: W) -> R:
  match w:
    case WZero{}:
      Obs{OZero{}}
    case WPair{a, b}:
      read.pair(read(data, a), read(data, b))
    case WCode{fi, b}:
      Obs{only(data, OCode{fi})}
    case WGate{}:
      Obs{only(data, OGate{})}
    case WAbort{at}:
      Obs{only(data, OAbort{})}
    case WAborted{at, m}:
      Obs{only(data, OAborted{at, m})}
    case WStuck{}:
      Obs{only(data, OStuck{})}
    case WHole{p}:
      Obs{OHole{p}}
    case WMark{at}:
      Fired{at}

def aborted.of(+at: E.Site, r: R) -> R:
  match r:
    case Obs{m}:
      Val{WAborted{at, m}}
    case other:
      other

# Abort at `at` applied to e: 0 is the identity; a pair aborts with the
# pair, read as data, for message.
def abort.of(+at: E.Site, e: W) -> R:
  match e:
    case WZero{}:
      Val{WCode{Co.abort.ind(), E.XEnv{}}}
    case WPair{+a, +b}:
      marked.or(mark.in(WPair{a, b}), aborted.of(at, read(True{}, WPair{a, b})))
    case WAborted{at2, m}:
      Val{WAborted{at2, m}}
    case WHole{p}:
      Needs{p}
    case WMark{at2}:
      used(at2)
    case _:
      Val{WStuck{}}

# A watched check: its value where its test gave 0, else a mark.
def checked(+site: U32, t: R, c: R) -> R:
  match t:
    case Val{w}:
      match w:
        case WZero{}:
          c
        case WHole{p}:
          Needs{p}
        case WMark{at}:
          used(at)
        case _:
          Val{WMark{E.AtCheck{site}}}
    case other:
      other

def pair.of(a: R, b: R) -> R:
  match a:
    case Val{x}:
      match b:
        case Val{y}:
          Val{WPair{x, y}}
        case other:
          other
    case other:
      other

# An aborted value's message, as written in the program.
def odata(x: E.X) -> O:
  match x:
    case E.XZero{}:
      OZero{}
    case E.XPair{a, b}:
      OPair{odata(a), odata(b)}
    case _:
      OZero{}

def left.r(r: R) -> R:
  match r:
    case Val{w}:
      left.of(w)
    case other:
      other

def right.r(r: R) -> R:
  match r:
    case Val{w}:
      right.of(w)
    case other:
      other

# The evaluator
# -------------

# The strict if's parts: SetEnv(Pair(SetEnv(Pair(Gate, s)), Pair(l, r))),
# the shape the IC runs only one branch of (P4).
type If is Data:
  If{+s: E.X, +l: E.X, +rt: E.X}

def if.of(y: E.X) -> Maybe<&2, If>:
  match y:
    case E.XPair{E.XSetEnv{E.XPair{E.XGate{}, s}}, E.XPair{l, rt}}:
      Some{If{s, l, rt}}
    case _:
      None{}

def setenv.of(m: Maybe<&2, If>, y: E.X, env: W) -> Job:
  match m:
    case Some{i}:
      match i:
        case If{s, l, rt}:
          JIfE{s, l, rt, env}
    case None{}:
      JSetE{y, env}

def check.of(how: How, +site: U32, tc: E.X, c: E.X, env: W) -> Job:
  match how:
    case Kept{}:
      JE{E.check.of(True{}, site, tc, c), env}
    case Gone{}:
      JE{c, env}
    case Watched{}:
      JWatch{site, tc, c, env}

# What x is, or what to evaluate for it.
def step(+pol: Pol, x: E.X, +env: W) -> Job:
  match x:
    case E.XZero{}:
      JDone{Val{WZero{}}}
    case E.XPair{a, b}:
      JPair{a, b, env}
    case E.XEnv{}:
      JDone{Val{env}}
    case E.XSetEnv{+y}:
      setenv.of(if.of(y), y, env)
    case E.XDefer{fi, b}:
      JDone{Val{WCode{fi, b}}}
    case E.XGate{}:
      JDone{Val{WGate{}}}
    case E.XLeft{y}:
      JLeft{y, env}
    case E.XRight{y}:
      JRight{y, env}
    case E.XAbort{at}:
      JDone{Val{WAbort{at}}}
    case E.XAborted{at, m}:
      JDone{Val{WAborted{at, odata(m)}}}
    case E.XVar{p}:
      JDone{Val{WHole{p}}}
    case E.XCheck{+site, tc, c}:
      check.of(check.how(pol, site), site, tc, c, env)
    case E.XStub{+tok, y}:
      stub.job(pol, tok, env)
    case _:
      JDone{Val{WStuck{}}}

# c applied to e.
def apply.of(c: W, e: W) -> Job:
  match c:
    case WCode{fi, b}:
      JE{b, e}
    case WGate{}:
      JDone{gate.of(e)}
    case WAbort{+at}:
      JDone{abort.of(at, e)}
    case WAborted{at, m}:
      JDone{Val{WAborted{at, m}}}
    case WMark{at}:
      JDone{used(at)}
    case _:
      JDone{Val{WStuck{}}}

# SetEnv of w: its left applied to its right.
def set.of(w: W) -> Job:
  match w:
    case WPair{c, e}:
      apply.of(c, e)
    case WAborted{at, m}:
      JDone{Val{WAborted{at, m}}}
    case WMark{at}:
      JDone{used(at)}
    case _:
      JDone{Val{WStuck{}}}

def set.job(r: R) -> Job:
  match r:
    case Val{w}:
      set.of(w)
    case other:
      JDone{other}

# The strict if on w: only the branch w chooses.
def branch.of(w: W, l: E.X, rt: E.X, env: W) -> Job:
  match w:
    case WZero{}:
      JE{l, env}
    case WPair{a, b}:
      JE{rt, env}
    case WAborted{at, m}:
      JDone{Val{WAborted{at, m}}}
    case WHole{p}:
      JDone{Needs{p}}
    case WMark{at}:
      JDone{used(at)}
    case _:
      JDone{Val{WStuck{}}}

def if.job(r: R, l: E.X, rt: E.X, env: W) -> Job:
  match r:
    case Val{w}:
      branch.of(w, l, rt, env)
    case other:
      JDone{other}

def sem(+fuel: Nat, +pol: Pol, job: Job) -> R:
  match fuel:
    case 0n:
      Spent{}
    case 1n+f:
      match job:
        case JE{x, env}:
          sem(f, pol, step(pol, x, env))
        case JPair{a, b, +env}:
          pair.of(sem(f, pol, JE{a, env}), sem(f, pol, JE{b, env}))
        case JSetE{y, env}:
          sem(f, pol, JSet{sem(f, pol, JE{y, env})})
        case JSet{r}:
          sem(f, pol, set.job(r))
        case JIfE{s, l, rt, +env}:
          sem(f, pol, JIf{sem(f, pol, JE{s, env}), l, rt, env})
        case JIf{r, l, rt, env}:
          sem(f, pol, if.job(r, l, rt, env))
        case JLeft{y, env}:
          left.r(sem(f, pol, JE{y, env}))
        case JRight{y, env}:
          right.r(sem(f, pol, JE{y, env}))
        case JWatch{+site, +tc, +c, +env}:
          checked(site, sem(f, pol, JE{E.app(tc, c), env}), sem(f, pol, JE{c, env}))
        case JDone{r}:
          r

# Running
# -------

# Fuel enough for any program the port runs (sizing's).
def fuel() -> Nat:
  U32.to_nat(4294967295)

def read.r(r: R) -> R:
  match r:
    case Val{w}:
      read(False{}, w)
    case other:
      other

# main applied to input (data, with XVar where a position is not yet
# known), read back in full.
def run(+fuel: Nat, +pol: Pol, main: E.X, input: E.X) -> R:
  read.r(sem(fuel, pol, JE{E.app(main, input), WZero{}}))

# Counting
# --------

# The erasure checker's budget is evaluation steps (Check.bend), so it
# runs sem counted: semc is sem that also counts the jobs it takes on fuel
# left. Its result is sem's (PROOF.bend, semc_sem), so a verdict reached
# with it is one reached with sem, which is what the laws read.
#
# A def may only call itself, and a match only open a parameter, so where
# sem feeds one run's result to the next (JSetE, JIfE) semc hands itself
# the result as a job (Kc's SetK, IfK) and opens it there.
type C is Data:
  C{+r: R, +n: Nat}

# What semc runs: a job, counted from n; or JSet, JIf on c's result,
# counted from c's count.
type Kc is Data:
  Go{+job: Job, +n: Nat}
  SetK{+c: C}
  IfK{+c: C, +l: E.X, +rt: E.X, +env: W}

def c.r(c: C) -> R:
  match c:
    case C{r, n}:
      r

def c.n(c: C) -> Nat:
  match c:
    case C{r, n}:
      n

# The job k stands for (PROOF.bend), and the count it starts from.
def kc.job(k: Kc) -> Job:
  match k:
    case Go{job, n}:
      job
    case SetK{c}:
      JSet{c.r(c)}
    case IfK{c, l, rt, env}:
      JIf{c.r(c), l, rt, env}

def kc.n(k: Kc) -> Nat:
  match k:
    case Go{job, n}:
      n
    case SetK{c}:
      c.n(c)
    case IfK{c, l, rt, env}:
      c.n(c)

def pair.c(ca: C, cb: C) -> C:
  match ca:
    case C{a, x}:
      match cb:
        case C{b, y}:
          C{pair.of(a, b), Nat.add(x, y)}

def watch.c(+site: U32, ct: C, cc: C) -> C:
  match ct:
    case C{t, x}:
      match cc:
        case C{c, y}:
          C{checked(site, t, c), Nat.add(x, y)}

def left.c(c: C) -> C:
  match c:
    case C{r, m}:
      C{left.r(r), m}

def right.c(c: C) -> C:
  match c:
    case C{r, m}:
      C{right.r(r), m}

def semc(+fuel: Nat, +pol: Pol, k: Kc) -> C:
  match fuel:
    case 0n:
      C{Spent{}, kc.n(k)}
    case 1n+f:
      match k:
        case Go{job, n}:
          match job:
            case JE{x, env}:
              semc(f, pol, Go{step(pol, x, env), 1n+n})
            case JPair{a, b, +env}:
              pair.c(semc(f, pol, Go{JE{a, env}, 1n+n}), semc(f, pol, Go{JE{b, env}, 0n}))
            case JSetE{y, env}:
              semc(f, pol, SetK{semc(f, pol, Go{JE{y, env}, 1n+n})})
            case JSet{r}:
              semc(f, pol, Go{set.job(r), 1n+n})
            case JIfE{s, l, rt, +env}:
              semc(f, pol, IfK{semc(f, pol, Go{JE{s, env}, 1n+n}), l, rt, env})
            case JIf{r, l, rt, env}:
              semc(f, pol, Go{if.job(r, l, rt, env), 1n+n})
            case JLeft{y, env}:
              left.c(semc(f, pol, Go{JE{y, env}, 1n+n}))
            case JRight{y, env}:
              right.c(semc(f, pol, Go{JE{y, env}, 1n+n}))
            case JWatch{+site, tc, +c, +env}:
              watch.c(site, semc(f, pol, Go{JE{E.app(tc, c), env}, 1n+n}), semc(f, pol, Go{JE{c, env}, 0n}))
            case JDone{r}:
              C{r, n}
        case SetK{c}:
          match c:
            case C{r, m}:
              semc(f, pol, Go{set.job(r), 1n+m})
        case IfK{c, l, rt, env}:
          match c:
            case C{r, m}:
              semc(f, pol, Go{if.job(r, l, rt, env), 1n+m})

def read.c(c: C) -> C:
  match c:
    case C{r, m}:
      C{read.r(r), m}

# run, counted from n.
def runc(+fuel: Nat, +pol: Pol, main: E.X, input: E.X, n: Nat) -> C:
  read.c(semc(fuel, pol, Go{JE{E.app(main, input), WZero{}}, n}))

# What runs: every erasable site erased (no check is erasable but those
# listed; a program with no XCheck and no XStub ignores them).
def plain() -> Pol:
  Pol{Erase{}, []}

def of.data(d: Co.D) -> E.X:
  match d:
    case Co.DZero{}:
      E.XZero{}
    case Co.DPair{a, b}:
      E.XPair{of.data(a), of.data(b)}

# The runnable core as X (an Abort's site is unknown there).
def of.core(v: Co.V) -> E.X:
  match v:
    case Co.VZero{}:
      E.XZero{}
    case Co.VPair{a, b}:
      E.XPair{of.core(a), of.core(b)}
    case Co.VEnv{}:
      E.XEnv{}
    case Co.VSetEnv{a}:
      E.XSetEnv{of.core(a)}
    case Co.VDefer{fi, a}:
      E.XDefer{fi, of.core(a)}
    case Co.VGate{}:
      E.XGate{}
    case Co.VLeft{a}:
      E.XLeft{of.core(a)}
    case Co.VRight{a}:
      E.XRight{of.core(a)}
    case Co.VAbort{}:
      E.XAbort{E.AtAbort{}}
    case Co.VAborted{m}:
      E.XAborted{E.AtAbort{}, of.data(m)}
