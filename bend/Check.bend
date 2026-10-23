import Base
import ./Expr.bend as E
import ./Sem.bend as Sm

# The erasure checker (SIZING-PROOF.md §4, checker v1): whether a
# sized program's erasures are sound, by running its witness under Sem
# over every input the session can give it.
#
# The witness is main as sizing sized it, with every erasable site still
# marked: each recursion a chain of its count of links over XStub (the
# rest of the recursion), each check an XCheck. Watched, a run of it ends
# with Fired where an erasable check does not pass or a chain's bottom is
# reached (Sem.bend).
#
# The run starts on an input it knows nothing of (XVar ""). Where it needs
# a position's shape (Needs), the input is split there, 0 and a pair, and
# each side runs again; the guard runs first and prunes what it refuses.
# Every input lies under one leaf of that tree, and a leaf's run never
# looked at what it left unknown, so it is that input's run. A program is
# proven when no leaf fires; one that fires names the input; one past the
# budget is unknown.
#
# The budget is work: the evaluation steps of every run the tree makes,
# the guard's and main's (Sem.semc counts them; its results are Sem.sem's,
# PROOF.bend's semc_sem). Each leaf spends one more, so the tree always
# ends. A count of runs alone would not do: a program whose runs are long
# would spend minutes before it gave up.

# The witness
# -----------

def witness(+counts: List<&2, E.TS>, x: E.X) -> E.X:
  match x:
    case E.XStub{+tok, y}:
      E.chain.over(U32.to_nat(E.count.of(counts, tok)), E.XStub{tok, y})
    case E.XCheck{site, tc, c}:
      E.XCheck{site, witness(counts, tc), witness(counts, c)}
    case E.XPair{a, b}:
      E.XPair{witness(counts, a), witness(counts, b)}
    case E.XSetEnv{a}:
      E.XSetEnv{witness(counts, a)}
    case E.XDefer{fi, a}:
      E.XDefer{fi, witness(counts, a)}
    case E.XLeft{a}:
      E.XLeft{witness(counts, a)}
    case E.XRight{a}:
      E.XRight{witness(counts, a)}
    case other:
      other

# The check sites in x, by number.
def sites(x: E.X, acc: List<&2, U32>) -> List<&2, U32>:
  match x:
    case E.XCheck{site, tc, c}:
      site <> sites(tc, sites(c, acc))
    case E.XPair{a, b}:
      sites(a, sites(b, acc))
    case E.XSetEnv{a}:
      sites(a, acc)
    case E.XDefer{fi, a}:
      sites(a, acc)
    case E.XLeft{a}:
      sites(a, acc)
    case E.XRight{a}:
      sites(a, acc)
    case E.XStub{tok, a}:
      sites(a, acc)
    case _:
      acc

def kept(+left: Set(), +site: U32) -> Bool:
  Pair.snd(Set(), Bool, Set.has(left, U32.show(site)))

def unkept.of(k: Bool, s: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match k:
    case True{}:
      rest
    case False{}:
      s <> rest

def unkept(xs: List<&2, U32>, +left: Set()) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+s, rest}:
      unkept.of(kept(left, s), s, unkept(rest, left))

# The checks sizing erases: every one not left to run time (Sz.discharged).
def erasable(x: E.X, +left: Set()) -> List<&2, U32>:
  unkept(sites(x, []), left)

# Splitting the input
# -------------------

def split.at(+p: String, zero: Bool) -> E.X:
  match zero:
    case True{}:
      E.XZero{}
    case False{}:
      E.XPair{E.XVar{p ++ "L"}, E.XVar{p ++ "R"}}

# A position's path as directions, True for left.
def dirs(p: String) -> List<&2, Bool>:
  match p:
    case SNil{}:
      []
    case SCon{c, rest}:
      match c:
        case Chr{k}:
          U32.is_eq(k, 76) <> dirs(rest)

# The input with the unknown position on the way to the position at rest (at
# or above it) made 0 or a pair.
def split(i: E.X, rest: List<&2, Bool>, +zero: Bool) -> E.X:
  match i:
    case E.XVar{+q}:
      split.at(q, zero)
    case E.XPair{a, b}:
      match rest:
        case Con{d, more}:
          match d:
            case True{}:
              E.XPair{split(a, more, zero), b}
            case False{}:
              E.XPair{a, split(b, more, zero)}
        case Nil{}:
          E.XPair{a, b}
    case other:
      other

# Exploring
# ---------

type Verdict is Data:
  Proven{}
  Fires{+input: E.X, +at: E.Site}
  Unknown{+why: String}

def worse(a: Verdict, b: Verdict) -> Verdict:
  match a:
    case Proven{}:
      b
    case other:
      other

def any.bad(o: Sm.O) -> Bool:
  match o:
    case Sm.OAborted{at, m}:
      True{}
    case Sm.OStuck{}:
      True{}
    case Sm.OPair{a, b}:
      any.bad(a) || any.bad(b)
    case _:
      False{}

# What the session does with the guard's answer: go on to main, or not.
type Gate is Data:
  Pass{}
  Refuse{}
  Need{+p: String}
  Lost{+why: String}

def guard.gate(r: Sm.R) -> Gate:
  match r:
    case Sm.Obs{+o}:
      Bool.pick(Gate, any.bad(o), Refuse{}, Pass{})
    case Sm.Needs{p}:
      Need{p}
    case Sm.Spent{}:
      Lost{"the guard ran out of fuel"}
    case _:
      Lost{"the guard fired a site"}

def guard.on(+fuel: Nat, g: Maybe<&2, E.X>, i: E.X) -> Gate:
  match g:
    case None{}:
      Pass{}
    case Some{gx}:
      guard.gate(Sm.run(fuel, Sm.plain(), gx, i))

# What a node of the tree asks for next.
type Step is Data:
  Settled{+v: Verdict}
  Fork{+p: String}

def main.step(+i: E.X, r: Sm.R) -> Step:
  match r:
    case Sm.Obs{o}:
      Settled{Proven{}}
    case Sm.Fired{at}:
      Settled{Fires{i, at}}
    case Sm.Needs{p}:
      Fork{p}
    case _:
      Settled{Unknown{"main ran out of fuel"}}

def node.step(g: Gate, +fuel: Nat, +pol: Sm.Pol, +main: E.X, +i: E.X) -> Step:
  match g:
    case Pass{}:
      main.step(i, Sm.run(fuel, pol, main, i))
    case Refuse{}:
      Settled{Proven{}}
    case Need{p}:
      Fork{p}
    case Lost{why}:
      Settled{Unknown{why}}

# A node's step, counted: the step, and n plus the evaluation steps its
# runs took.
type Counted is Data:
  Counted{+s: Step, +n: Nat}

def counted.s(c: Counted) -> Step:
  match c:
    case Counted{s, n}:
      s

def main.c(+i: E.X, c: Sm.C) -> Counted:
  match c:
    case Sm.C{r, n}:
      Counted{main.step(i, r), n}

# node.step, counted from n.
def node.c(g: Gate, +fuel: Nat, +pol: Sm.Pol, +main: E.X, +i: E.X, n: Nat) -> Counted:
  match g:
    case Pass{}:
      main.c(i, Sm.runc(fuel, pol, main, i, n))
    case Refuse{}:
      Counted{Settled{Proven{}}, n}
    case Need{p}:
      Counted{Fork{p}, n}
    case Lost{why}:
      Counted{Settled{Unknown{why}}, n}

def gate.c(+fuel: Nat, +pol: Sm.Pol, +main: E.X, +i: E.X, c: Sm.C) -> Counted:
  match c:
    case Sm.C{r, n}:
      node.c(guard.gate(r), fuel, pol, main, i, n)

# What node.step says of i, with the guard's answer guard.on's, counted.
def node.counted(+fuel: Nat, +pol: Sm.Pol, +main: E.X, g: Maybe<&2, E.X>, +i: E.X) -> Counted:
  match g:
    case None{}:
      node.c(Pass{}, fuel, pol, main, i, 0n)
    case Some{gx}:
      gate.c(fuel, pol, main, i, Sm.runc(fuel, Sm.plain(), gx, i, 0n))

type Seen is Data:
  Seen{+v: Verdict, +left: Nat}

def seen.v(s: Seen) -> Verdict:
  match s:
    case Seen{v, left}:
      v

# A node of the tree: the inputs under i, with work left; the step its run
# asks for; or the pair side i, once the zero side (first) is done.
type Job is Data:
  Node{+i: E.X, +work: Nat}
  At{+i: E.X, +work: Nat, +s: Step}
  Then{+i: E.X, +first: Seen}

# The node at i, its step taken and its work spent.
def at.of(+i: E.X, w: Nat, c: Counted) -> Job:
  match c:
    case Counted{s, n}:
      At{i, Nat.sub(w, n), s}

# Explore: depth bounds how deep the tree's jobs nest, work the steps its
# runs take in all (and one a leaf).
def explore(+depth: Nat, +fuel: Nat, +pol: Sm.Pol, +main: E.X, +g: Maybe<&2, E.X>, job: Job) -> Seen:
  match depth:
    case 0n:
      Seen{Unknown{"the input split too deep"}, 0n}
    case 1n+d:
      match job:
        case Node{+i, work}:
          match work:
            case 0n:
              Seen{Unknown{"its budget of evaluation steps ran out"}, 0n}
            case 1n+w:
              explore(d, fuel, pol, main, g, at.of(i, w, node.counted(fuel, pol, main, g, i)))
        case At{+i, +work, s}:
          match s:
            case Settled{v}:
              Seen{v, work}
            case Fork{+p}:
              explore(d, fuel, pol, main, g, Then{split(i, dirs(p), False{}), explore(d, fuel, pol, main, g, Node{split(i, dirs(p), True{}), work})})
        case Then{+i, first}:
          match first:
            case Seen{v, left}:
              match v:
                case Proven{}:
                  explore(d, fuel, pol, main, g, Node{i, left})
                case other:
                  Seen{other, left}

def step.verdict(s: Step) -> Verdict:
  match s:
    case Settled{v}:
      v
    case Fork{p}:
      Unknown{"the opening input has no unknown position"}

# The verdict on main's witness, watched under pol: on the opening 0, and
# on every input its guard g passes, within work evaluation steps (the
# opening run's not counted). Seen's left: the work not spent.
def opened(v: Verdict, s: Seen) -> Seen:
  match s:
    case Seen{w, left}:
      Seen{worse(v, w), left}

def check(+depth: Nat, +fuel: Nat, +pol: Sm.Pol, +main: E.X, +g: Maybe<&2, E.X>, work: Nat) -> Seen:
  opened(step.verdict(main.step(E.XZero{}, Sm.run(fuel, pol, main, E.XZero{}))),
    explore(depth, fuel, pol, main, g, Node{E.XVar{""}, work}))

# Saying it
# ---------

# An input: a unary number as its value, a pair as (a b), an unknown
# position as _. m: x as a number, if it is one.
def shown(x: E.X, m: Maybe<&2, U32>) -> String:
  match x:
    case E.XPair{+a, +b}:
      match m:
        case Some{k}:
          U32.show(k)
        case None{}:
          "(" ++ shown(a, E.to.int(a)) ++ " " ++ shown(b, E.to.int(b)) ++ ")"
    case E.XZero{}:
      "0"
    case E.XVar{p}:
      "_"
    case _:
      "?"

def show(+x: E.X) -> String:
  shown(x, E.to.int(x))

def at.name(at: E.Site) -> String:
  match at:
    case E.AtCheck{n}:
      "check " ++ U32.show(n)
    case E.AtRecursion{t}:
      "the bottom of recursion #" ++ U32.show(t)
    case E.AtAbort{}:
      "an abort"
