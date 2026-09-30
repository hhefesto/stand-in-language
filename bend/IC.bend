import Base
import ./Loc.bend as Lc
import ./Expr.bend as E
import ./Show.bend as Sh
import ./Lift.bend as Lf

# The interaction-combinator runtime (haskell-final's Telomare.IC, the part
# a run uses). The sized program's closures are compiled once into
# templates; each iteration builds the entry net around its input, reduces
# it, and reads the result back.
#
# The net is one Array<U32>, eight words per agent: kind, the peers of its
# ports 0-2 (a port is agent*4+slot), and two payload words (a Dup's label;
# a Ref's template and function index; a StuckV's message number). Agent 0
# is never used, so 0 ends the free list. Active pairs sit on a LIFO list,
# as in Haskell, and every rule consumes the pair it fires, so the count of
# interactions does not depend on the order they fire in.

# Agent kinds
# -----------

# What is not the agents: the active pairs (a flat list, a then b), the
# stuck values' messages (newest first, numbered from 0), the allocation
# state, the fuel, the interactions spent and an error.

type Ctl is Data:
  Ctl{+stk: List<&2, U32>, +msgs: List<&2, String>, +nmsg: U32, +bump: U32, +free: U32,
      +label: U32, +fuel: U32, +spent: U32, +err: U32, +emsg: String, +cap: U32}

# The agents, the templates, and the rest.
type Net is Type:
  Net{mem: Array<U32>, tpl: Array<U32>, ctl: Ctl}

# An agent at a glance: kind, payload, and the peers of ports 1 and 2.
type NI is Data:
  NI{+k: U32, +a: U32, +b: U32, +p1: U32, +p2: U32}

# A step of describe: an agent to look at, or what was read of it.
type DJ is Data:
  DNode{+n: U32, +d: Nat}
  DAt{+i: NI, +src: U32, +d: Nat}

type Ids is Data:
  Ids{+x: U32, +y: U32, +z: U32, +w: U32}

type Popped is Type:
  PEmpty{net: Net}
  PStale{net: Net}
  PPair{net: Net, +a: U32, +b: U32}

# While compiling a body: the net and, per environment path, the wires
# that deliver it (icEnvQueue). A path lists the projections from Env
# outward, first applied first: Left (Right Env) is "RL".
type CS is Type:
  CS{net: Net, q: Map<&2, List<&2, U32>>}

type WJ is Data:
  WStart{+src: U32, +use: Map<&2, U32>}
  WAfter{+desc: Bool, +here: Map<&2, List<&2, U32>>, +rest: List<&2, U32>, +subl: Map<&2, U32>, +subr: Map<&2, U32>}

type CJ is Data:
  CTerm{+x: E.X}
  CProj{+path: Maybe<&2, String>, +k: U32, +x: E.X}

# A closure body to compile: its template number, function index, body
# (nested closures already templates), the body as written, and its code's
# hash (tplHash) when there is guidance to look up by it.
type Src is Data:
  Src{+tid: U32, +fi: U32, +body: E.X, +orig: E.X, +code: String}

# The templates so far and, when there is guidance, their codes' hashes.
type Coll is Data:
  Coll{+next: U32, +srcs: List<&2, Src>, +hs: Maybe<&2, Map<&2, String>>}

# A compiled template, read out of the scratch net where it was built:
# its agents (kind, a, b) and its wires, each from the lower port.
type Ser is Data:
  Ser{+nodes: List<&2, U32>, +wires: List<&2, U32>, +w: U32}

# The compiled program: the entry (main applied to the environment, its
# closures templates), the templates' bodies for reading closures back,
# and the template store.
type Prog is Data:
  Prog{+entry: E.X, +bodies: Map<&2, E.X>, +words: List<&2, U32>, +maxk: U32}

type RJ is Data:
  RVisit{+p: U32, +data: Bool}
  RMkPair{}
  RMkAborted{}

type RB is Data:
  RBOk{+x: E.X}
  RBErr{+msg: String}

# A step of copying a value region (dupRegion): the value at a port, by
# the shape at an offset of the store, or the last two regions' copies to
# pair up.
type RG is Data:
  RgVisit{+s: U32, +p: U32}
  RgPair{}

# The jobs left, and the copies made: two ports per region, first copy on
# top.
type RgSt is Type:
  RgSt{net: Net, jobs: List<&2, RG>, vals: List<&2, U32>}

type RSt is Type:
  RLoop{net: Net, jobs: List<&2, RJ>, vals: List<&2, E.X>}
  RSeen{data: Bool, r: Net & NI, jobs: List<&2, RJ>, vals: List<&2, E.X>}

# What a run gives: the net back (for the next run), the result or the
# error as Haskell shows an ICError, and the interactions spent.
type Run is Type:
  Run{net: Net, out: RB, spent: U32}

def root() -> U32:
  1

def ext() -> U32:
  2

def era() -> U32:
  3

def zero() -> U32:
  4

def gate() -> U32:
  5

def abort() -> U32:
  6

def ref() -> U32:
  7

def pair() -> U32:
  8

def aborted() -> U32:
  9

def dup() -> U32:
  10

def split() -> U32:
  11

def setenv() -> U32:
  12

def apply() -> U32:
  13

def scrut() -> U32:
  14

def scrut.abort() -> U32:
  15

def left() -> U32:
  16

def right() -> U32:
  17

def stuck() -> U32:
  18

# The number of ports an agent of kind k has.
def arity(k: U32) -> U32:
  match k:
    case 2:
      2
    case 8:
      3
    case 9:
      2
    case 10:
      3
    case 11:
      3
    case 12:
      2
    case 13:
      3
    case 14:
      2
    case 15:
      2
    case 16:
      2
    case 17:
      2
    case _:
      1

# Values: what a consumer can meet (valueKind).
def is.value(k: U32) -> Bool:
  match k:
    case 4:
      True{}
    case 5:
      True{}
    case 6:
      True{}
    case 7:
      True{}
    case 8:
      True{}
    case 9:
      True{}
    case 18:
      True{}
    case _:
      False{}

def signed.pick(neg: Bool, +n: U32) -> String:
  match neg:
    case True{}:
      "-" ++ U32.show((0 - n : U32))
    case False{}:
      U32.show(n)

# A function index as Haskell shows an Int.
def signed(+n: U32) -> String:
  signed.pick(U32.is_ge(n, 2147483648), n)

def msg.got(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      s
    case None{}:
      "?"

# Stuck message number n of nmsg (the list is newest first).
def msg.at(msgs: List<&2, String>, +nmsg: U32, +n: U32) -> String:
  msg.got(List.get(&2, String, msgs, U32.to_nat((nmsg - 1 - n : U32))))

# The net
# -------

def rd.got(tpl: Array<U32>, ctl: Ctl, r: Array<U32> & U32) -> Net & U32:
  (mem, v) = r
  (Net{mem, tpl, ctl}, v)

# Word i of the agents.
def rd(net: Net, +i: U32) -> Net & U32:
  match net:
    case Net{mem, tpl, ctl}:
      rd.got(tpl, ctl, mem[i])

def wr(net: Net, +i: U32, +v: U32) -> Net:
  match net:
    case Net{mem, tpl, ctl}:
      Net{mem[i] <- v, tpl, ctl}

def trd.got(mem: Array<U32>, ctl: Ctl, r: Array<U32> & U32) -> Net & U32:
  (tpl, v) = r
  (Net{mem, tpl, ctl}, v)

# Word i of the templates.
def trd(net: Net, +i: U32) -> Net & U32:
  match net:
    case Net{mem, tpl, ctl}:
      trd.got(mem, ctl, tpl[i])

def twr(net: Net, +i: U32, +v: U32) -> Net:
  match net:
    case Net{mem, tpl, ctl}:
      Net{mem, tpl[i] <- v, ctl}

def slot.of(+p: U32) -> U32:
  (p % 4 : U32)

def node.of(+p: U32) -> U32:
  (p / 4 : U32)

# Where port p's peer is written.
def idx(+p: U32) -> U32:
  ((p / 4) * 8 + 1 + p % 4 : U32)

def peer(net: Net, +p: U32) -> Net & U32:
  rd(net, idx(p))

def kind.of(net: Net, +n: U32) -> Net & U32:
  rd(net, (n * 8 : U32))

def interactive(k: U32) -> Bool:
  match k:
    case 1:
      False{}
    case 2:
      False{}
    case 0:
      False{}
    case _:
      True{}

def ctl.of(net: Net) -> Net & Ctl:
  match net:
    case Net{mem, tpl, +ctl}:
      (Net{mem, tpl, ctl}, ctl)

def with.ctl(net: Net, ctl: Ctl) -> Net:
  match net:
    case Net{mem, tpl, old}:
      Net{mem, tpl, ctl}

def c.bump(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      bump

def c.cap(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      cap

# Copy words i.. of an array into another (for growing the agents).
def copy(n: Nat, +i: U32, r: Array<U32> & U32, dst: Array<U32>) -> Array<U32>:
  match n:
    case 0n:
      dst
    case 1n+k:
      (src, v) = r
      copy(k, (i + 1 : U32), src[(i + 1 : U32)], dst[i] <- v)

def init(net: Net, +id: U32, +k: U32, +a: U32, +b: U32) -> Net & U32:
  (wr(wr(wr(net, (id * 8 : U32), k), (id * 8 + 4 : U32), a), (id * 8 + 5 : U32), b), id)

def c.label(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      label

def c.nmsg(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      nmsg

def ni.k(i: NI) -> U32:
  match i:
    case NI{k, a, b, p1, p2}:
      k

def ni.a(i: NI) -> U32:
  match i:
    case NI{k, a, b, p1, p2}:
      a

def ni.b(i: NI) -> U32:
  match i:
    case NI{k, a, b, p1, p2}:
      b

def ni.p1(i: NI) -> U32:
  match i:
    case NI{k, a, b, p1, p2}:
      p1

def ni.p2(i: NI) -> U32:
  match i:
    case NI{k, a, b, p1, p2}:
      p2

def info.five(+k: U32, +a: U32, +b: U32, +p1: U32, r: Net & U32) -> Net & NI:
  (net, +p2) = r
  (net, NI{k, a, b, p1, p2})

def info.four(+n: U32, +k: U32, +a: U32, +b: U32, r: Net & U32) -> Net & NI:
  (net, +p1) = r
  info.five(k, a, b, p1, rd(net, (n * 8 + 3 : U32)))

def info.three(+n: U32, +k: U32, +a: U32, r: Net & U32) -> Net & NI:
  (net, +b) = r
  info.four(n, k, a, b, rd(net, (n * 8 + 2 : U32)))

def info.two(+n: U32, +k: U32, r: Net & U32) -> Net & NI:
  (net, +a) = r
  info.three(n, k, a, rd(net, (n * 8 + 5 : U32)))

def info.one(+n: U32, r: Net & U32) -> Net & NI:
  (net, +k) = r
  info.two(n, k, rd(net, (n * 8 + 4 : U32)))

def info(net: Net, +n: U32) -> Net & NI:
  info.one(n, rd(net, (n * 8 : U32)))

# A monad over the net, for walks that thread it
# ----------------------------------------------

def N(-A: Data) -> Type:
  Net -> Net & A

def N.pure(-A: Data, x: A) -> N(A):
  net => (net, x)

def N.run(-A: Data, -B: Data, f: A -> N(B), r: Net & A) -> Net & B:
  (net, +a) = r
  f(a)(net)

def N.bind(-A: Data, -B: Data, m: N(A), f: A -> N(B)) -> N(B):
  net => N.run(A, B, f, m(net))

def n.rd(+i: U32) -> N(U32):
  net => rd(net, i)

def n.peer(+p: U32) -> N(U32):
  net => peer(net, p)

def n.info(+n: U32) -> N(NI):
  net => info(net, n)

# How Haskell shows an agent's kind (Show ICKind).
def show.kind(k: U32, +a: U32, +b: U32) -> String:
  match k:
    case 1:
      "ICRoot"
    case 2:
      "ICExt"
    case 3:
      "ICEra"
    case 4:
      "ICZero"
    case 5:
      "ICGate"
    case 6:
      "ICAbort"
    case 7:
      "ICRef " ++ U32.show(a) ++ " (FunctionIndex {unFunctionIndex = " ++ signed(b) ++ "})"
    case 8:
      "ICPair"
    case 9:
      "ICAborted"
    case 10:
      "ICDup " ++ U32.show(a)
    case 11:
      "ICSplit"
    case 12:
      "ICSetEnv"
    case 13:
      "ICApply"
    case 14:
      "ICScrut"
    case 15:
      "ICScrutAbort"
    case 16:
      "ICLeft"
    case 17:
      "ICRight"
    case 18:
      "ICStuckV"
    case _:
      "ICFree"

def show.ni(i: NI) -> String:
  match i:
    case NI{k, a, b, p1, p2}:
      show.kind(k, a, b)

# A value's shape to depth d, for messages (describeValue).
def describe(+fuel: Nat, j: DJ) -> N(String):
  match fuel:
    case 0n:
      N.pure(String, "...")
    case 1n+f:
      match j:
        case DNode{+n, d}:
          match d:
            case 0n:
              N.pure(String, "...")
            case 1n+e:
              do N<String>:
                i : NI <- n.info(n)
                src : U32 <- n.peer((n * 4 : U32))
                describe(f, DAt{i, src, e})
        case DAt{i, src, e}:
          match i:
            case NI{4, a, b, p1, p2}:
              N.pure(String, "0")
            case NI{8, a, b, p1, p2}:
              do N<String>:
                sa : String <- describe(f, DNode{node.of(p1), e})
                sb : String <- describe(f, DNode{node.of(p2), e})
                return "(" ++ sa ++ "," ++ sb ++ ")"
            case NI{7, +a, b, p1, p2}:
              N.pure(String, "ref" ++ U32.show(a))
            case NI{10, +a, b, p1, p2}:
              do N<String>:
                s : String <- describe(f, DNode{node.of(src), e})
                return "dup" ++ U32.show(a) ++ "[" ++ s ++ "]"
            case NI{k, +a, +b, p1, p2}:
              N.pure(String, show.kind(k, a, b))

# Rules
# -----

def alloc2.two(+x: U32, r: Net & U32) -> Net & Ids:
  (net, +y) = r
  (net, Ids{x, y, 0, 0})

def alloc4.two(+x: U32, +y: U32, r: Net & Ids) -> Net & Ids:
  (net, +i) = r
  match i:
    case Ids{z, w, a, b}:
      (net, Ids{x, y, z, w})

def port(+n: U32, +s: U32) -> U32:
  (n * 4 + s : U32)

def comps(j: NI) -> List<&2, U32>:
  match j:
    case NI{8, a, b, p1, p2}:
      [p1, p2]
    case _:
      []

def relabel(dup: Bool, +a: U32, +base: U32) -> U32:
  match dup:
    case True{}:
      (a + base : U32)
    case False{}:
      a

def inst.node.id(+map: U32, +i: U32, r: Net & U32) -> Net:
  (net, +id) = r
  twr(net, (map + i : U32), id)

def tr.got(+s: U32, r: Net & U32) -> Net & U32:
  (net, +id) = r
  (net, (id * 4 + s : U32))

def tr.ext(zero: Bool, +env: U32, +res: U32) -> U32:
  match zero:
    case True{}:
      env
    case False{}:
      res

def tr.pick(boundary: Bool, net: Net, +p: U32, +env: U32, +res: U32, +map: U32) -> Net & U32:
  match boundary:
    case True{}:
      (net, tr.ext(U32.is_zero(slot.of(p)), env, res))
    case False{}:
      tr.got(slot.of(p), trd(net, (map + node.of(p) : U32)))

# A template port in the net: the boundary's env and result ports are the
# application's environment and result.
def tr(net: Net, +p: U32, +e: U32, +env: U32, +res: U32, +map: U32) -> Net & U32:
  tr.pick(U32.is_eq(node.of(p), e), net, p, env, res, map)

def code.if(yes: Bool, c: U32) -> U32:
  match yes:
    case True{}:
      c
    case False{}:
      0

def code.pass(+kb: U32, other: U32) -> U32:
  match kb:
    case 9:
      2
    case 18:
      2
    case _:
      code.if(is.value(kb), other)

# Which rule applies when agent kind ka meets kb, ka first (0: none).
def rule.code(ka: U32, +kb: U32) -> U32:
  match ka:
    case 12:
      match kb:
        case 8:
          1
        case _:
          code.pass(kb, 3)
    case 13:
      match kb:
        case 7:
          4
        case 5:
          5
        case 6:
          6
        case 9:
          7
        case 18:
          7
        case _:
          code.if(is.value(kb), 8)
    case 14:
      match kb:
        case 4:
          9
        case 8:
          10
        case _:
          code.pass(kb, 12)
    case 15:
      match kb:
        case 4:
          13
        case 8:
          14
        case _:
          code.pass(kb, 16)
    case 16:
      match kb:
        case 4:
          2
        case 8:
          18
        case _:
          code.pass(kb, 20)
    case 17:
      match kb:
        case 4:
          2
        case 8:
          22
        case _:
          code.pass(kb, 20)
    case 11:
      match kb:
        case 8:
          25
        case 4:
          26
        case 9:
          27
        case 18:
          28
        case _:
          code.if(is.value(kb), 29)
    case 3:
      match kb:
        case 8:
          30
        case 9:
          31
        case _:
          code.if(is.value(kb), 32)
    case 10:
      match kb:
        case 8:
          33
        case 9:
          34
        case 10:
          35
        case _:
          code.if(is.value(kb), 36)
    case _:
      0

def c.err(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      err

def c.stk(c: Ctl) -> List<&2, U32>:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      stk

def pop.done(net: Net, facing: Bool, +a: U32, +b: U32) -> Popped:
  match facing:
    case True{}:
      PPair{net, a, b}
    case False{}:
      PStale{net}

def pop.pb(+a: U32, +b: U32, ok: Bool, r: Net & U32) -> Popped:
  (net, +pb) = r
  pop.done(net, ok && U32.is_eq(pb, (a * 4 : U32)), a, b)

def pop.pa(+a: U32, +b: U32, ok: Bool, r: Net & U32) -> Popped:
  (net, +pa) = r
  pop.pb(a, b, ok && U32.is_eq(pa, (b * 4 : U32)), rd(net, (b * 8 + 1 : U32)))

def pop.kb(+a: U32, +b: U32, ok: Bool, r: Net & U32) -> Popped:
  (net, +kb) = r
  pop.pa(a, b, ok && Bool.not(U32.is_zero(kb)), rd(net, (a * 8 + 1 : U32)))

def pop.ka(+a: U32, +b: U32, r: Net & U32) -> Popped:
  (net, +ka) = r
  pop.kb(a, b, Bool.not(U32.is_zero(ka)), rd(net, (b * 8 : U32)))

def M(-A: Data) -> Type:
  CS -> CS & A

def M.pure(-A: Data, x: A) -> M(A):
  cs => (cs, x)

def M.run(-A: Data, -B: Data, f: A -> M(B), r: CS & A) -> CS & B:
  (cs, a) = r
  f(a)(cs)

def M.bind(-A: Data, -B: Data, m: M(A), f: A -> M(B)) -> M(B):
  cs => M.run(A, B, f, m(cs))

def m.back(q: Map<&2, List<&2, U32>>, r: Net & U32) -> CS & U32:
  (net, v) = r
  (CS{net, q}, v)

def m.rd.go(+i: U32, cs: CS) -> CS & U32:
  match cs:
    case CS{net, q}:
      m.back(q, rd(net, i))

def m.rd(+i: U32) -> M(U32):
  cs => m.rd.go(i, cs)

def m.peer(+p: U32) -> M(U32):
  m.rd(idx(p))

def m.ctl.back(q: Map<&2, List<&2, U32>>, r: Net & Ctl) -> CS & Ctl:
  (net, c) = r
  (CS{net, q}, c)

def m.ctl.go(cs: CS) -> CS & Ctl:
  match cs:
    case CS{net, q}:
      m.ctl.back(q, ctl.of(net))

def m.ctl() -> M(Ctl):
  cs => m.ctl.go(cs)

def m.setq.go(q: Map<&2, List<&2, U32>>, cs: CS) -> CS & Unit:
  match cs:
    case CS{net, old}:
      (CS{net, q}, Unit{})

def m.setq(q: Map<&2, List<&2, U32>>) -> M(Unit):
  cs => m.setq.go(q, cs)

def usage.add.got(+k: String, r: Map<&2, U32> & U32) -> Map<&2, U32>:
  (m, n) = r
  Map.set(&2, U32, m, k, (n + 1 : U32))

def usage.add(m: Map<&2, U32>, +k: String) -> Map<&2, U32>:
  usage.add.got(k, Map.get(U32, 0, m, k))

# How often the body uses each environment path, not looking inside
# closures; a projection chain over Env is one use of its path.
def usage(x: E.X, +path: String, acc: Map<&2, U32>) -> Map<&2, U32>:
  match x:
    case E.XEnv{}:
      usage.add(acc, path)
    case E.XLeft{c}:
      usage(c, "L" ++ path, acc)
    case E.XRight{c}:
      usage(c, "R" ++ path, acc)
    case E.XPair{a, b}:
      usage(b, "", usage(a, "", acc))
    case E.XSetEnv{c}:
      usage(c, "", acc)
    case _:
      acc

# The path of a pure projection chain over Env (envPathOf).
def env.path(x: E.X, +path: String) -> Maybe<&2, String>:
  match x:
    case E.XEnv{}:
      Some{path}
    case E.XLeft{c}:
      env.path(c, "L" ++ path)
    case E.XRight{c}:
      env.path(c, "R" ++ path)
    case _:
      None{}

def under.pick(yes: Bool, +t: String, n: U32, acc: Map<&2, U32>) -> Map<&2, U32>:
  match yes:
    case True{}:
      Map.set(&2, U32, acc, t, n)
    case False{}:
      acc

def under.one(+k: String, +step: Char, +m: Map<&2, U32>, acc: Map<&2, U32>) -> Map<&2, U32>:
  match k:
    case SCon{c, t}:
      under.pick(Char.is_eq(c, step), t, Pair.snd(Map<&2, U32>, U32, Map.get(U32, 0, m, k)), acc)
    case SNil{}:
      acc

# The part of a usage map under one first step, that step removed.
def under(xs: List<&2, String>, +step: Char, +m: Map<&2, U32>, acc: Map<&2, U32>) -> Map<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{+k, rest}:
      under(rest, step, m, under.one(k, step, m, acc))

def prefixed(xs: List<&2, String>, +step: String, +m: Map<&2, List<&2, U32>>, acc: Map<&2, List<&2, U32>>) ->
  Map<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case Con{+k, rest}:
      prefixed(rest, step, m, Map.set(&2, List<&2, U32>, acc, step ++ k,
               Pair.snd(Map<&2, List<&2, U32>>, List<&2, U32>, Map.get(List<&2, U32>, [], m, k))))

def wires.union(here: Map<&2, List<&2, U32>>, +l: Map<&2, List<&2, U32>>, +r: Map<&2, List<&2, U32>>) ->
  Map<&2, List<&2, U32>>:
  prefixed(Map.keys(&2, List<&2, U32>, r), "R", r, prefixed(Map.keys(&2, List<&2, U32>, l), "L", l, here))

# Environment wiring (envCopies, envWiring)
# -----------------------------------------

def here.pick(none: Bool, +direct: U32, ws: List<&2, U32>) -> Map<&2, List<&2, U32>>:
  match none:
    case True{}:
      Map.new(&2, List<&2, U32>)
    case False{}:
      Map.set(&2, List<&2, U32>, Map.new(&2, List<&2, U32>), "",
              List.take(&2, U32, ws, U32.to_nat(direct)))

def here(+direct: U32, ws: List<&2, U32>) -> Map<&2, List<&2, U32>>:
  here.pick(U32.is_zero(direct), direct, ws)

def wiring.after(+direct: U32, +desc: Bool, +subl: Map<&2, U32>, +subr: Map<&2, U32>, +ws: List<&2, U32>) -> WJ:
  WAfter{desc, here(direct, ws), List.drop(&2, U32, ws, U32.to_nat(direct)), subl, subr}

def plus.one(desc: Bool) -> U32:
  match desc:
    case True{}:
      1
    case False{}:
      0

def fuel() -> Nat:
  U32.to_nat(4294967295)

def fuel.of(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      fuel

def c.set.free(c: Ctl, +v: U32) -> Ctl:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      Ctl{stk, msgs, nmsg, bump, v, label, fuel, spent, err, emsg, cap}

def alloc.reuse(+id: U32, +k: U32, +a: U32, +b: U32, r: Net & U32) -> Net & U32:
  (net, +next) = r
  match net:
    case Net{mem, tpl, ctl}:
      init(Net{mem, tpl, c.set.free(ctl, next)}, id, k, a, b)

def free(net: Net, +n: U32) -> Net:
  match net:
    case Net{mem, tpl, +ctl}:
      Net{mem[(n * 8 : U32)] <- 0, tpl, c.set.free(ctl, n)} 

def push(net: Net, +a: U32, +b: U32) -> Net:
  match net:
    case Net{mem, tpl, ctl}:
      match ctl:
        case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
          Net{mem, tpl, Ctl{a <> b <> stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}}

def push.if(net: Net, yes: Bool, +a: U32, +b: U32) -> Net:
  match yes:
    case True{}:
      push(net, a, b)
    case False{}:
      net

def push.kb(+a: U32, +b: U32, ka: U32, r: Net & U32) -> Net:
  (net, +kb) = r
  push.if(net, interactive(ka) && interactive(kb), a, b)

def push.ka(+a: U32, +b: U32, r: Net & U32) -> Net:
  (net, +ka) = r
  push.kb(a, b, ka, kind.of(net, b))

def connect.push(net: Net, principal: Bool, +a: U32, +b: U32) -> Net:
  match principal:
    case True{}:
      push.ka(a, b, kind.of(net, a))
    case False{}:
      net

# Wire p to q; two principal ports meeting are an active pair (connect).
def connect(net: Net, +p: U32, +q: U32) -> Net:
  connect.push(wr(wr(net, idx(p), q), idx(q), p),
               U32.is_eq(slot.of(p), 0) && U32.is_eq(slot.of(q), 0), node.of(p), node.of(q))

def spend.ctl(out: Bool, c: Ctl) -> Ctl:
  match out:
    case True{}:
      match c:
        case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
          Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, 1, emsg, cap}
    case False{}:
      match c:
        case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
          Ctl{stk, msgs, nmsg, bump, free, label, (fuel - 1 : U32), (spent + 1 : U32), err, emsg, cap}

# One interaction, or the error that fuel ran out (spend).
def spend(net: Net) -> Net:
  match net:
    case Net{mem, tpl, +ctl}:
      Net{mem, tpl, spend.ctl(U32.is_zero(fuel.of(ctl)), ctl)}

# Allocation
# ----------

def c.free(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      free

def c.set.bump(c: Ctl, +v: U32) -> Ctl:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      Ctl{stk, msgs, nmsg, v, free, label, fuel, spent, err, emsg, cap}

def c.set.cap(c: Ctl, +v: U32) -> Ctl:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, v}

# Twice the room for agents, the old ones copied over.
def grow(net: Net) -> Net:
  match net:
    case Net{mem, tpl, +ctl}:
      Net{copy(U32.to_nat((c.cap(ctl) * 8 : U32)), 0, mem[0],
               Array.new(U32, 1n+U32.log2((c.cap(ctl) * 8 : U32)), 0)),
          tpl, c.set.cap(ctl, (c.cap(ctl) * 2 : U32))}

def alloc.at(net: Net, +id: U32, +k: U32, +a: U32, +b: U32) -> Net & U32:
  match net:
    case Net{mem, tpl, ctl}:
      init(Net{mem, tpl, c.set.bump(ctl, (id + 1 : U32))}, id, k, a, b)

def alloc.new(full: Bool, net: Net, +id: U32, +k: U32, +a: U32, +b: U32) -> Net & U32:
  match full:
    case True{}:
      alloc.at(grow(net), id, k, a, b)
    case False{}:
      alloc.at(net, id, k, a, b)

def alloc.pick(net: Net, reuse: Bool, +free: U32, +bump: U32, +cap: U32, +k: U32, +a: U32, +b: U32) -> Net & U32:
  match reuse:
    case True{}:
      alloc.reuse(free, k, a, b, rd(net, (free * 8 + 1 : U32)))
    case False{}:
      alloc.new(U32.is_ge(bump, cap), net, bump, k, a, b)

# A new agent of kind k with payload (a, b): the last one freed, else the
# next unused one.
def alloc(net: Net, +k: U32, +a: U32, +b: U32) -> Net & U32:
  match net:
    case Net{mem, tpl, +ctl}:
      alloc.pick(Net{mem, tpl, ctl}, Bool.not(U32.is_zero(c.free(ctl))), c.free(ctl), c.bump(ctl),
                 c.cap(ctl), k, a, b)

# Free: the agent's kind cleared and it heads the free list.
def delete(net: Net, +n: U32) -> Net:
  match net:
    case Net{mem, tpl, +ctl}:
      free(Net{mem[(n * 8 + 1 : U32)] <- c.free(ctl), tpl, ctl}, n)

def c.add.label(c: Ctl, +n: U32) -> Ctl:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      Ctl{stk, msgs, nmsg, bump, free, (label + n : U32), fuel, spent, err, emsg, cap}

# A label no Dup has yet (freshLabel).
def fresh.label(net: Net) -> Net & U32:
  match net:
    case Net{mem, tpl, +ctl}:
      (Net{mem, tpl, c.add.label(ctl, 1)}, c.label(ctl))

def c.add.msg(c: Ctl, m: String) -> Ctl:
  match c:
    case Ctl{stk, msgs, +nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      Ctl{stk, m <> msgs, (nmsg + 1 : U32), bump, free, label, fuel, spent, err, emsg, cap}

# A stuck value's message, kept aside; its number goes in the agent.
def add.msg(net: Net, m: String) -> Net & U32:
  match net:
    case Net{mem, tpl, +ctl}:
      (Net{mem, tpl, c.add.msg(ctl, m)}, c.nmsg(ctl))

def c.fail(c: Ctl, m: String) -> Ctl:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, 2, m, cap}

# An internal error (ICInternal): the run stops.
def fail(net: Net, m: String) -> Net:
  match net:
    case Net{mem, tpl, ctl}:
      Net{mem, tpl, c.fail(ctl, m)}

def alloc2.one(+k2: U32, +a2: U32, +b2: U32, r: Net & U32) -> Net & Ids:
  (net, +x) = r
  alloc2.two(x, alloc(net, k2, a2, b2))

def alloc2(net: Net, +k1: U32, +a1: U32, +b1: U32, +k2: U32, +a2: U32, +b2: U32) -> Net & Ids:
  alloc2.one(k2, a2, b2, alloc(net, k1, a1, b1))

def alloc4.one(+k3: U32, +a3: U32, +k4: U32, +a4: U32, r: Net & Ids) -> Net & Ids:
  (net, +i) = r
  match i:
    case Ids{x, y, a, b}:
      alloc4.two(x, y, alloc2(net, k3, a3, 0, k4, a4, 0))

# Four agents, no second payload.
def alloc4(net: Net, +k1: U32, +a1: U32, +k2: U32, +a2: U32, +k3: U32, +a3: U32, +k4: U32, +a4: U32) -> Net & Ids:
  alloc4.one(k3, a3, k4, a4, alloc2(net, k1, a1, 0, k2, a2, 0))

def eras.one(+x: U32, r: Net & U32) -> Net:
  (net, +e) = r
  connect(net, (e * 4 : U32), x)

def eras(xs: List<&2, U32>, net: Net) -> Net:
  match xs:
    case Nil{}:
      net
    case Con{+x, rest}:
      eras(rest, eras.one(x, alloc(net, era(), 0, 0)))

def stuck.sv(+r: U32, extras: List<&2, U32>, a: Net & U32) -> Net:
  (net, +sv) = a
  eras(extras, connect(net, (sv * 4 : U32), r))

def stuck.msg(+r: U32, extras: List<&2, U32>, a: Net & U32) -> Net:
  (net, +i) = a
  stuck.sv(r, extras, alloc(net, stuck(), i, 0))

# An ill-shaped interaction's result: a stuck value with a message, the
# leftovers erased (stuckAt).
def stuck.at(net: Net, +r: U32, msg: String, extras: List<&2, U32>) -> Net:
  stuck.msg(r, extras, add.msg(spend(net), msg))

def del2(net: Net, +n: U32, +m: U32) -> Net:
  delete(delete(net, n), m)

def r.apply.go(+i: NI, +j: NI, a: Net & U32) -> Net:
  (net, +ap) = a
  connect(connect(connect(net, port(ap, 0), ni.p1(j)), port(ap, 1), ni.p2(j)), port(ap, 2), ni.p1(i))

# SetEnv meets a pair: apply its function to its environment.
def r.setenv.pair(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.apply.go(i, j, alloc(del2(spend(net), n, m), apply(), 0, 0))

# An aborted or stuck value (and 0 under a projection) passes to the
# consumer's result (passThrough).
def r.pass(net: Net, +n: U32, +i: NI, +m: U32) -> Net:
  connect(delete(spend(net), n), port(m, 0), ni.p1(i))

def r.setenv.nonpair(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  stuck.at(del2(net, n, m), ni.p1(i), "SetEnv operand is " ++ show.ni(j) ++ ", not a pair", [])

def r.await.go(+i: NI, a: Net & U32) -> Net:
  (net, +sc) = a
  connect(connect(net, port(sc, 0), ni.p1(i)), port(sc, 1), ni.p2(i))

# A gate or abort applied: wait for its argument's shape (awaitShape).
def r.await(net: Net, +n: U32, +i: NI, +m: U32, +k: U32) -> Net:
  r.await.go(i, alloc(del2(spend(net), n, m), k, 0, 0))

def r.pass.app.go(+i: NI, +m: U32, a: Net & U32) -> Net:
  (net, +e) = a
  connect(connect(net, port(e, 0), ni.p1(i)), port(m, 0), ni.p2(i))

# An aborted or stuck function: its argument erased, itself the result
# (passApplication).
def r.pass.app(net: Net, +n: U32, +i: NI, +m: U32) -> Net:
  r.pass.app.go(i, m, alloc(delete(spend(net), n), era(), 0, 0))

def r.nonfunction.go(+n: U32, +i: NI, +m: U32, +j: NI, d: Net & String) -> Net:
  (net, shape) = d
  stuck.at(del2(net, n, m), ni.p2(i),
           "applied value is " ++ show.ni(j) ++ ", not a function: " ++ shape,
           ni.p1(i) <> comps(j))

# Applying data: stuck, its parts erased.
def r.apply.nonfunction(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.nonfunction.go(n, i, m, j, describe(U32.to_nat(64), DNode{m, 6n})(net))

def r.select.go(+r: U32, a: Net & U32) -> Net:
  (net, +sel) = a
  connect(net, port(sel, 0), r)

# A gate's scrutinee is 0: the left selector (selectZero); an abort's: the
# identity.
def r.select(net: Net, +n: U32, +i: NI, +m: U32, +tid: U32, +fi: U32) -> Net:
  r.select.go(ni.p1(i), alloc(del2(spend(net), n, m), ref(), tid, fi))

def r.scrut.pair.go(+i: NI, +j: NI, a: Net & Ids) -> Net:
  (net, +ids) = a
  match ids:
    case Ids{el, er, x, y}:
      r.select.go(ni.p1(i), alloc(connect(connect(net, port(el, 0), ni.p1(j)), port(er, 0), ni.p2(j)),
                                  ref(), 1, E.right.gate.ind()))

# A gate's scrutinee is a pair: erase it, the right selector.
def r.scrut.pair(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.scrut.pair.go(i, j, alloc2(del2(spend(net), n, m), era(), 0, 0, era(), 0, 0))

def r.nondata(net: Net, +n: U32, +i: NI, +m: U32, +j: NI, what: String) -> Net:
  stuck.at(del2(net, n, m), ni.p1(i), what ++ " is " ++ show.ni(j) ++ ", not data", [])

def r.abort.pair.go(+i: NI, +m: U32, a: Net & U32) -> Net:
  (net, +ab) = a
  connect(connect(net, port(ab, 1), port(m, 0)), port(ab, 0), ni.p1(i))

# Abort with a pair: the program aborts with that message.
def r.abort.pair(net: Net, +n: U32, +i: NI, +m: U32) -> Net:
  r.abort.pair.go(i, m, alloc(delete(spend(net), n), aborted(), 0, 0))

def r.project.go(+i: NI, +kept: U32, +dropped: U32, a: Net & U32) -> Net:
  (net, +e) = a
  connect(connect(net, port(e, 0), dropped), kept, ni.p1(i))

# Left or Right of a pair: keep one side, erase the other (projectPair).
def r.project(net: Net, +n: U32, +i: NI, +m: U32, +kept: U32, +dropped: U32) -> Net:
  r.project.go(i, kept, dropped, alloc(del2(spend(net), n, m), era(), 0, 0))

def r.nonpair(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  stuck.at(del2(net, n, m), ni.p1(i), "projection target is " ++ show.ni(j) ++ ", not a pair", [])

# Split meets a pair: its halves go their ways.
def r.split.pair(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  connect(connect(del2(spend(net), n, m), ni.p1(j), ni.p1(i)), ni.p2(j), ni.p2(i))

def r.two.leaves(+i: NI, a: Net & Ids) -> Net:
  (net, +ids) = a
  match ids:
    case Ids{x, y, z, w}:
      connect(connect(net, port(x, 0), ni.p1(i)), port(y, 0), ni.p2(i))

# Split meets 0: two 0s.
def r.split.zero(net: Net, +n: U32, +i: NI, +m: U32) -> Net:
  r.two.leaves(i, alloc2(del2(spend(net), n, m), zero(), 0, 0, zero(), 0, 0))

def r.split.aborted.two(+i: NI, +dm: U32, a: Net & Ids) -> Net:
  (net, +ids) = a
  match ids:
    case Ids{a1, a2, z, w}:
      connect(connect(connect(connect(net, port(a1, 1), port(dm, 1)), port(a1, 0), ni.p1(i)),
                      port(a2, 1), port(dm, 2)), port(a2, 0), ni.p2(i))

def r.split.aborted.one(+i: NI, +j: NI, a: Net & U32) -> Net:
  (net, +dm) = a
  r.split.aborted.two(i, dm, alloc2(connect(net, port(dm, 0), ni.p1(j)), aborted(), 0, 0, aborted(), 0, 0))

def r.split.aborted.label(+i: NI, +j: NI, a: Net & U32) -> Net:
  (net, +l) = a
  r.split.aborted.one(i, j, alloc(net, dup(), l, 0))

# Split meets an aborted value: both halves aborted with the message.
def r.split.aborted(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.split.aborted.label(i, j, fresh.label(del2(spend(net), n, m)))

# Split meets a stuck value: both halves stuck with its message.
def r.split.stuck(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.two.leaves(i, alloc2(del2(spend(net), n, m), stuck(), ni.a(j), 0, stuck(), ni.a(j), 0))

def r.split.nonpair.go(+i: NI, a: Net & U32) -> Net:
  (net, +msg) = a
  r.two.leaves(i, alloc2(net, stuck(), msg, 0, stuck(), msg, 0))

def r.split.nonpair(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.split.nonpair.go(i, add.msg(del2(spend(net), n, m), "projection target is " ++ show.ni(j) ++ ", not a pair"))

def r.era.pair.go(+j: NI, a: Net & Ids) -> Net:
  (net, +ids) = a
  match ids:
    case Ids{el, er, z, w}:
      connect(connect(net, port(el, 0), ni.p1(j)), port(er, 0), ni.p2(j))

# Erasing a pair erases its halves.
def r.era.pair(net: Net, +n: U32, +m: U32, +j: NI) -> Net:
  r.era.pair.go(j, alloc2(del2(spend(net), n, m), era(), 0, 0, era(), 0, 0))

def r.era.aborted.go(+j: NI, a: Net & U32) -> Net:
  (net, +e) = a
  connect(net, port(e, 0), ni.p1(j))

def r.era.aborted(net: Net, +n: U32, +m: U32, +j: NI) -> Net:
  r.era.aborted.go(j, alloc(del2(spend(net), n, m), era(), 0, 0))

def r.era.leaf(net: Net, +n: U32, +m: U32) -> Net:
  del2(spend(net), n, m)

def r.dup.pair.go(+i: NI, +j: NI, a: Net & Ids) -> Net:
  (net, +ids) = a
  match ids:
    case Ids{+p1, +p2, +dl, +dr}:
      connect(connect(connect(connect(connect(connect(connect(connect(net,
        port(dl, 0), ni.p1(j)), port(dr, 0), ni.p2(j)),
        port(p1, 1), port(dl, 1)), port(p1, 2), port(dr, 1)),
        port(p2, 1), port(dl, 2)), port(p2, 2), port(dr, 2)),
        port(p1, 0), ni.p1(i)), port(p2, 0), ni.p2(i))

# Copying a pair: two pairs over copies of each half (dup-pair).
def r.dup.pair(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.dup.pair.go(i, j, alloc4(del2(spend(net), n, m), pair(), 0, pair(), 0, dup(), ni.a(i), dup(), ni.a(i)))

def r.dup.aborted.go(+i: NI, +j: NI, a: Net & Ids) -> Net:
  (net, +ids) = a
  match ids:
    case Ids{+a1, +a2, +dm, w}:
      connect(connect(connect(connect(connect(net,
        port(dm, 0), ni.p1(j)), port(a1, 1), port(dm, 1)), port(a2, 1), port(dm, 2)),
        port(a1, 0), ni.p1(i)), port(a2, 0), ni.p2(i))

def r.dup.aborted(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.dup.aborted.go(i, j, alloc4(del2(spend(net), n, m), aborted(), 0, aborted(), 0, dup(), ni.a(i), zero(), 0))

def r.dup.commute.go(+i: NI, +j: NI, a: Net & Ids) -> Net:
  (net, +ids) = a
  match ids:
    case Ids{+m1, +m2, +n1, +n2}:
      connect(connect(connect(connect(connect(connect(connect(connect(net,
        port(m1, 0), ni.p1(i)), port(m2, 0), ni.p2(i)),
        port(n1, 0), ni.p1(j)), port(n2, 0), ni.p2(j)),
        port(m1, 1), port(n1, 1)), port(m1, 2), port(n2, 1)),
        port(m2, 1), port(n1, 2)), port(m2, 2), port(n2, 2))

# Two Dups: the same label annihilates, different labels commute.
def r.dup.dup(net: Net, +n: U32, +i: NI, +m: U32, +j: NI, same: Bool) -> Net:
  match same:
    case True{}:
      connect(connect(del2(spend(net), n, m), ni.p1(i), ni.p1(j)), ni.p2(i), ni.p2(j))
    case False{}:
      r.dup.commute.go(i, j, alloc4(del2(spend(net), n, m), dup(), ni.a(j), dup(), ni.a(j), dup(), ni.a(i), dup(), ni.a(i)))

# Copying a leaf value: two of it.
def r.dup.leaf(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.two.leaves(i, alloc2(del2(spend(net), n, m), ni.k(j), ni.a(j), ni.b(j), ni.k(j), ni.a(j), ni.b(j)))

# Guided copying (dupPlanFor, dupRegion)
# --------------------------------------

# How to copy a value of kind k by shape tag t (see the store), when it is
# materialized (its principal port faces us): 1 as a leaf, 2 as a pair of
# data, 3 as a pair by the pair shape's parts; 0 not at all, a Dup goes
# there instead (a frontier).
def rg.how(material: Bool, +t: U32, +k: U32) -> U32:
  match material:
    case False{}:
      0
    case True{}:
      match t:
        case 1:
          (code.if(U32.is_eq(k, zero()), 1) + code.if(U32.is_eq(k, pair()), 2) : U32)
        case 2:
          code.if(U32.is_eq(k, ref()), 1)
        case 4:
          code.if(U32.is_eq(k, pair()), 3)
        case _:
          0

def rg.leaf(rest: List<&2, RG>, vals: List<&2, U32>, r: Net & Ids) -> RgSt:
  (net, +ids) = r
  match ids:
    case Ids{+x, +y, z, w}:
      RgSt{net, rest, port(x, 0) <> port(y, 0) <> vals}

def rg.front(+p: U32, rest: List<&2, RG>, vals: List<&2, U32>, r: Net & U32) -> RgSt:
  (net, +d) = r
  RgSt{connect(net, port(d, 0), p), rest, port(d, 1) <> port(d, 2) <> vals}

def rg.halves(+s1: U32, +i: NI, rest: List<&2, RG>, vals: List<&2, U32>, r: Net & U32) -> RgSt:
  (net, +s2) = r
  RgSt{net, RgVisit{s1, ni.p1(i)} <> RgVisit{s2, ni.p2(i)} <> RgPair{} <> rest, vals}

def rg.act(how: U32, net: Net, +l: U32, +s: U32, +p: U32, +i: NI, rest: List<&2, RG>, vals: List<&2, U32>) -> RgSt:
  match how:
    case 1:
      rg.leaf(rest, vals, alloc2(delete(net, node.of(p)), ni.k(i), ni.a(i), ni.b(i), ni.k(i), ni.a(i), ni.b(i)))
    case 2:
      RgSt{delete(net, node.of(p)), RgVisit{s, ni.p1(i)} <> RgVisit{s, ni.p2(i)} <> RgPair{} <> rest, vals}
    case 3:
      rg.halves((s + 2 : U32), i, rest, vals, trd(delete(net, node.of(p)), (s + 1 : U32)))
    case _:
      rg.front(p, rest, vals, alloc(net, dup(), l, 0))

def rg.visit(+l: U32, +s: U32, +p: U32, rest: List<&2, RG>, vals: List<&2, U32>, +t: U32, r: Net & NI) -> RgSt:
  (net, +i) = r
  rg.act(rg.how(U32.is_zero(slot.of(p)), t, ni.k(i)), net, l, s, p, i, rest, vals)

def rg.tag(+l: U32, +s: U32, +p: U32, rest: List<&2, RG>, vals: List<&2, U32>, r: Net & U32) -> RgSt:
  (net, +t) = r
  rg.visit(l, s, p, rest, vals, t, info(net, node.of(p)))

def rg.pair(+a1: U32, +a2: U32, +b1: U32, +b2: U32, rest: List<&2, RG>, more: List<&2, U32>, r: Net & Ids) -> RgSt:
  (net, +ids) = r
  match ids:
    case Ids{+p1, +p2, z, w}:
      RgSt{connect(connect(connect(connect(net, port(p1, 1), a1), port(p1, 2), b1), port(p2, 1), a2), port(p2, 2), b2),
           rest, port(p1, 0) <> port(p2, 0) <> more}

def rg.step(net: Net, +l: U32, j: RG, rest: List<&2, RG>, vals: List<&2, U32>) -> RgSt:
  match j:
    case RgVisit{+s, +p}:
      rg.tag(l, s, p, rest, vals, trd(net, s))
    case RgPair{}:
      match vals:
        case b1 <> b2 <> a1 <> a2 <> more:
          rg.pair(a1, a2, b1, b2, rest, more, alloc2(net, pair(), 0, 0, pair(), 0, 0))
        case _:
          RgSt{fail(net, "dupRegion: nothing to pair"), [], vals}

# dupRegion: copy what the shapes vouch for and is materialized (pairs, 0s
# and code pointers), agent by agent, as notes, not interactions; a Dup of
# label l at every frontier. Any shape is correct: it only picks where
# copying is tried.
def region(fuel: Nat, +l: U32, st: RgSt) -> Net & List<&2, U32>:
  match fuel:
    case 0n:
      match st:
        case RgSt{net, jobs, vals}:
          (fail(net, "dupRegion: too deep"), vals)
    case 1n+f:
      match st:
        case RgSt{net, jobs, vals}:
          match jobs:
            case Nil{}:
              (net, vals)
            case Con{j, rest}:
              region(f, l, rg.step(net, l, j, rest, vals))

def r.dup.closure.go(+i: NI, r: Net & List<&2, U32>) -> Net:
  (net, vals) = r
  match vals:
    case p1 <> p2 <> more:
      connect(connect(net, p1, ni.p1(i)), p2, ni.p2(i))
    case _:
      fail(net, "dup-closure: no copies")

# Copying a closure whose code has a published capture layout
# (dup-closure): one interaction, then the pair copied by its plan at s.
def r.dup.closure(net: Net, +s: U32, +n: U32, +i: NI, +m: U32) -> Net:
  r.dup.closure.go(i, region(U32.to_nat(4294967295), ni.a(i),
    RgSt{delete(spend(net), n), [RgVisit{s, port(m, 0)}], []}))

def plan.at(+tid: U32, r: Net & U32) -> Net & U32:
  (net, +t) = r
  trd(net, (2 + t + tid : U32))

def plan.code(code: Bool, net: Net, +tid: U32) -> Net & U32:
  match code:
    case True{}:
      plan.at(tid, trd(net, 0))
    case False{}:
      (net, 0)

def plan.got(+p: U32, r: Net & NI) -> Net & U32:
  (net, +i) = r
  plan.code(U32.is_zero(slot.of(p)) && U32.is_eq(ni.k(i), ref()), net, ni.a(i))

# The plan for a pair whose head is at port p (dupPlanFor): when p is a
# materialized code pointer whose code has published guidance, where its
# closures' shape is in the store; else 0.
def plan.of(net: Net, +p: U32) -> Net & U32:
  plan.got(p, info(net, node.of(p)))

def r.dup.pick(plain: Bool, net: Net, +s: U32, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  match plain:
    case True{}:
      r.dup.pair(net, n, i, m, j)
    case False{}:
      r.dup.closure(net, s, n, i, m)

def r.dup.planned.got(+n: U32, +i: NI, +m: U32, +j: NI, r: Net & U32) -> Net:
  (net, +s) = r
  r.dup.pick(U32.is_zero(s), net, s, n, i, m, j)

# Copying a pair: by plan when it is a closure whose code has published
# guidance, else generically.
def r.dup.planned(net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  r.dup.planned.got(n, i, m, j, plan.of(net, ni.p1(j)))

# Instantiation
# -------------
#
# The template store: word 0 the number of templates T, word 1 where the
# scratch map begins (a template agent's number -> the agent copied from
# it), then each template's offset, then where each template's plan is (0:
# none), then the templates: K agents, the index of its boundary (Ext), its
# labels, W wires, then K (kind, a, b) and W (p, q) wires in the order
# Haskell connects them (a port is agent*4+slot, numbered within the
# template); then the plans: the shape of the template's closures, a code
# pointer and the capture EAL published for its code, as tags: 1 CapData,
# 2 CapCode, 3 CapOther, 4 CapPair followed by where its second part is,
# then its first part.

def inst.node.b(+i: U32, +base: U32, +map: U32, +k: U32, +a: U32, r: Net & U32) -> Net:
  (net, +b) = r
  inst.node.id(map, i, alloc(net, k, relabel(U32.is_eq(k, 10), a, base), b))

def inst.node.a(+i: U32, +at: U32, +base: U32, +map: U32, +k: U32, r: Net & U32) -> Net:
  (net, +a) = r
  inst.node.b(i, base, map, k, a, trd(net, (at + 2 : U32)))

def inst.node.k(+i: U32, +at: U32, +base: U32, +map: U32, r: Net & U32) -> Net:
  (net, +k) = r
  inst.node.a(i, at, base, map, k, trd(net, (at + 1 : U32)))

def inst.node(skip: Bool, net: Net, +i: U32, +off: U32, +base: U32, +map: U32) -> Net:
  match skip:
    case True{}:
      net
    case False{}:
      inst.node.k(i, (off + 4 + 3 * i : U32), base, map, trd(net, (off + 4 + 3 * i : U32)))

# Copy every agent but the boundary, noting each copy in the map.
def inst.nodes(k: Nat, +i: U32, +off: U32, +e: U32, +base: U32, +map: U32, net: Net) -> Net:
  match k:
    case 0n:
      net
    case 1n+rest:
      inst.nodes(rest, (i + 1 : U32), off, e, base, map,
                 inst.node(U32.is_eq(i, e), net, i, off, base, map))

def inst.wire.q2(+p2: U32, r: Net & U32) -> Net:
  (net, +q2) = r
  connect(net, p2, q2)

def inst.wire.p2(+q: U32, +e: U32, +env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +p2) = r
  inst.wire.q2(p2, tr(net, q, e, env, res, map))

def inst.wire.q(+p: U32, +e: U32, +env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +q) = r
  inst.wire.p2(q, e, env, res, map, tr(net, p, e, env, res, map))

def inst.wire.p(+at: U32, +e: U32, +env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +p) = r
  inst.wire.q(p, e, env, res, map, trd(net, (at + 1 : U32)))

# Connect the copies as the template is wired.
def inst.wires(w: Nat, +at: U32, +e: U32, +env: U32, +res: U32, +map: U32, net: Net) -> Net:
  match w:
    case 0n:
      net
    case 1n+rest:
      inst.wires(rest, (at + 2 : U32), e, env, res, map,
                 inst.wire.p(at, e, env, res, map, trd(net, at)))

def inst.body(+off: U32, +k: U32, +e: U32, +w: U32, +env: U32, +res: U32, +map: U32, +base: U32, net: Net) -> Net:
  inst.wires(U32.to_nat(w), (off + 4 + 3 * k : U32), e, env, res, map,
             inst.nodes(U32.to_nat(k), 0, off, e, base, map, net))

def inst.labels(+off: U32, +k: U32, +e: U32, +w: U32, +env: U32, +res: U32, +map: U32, +l: U32, net: Net) -> Net:
  match net:
    case Net{mem, tpl, +ctl}:
      inst.body(off, k, e, w, env, res, map, c.label(ctl), Net{mem, tpl, c.add.label(ctl, l)})

def inst.w(+off: U32, +k: U32, +e: U32, +l: U32, +env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +w) = r
  inst.labels(off, k, e, w, env, res, map, l, net)

def inst.l(+off: U32, +k: U32, +e: U32, +env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +l) = r
  inst.w(off, k, e, l, env, res, map, trd(net, (off + 3 : U32)))

def inst.e(+off: U32, +k: U32, +env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +e) = r
  inst.l(off, k, e, env, res, map, trd(net, (off + 2 : U32)))

def inst.k(+off: U32, +env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +k) = r
  inst.e(off, k, env, res, map, trd(net, (off + 1 : U32)))

def inst.off(+env: U32, +res: U32, +map: U32, r: Net & U32) -> Net:
  (net, +off) = r
  inst.k(off, env, res, map, trd(net, off))

def inst.map(+tid: U32, +env: U32, +res: U32, r: Net & U32) -> Net:
  (net, +map) = r
  inst.off(env, res, map, trd(net, (2 + tid : U32)))

# A closure's body, copied fresh from its template, with its labels made
# new, between the application's environment and result (instantiate).
def instantiate(net: Net, +tid: U32, +env: U32, +res: U32) -> Net:
  inst.map(tid, env, res, trd(net, 1))

# Dispatch
# --------

# Fire rule c: agent n (info i) meeting agent m (info j).
def apply.rule(c: U32, net: Net, +n: U32, +i: NI, +m: U32, +j: NI) -> Net:
  match c:
    case 1:
      r.setenv.pair(net, n, i, m, j)
    case 2:
      r.pass(net, n, i, m)
    case 3:
      r.setenv.nonpair(net, n, i, m, j)
    case 4:
      instantiate(del2(spend(net), n, m), ni.a(j), ni.p1(i), ni.p2(i))
    case 5:
      r.await(net, n, i, m, scrut())
    case 6:
      r.await(net, n, i, m, scrut.abort())
    case 7:
      r.pass.app(net, n, i, m)
    case 8:
      r.apply.nonfunction(net, n, i, m, j)
    case 9:
      r.select(net, n, i, m, 0, E.left.gate.ind())
    case 10:
      r.scrut.pair(net, n, i, m, j)
    case 12:
      r.nondata(net, n, i, m, j, "gate scrutinee")
    case 13:
      r.select(net, n, i, m, 2, E.abort.ind())
    case 14:
      r.abort.pair(net, n, i, m)
    case 16:
      r.nondata(net, n, i, m, j, "abort message")
    case 18:
      r.project(net, n, i, m, ni.p1(j), ni.p2(j))
    case 20:
      r.nonpair(net, n, i, m, j)
    case 22:
      r.project(net, n, i, m, ni.p2(j), ni.p1(j))
    case 25:
      r.split.pair(net, n, i, m, j)
    case 26:
      r.split.zero(net, n, i, m)
    case 27:
      r.split.aborted(net, n, i, m, j)
    case 28:
      r.split.stuck(net, n, i, m, j)
    case 29:
      r.split.nonpair(net, n, i, m, j)
    case 30:
      r.era.pair(net, n, m, j)
    case 31:
      r.era.aborted(net, n, m, j)
    case 32:
      r.era.leaf(net, n, m)
    case 33:
      r.dup.planned(net, n, i, m, j)
    case 34:
      r.dup.aborted(net, n, i, m, j)
    case 35:
      r.dup.dup(net, n, i, m, j, U32.is_eq(ni.a(i), ni.a(j)))
    case 36:
      r.dup.leaf(net, n, i, m, j)
    case _:
      fail(net, "no rule")

def fire.flip(zero: Bool, net: Net, +a: U32, +ia: NI, +b: U32, +ib: NI, +c: U32) -> Net:
  match zero:
    case True{}:
      fail(net, "no interaction rule for " ++ show.ni(ia) ++ " meeting " ++ show.ni(ib))
    case False{}:
      apply.rule(c, net, b, ib, a, ia)

def fire.try(zero: Bool, net: Net, +a: U32, +ia: NI, +b: U32, +ib: NI, +c: U32) -> Net:
  match zero:
    case True{}:
      fire.flip(U32.is_zero(rule.code(ni.k(ib), ni.k(ia))), net, a, ia, b, ib, rule.code(ni.k(ib), ni.k(ia)))
    case False{}:
      apply.rule(c, net, a, ia, b, ib)

def fire.b(+a: U32, +b: U32, +ia: NI, r: Net & NI) -> Net:
  (net, +ib) = r
  fire.try(U32.is_zero(rule.code(ni.k(ia), ni.k(ib))), net, a, ia, b, ib, rule.code(ni.k(ia), ni.k(ib)))

def fire.a(+a: U32, +b: U32, r: Net & NI) -> Net:
  (net, +ia) = r
  fire.b(a, b, ia, info(net, b))

# An active pair: its rule, tried as (a, b), then as (b, a) (fire).
def fire(net: Net, +a: U32, +b: U32) -> Net:
  fire.a(a, b, info(net, a))

# The loop
# --------

def c.set.stk(c: Ctl, stk: List<&2, U32>) -> Ctl:
  match c:
    case Ctl{old, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}

def set.stk(net: Net, stk: List<&2, U32>) -> Net:
  match net:
    case Net{mem, tpl, ctl}:
      Net{mem, tpl, c.set.stk(ctl, stk)}

def pop.list(net: Net, stk: List<&2, U32>) -> Popped:
  match stk:
    case Con{+a, Con{+b, rest}}:
      pop.ka(a, b, rd(set.stk(net, rest), (a * 8 : U32)))
    case _:
      PEmpty{net}

def pop.err(ok: Bool, net: Net, stk: List<&2, U32>) -> Popped:
  match ok:
    case True{}:
      pop.list(net, stk)
    case False{}:
      PEmpty{net}

# The next active pair, if it is still facing (pop).
def pop(net: Net) -> Popped:
  match net:
    case Net{mem, tpl, +ctl}:
      pop.err(U32.is_zero(c.err(ctl)), Net{mem, tpl, ctl}, c.stk(ctl))

# Fire active pairs until none is left, the fuel runs out or a rule fails
# (reduce).
def reduce(fuel: Nat, st: Popped) -> Net:
  match fuel:
    case 0n:
      match st:
        case PEmpty{net}:
          net
        case PStale{net}:
          net
        case PPair{net, a, b}:
          net
    case 1n+f:
      match st:
        case PEmpty{net}:
          net
        case PStale{net}:
          reduce(f, pop(net))
        case PPair{net, a, b}:
          reduce(f, pop(fire(net, a, b)))

# Building nets
# -------------

def m.alloc.go(+k: U32, +a: U32, +b: U32, cs: CS) -> CS & U32:
  match cs:
    case CS{net, q}:
      m.back(q, alloc(net, k, a, b))

def m.alloc(+k: U32, +a: U32, +b: U32) -> M(U32):
  cs => m.alloc.go(k, a, b, cs)

def m.connect.go(+p: U32, +r: U32, cs: CS) -> CS & Unit:
  match cs:
    case CS{net, q}:
      (CS{connect(net, p, r), q}, Unit{})

def m.connect(+p: U32, +q: U32) -> M(Unit):
  cs => m.connect.go(p, q, cs)

def m.delete.go(+n: U32, cs: CS) -> CS & Unit:
  match cs:
    case CS{net, q}:
      (CS{delete(net, n), q}, Unit{})

def m.delete(+n: U32) -> M(Unit):
  cs => m.delete.go(n, cs)

def m.label.go(cs: CS) -> CS & U32:
  match cs:
    case CS{net, q}:
      m.back(q, fresh.label(net))

def m.label() -> M(U32):
  cs => m.label.go(cs)

def m.fail.go(msg: String, cs: CS) -> CS & U32:
  match cs:
    case CS{net, q}:
      (CS{fail(net, msg), q}, 0)

def m.fail(msg: String) -> M(U32):
  cs => m.fail.go(msg, cs)

def take.got(+path: String, q: Map<&2, List<&2, U32>>, net: Net, ws: List<&2, U32>) -> CS & U32:
  match ws:
    case Con{w, rest}:
      (CS{net, Map.set(&2, List<&2, U32>, q, path, rest)}, w)
    case Nil{}:
      (CS{fail(net, "compileTerm: no env wire for path " ++ path), q}, 0)

def take.go(+path: String, cs: CS) -> CS & U32:
  match cs:
    case CS{net, +q}:
      take.got(path, q, net, Pair.snd(Map<&2, List<&2, U32>>, List<&2, U32>, Map.get(List<&2, U32>, [], q, path)))

# The next wire for an environment path (takeEnvWire).
def m.take(+path: String) -> M(U32):
  cs => take.go(path, cs)

# Environment use (EnvUsage.usage over envView)
# ---------------------------------------------

# n copies of the wire from src: none erases it, one is itself, more go
# through a chain of Dups with fresh labels.
def copies(n: Nat, +src: U32) -> M(List<&2, U32>):
  match n:
    case 0n:
      do M<List<&2, U32>>:
        e : U32 <- m.alloc(era(), 0, 0)
        u : Unit <- m.connect(src, (e * 4 : U32))
        return []
    case 1n+k:
      match k:
        case 0n:
          M.pure(List<&2, U32>, [src])
        case 1n+j:
          do M<List<&2, U32>>:
            l : U32 <- m.label()
            +d : U32 <- m.alloc(dup(), l, 0)
            u : Unit <- m.connect(src, (d * 4 : U32))
            rest : List<&2, U32> <- copies(k, (d * 4 + 2 : U32))
            return (d * 4 + 1 : U32) <> rest

# The wires that deliver the environment to each path it is used at: its
# direct uses, and a Split for the paths below (envWiring).
def wiring(+fuel: Nat, j: WJ) -> M(Map<&2, List<&2, U32>>):
  match fuel:
    case 0n:
      M.pure(Map<&2, List<&2, U32>>, Map.new(&2, List<&2, U32>))
    case 1n+f:
      match j:
        case WStart{+src, +use}:
          +direct = Pair.snd(Map<&2, U32>, U32, Map.get(U32, 0, use, ""))
          +subl = under(Map.keys(&2, U32, use), 'L', use, Map.new(&2, U32))
          +subr = under(Map.keys(&2, U32, use), 'R', use, Map.new(&2, U32))
          +desc = Nat.is_ne(Nat.add(Map.size(&2, U32, subl), Map.size(&2, U32, subr)), 0n)
          do M<Map<&2, List<&2, U32>>>:
            ws : List<&2, U32> <- copies(U32.to_nat((direct + plus.one(desc) : U32)), src)
            wiring(f, wiring.after(direct, desc, subl, subr, ws))
        case WAfter{desc, here, rest, subl, subr}:
          match desc:
            case False{}:
              M.pure(Map<&2, List<&2, U32>>, here)
            case True{}:
              match rest:
                case Con{dw, x}:
                  do M<Map<&2, List<&2, U32>>>:
                    +sp : U32 <- m.alloc(split(), 0, 0)
                    u : Unit <- m.connect((sp * 4 : U32), dw)
                    wl : Map<&2, List<&2, U32>> <- wiring(f, WStart{(sp * 4 + 1 : U32), subl})
                    wr : Map<&2, List<&2, U32>> <- wiring(f, WStart{(sp * 4 + 2 : U32), subr})
                    return wires.union(here, wl, wr)
                case Nil{}:
                  M.pure(Map<&2, List<&2, U32>>, here)

# Compiling terms (compileTerm, compileData)
# ------------------------------------------

def value(+k: U32, +a: U32, +b: U32) -> M(U32):
  do M<U32>:
    id : U32 <- m.alloc(k, a, b)
    return (id * 4 : U32)

# A term's net; the port it delivers its value on.
def compile(+fuel: Nat, j: CJ) -> M(U32):
  match fuel:
    case 0n:
      m.fail("compileTerm: too deep")
    case 1n+f:
      match j:
        case CTerm{x}:
          match x:
            case E.XZero{}:
              value(zero(), 0, 0)
            case E.XPair{a, b}:
              do M<U32>:
                +p : U32 <- m.alloc(pair(), 0, 0)
                pa : U32 <- compile(f, CTerm{a})
                u1 : Unit <- m.connect((p * 4 + 1 : U32), pa)
                pb : U32 <- compile(f, CTerm{b})
                u2 : Unit <- m.connect((p * 4 + 2 : U32), pb)
                return (p * 4 : U32)
            case E.XEnv{}:
              m.take("")
            case E.XSetEnv{c}:
              compile(f, CProj{None{}, setenv(), c})
            case E.XLeft{+c}:
              compile(f, CProj{env.path(c, "L"), left(), c})
            case E.XRight{+c}:
              compile(f, CProj{env.path(c, "R"), right(), c})
            case E.XGate{}:
              value(gate(), 0, 0)
            case E.XAbort{}:
              value(abort(), 0, 0)
            case E.XAborted{m}:
              do M<U32>:
                +a : U32 <- m.alloc(aborted(), 0, 0)
                pm : U32 <- compile(f, CTerm{m})
                u : Unit <- m.connect((a * 4 + 1 : U32), pm)
                return (a * 4 : U32)
            case E.XTpl{tid, fi}:
              value(ref(), tid, fi)
            case _:
              m.fail("compileTerm: not a compiled expression")
        case CProj{path, +k, c}:
          match path:
            case Some{p}:
              m.take(p)
            case None{}:
              do M<U32>:
                +n : U32 <- m.alloc(k, 0, 0)
                pc : U32 <- compile(f, CTerm{c})
                u : Unit <- m.connect((n * 4 : U32), pc)
                return (n * 4 + 1 : U32)

# A body between a boundary agent's env port (0) and result port (1)
# (compileBody); the boundary.
def body(+x: E.X) -> M(U32):
  do M<U32>:
    +ext : U32 <- m.alloc(ext(), 0, 0)
    q : Map<&2, List<&2, U32>> <- wiring(fuel(), WStart{(ext * 4 : U32), usage(x, "", Map.new(&2, U32))})
    u : Unit <- m.setq(q)
    root : U32 <- compile(fuel(), CTerm{x})
    u2 : Unit <- m.connect((ext * 4 + 1 : U32), root)
    return ext

# Templates
# ---------

def C(-A: Data) -> Type:
  Coll -> A & Coll

def C.pure(-A: Data, x: A) -> C(A):
  c => (x, c)

def C.run(-A: Data, -B: Data, f: A -> C(B), r: A & Coll) -> B & Coll:
  (a, c) = r
  f(a)(c)

def C.bind(-A: Data, -B: Data, m: C(A), f: A -> C(B)) -> C(B):
  c => C.run(A, B, f, m(c))

# A collected body as EAL lifts it (Lift), each template reference its
# code's hash. Locations do not reach the hash.
def lifted(+hs: Map<&2, String>, x: E.X) -> Lf.L:
  match x:
    case E.XZero{}:
      Lf.LZero{Lc.Unknown{}}
    case E.XPair{a, b}:
      Lf.LPair{Lc.Unknown{}, lifted(hs, a), lifted(hs, b)}
    case E.XEnv{}:
      Lf.LEnv{Lc.Unknown{}}
    case E.XSetEnv{a}:
      Lf.LSetEnv{Lc.Unknown{}, lifted(hs, a)}
    case E.XGate{}:
      Lf.LGate{Lc.Unknown{}}
    case E.XLeft{a}:
      Lf.LLeft{Lc.Unknown{}, lifted(hs, a)}
    case E.XRight{a}:
      Lf.LRight{Lc.Unknown{}, lifted(hs, a)}
    case E.XTpl{tid, fi}:
      Lf.LRef{Lc.Unknown{}, Pair.snd(Map<&2, String>, String, Map.get(String, "", hs, U32.show(tid)))}
    case _:
      Lf.LAbort{Lc.Unknown{}}

# A body's code hash (tplHash, hashLiftedBody).
def code.of(+hs: Map<&2, String>, x: E.X) -> String:
  Lf.hash(lifted(hs, x))

def c.named(+next: U32, +fi: U32, +body: E.X, orig: E.X, srcs: List<&2, Src>, hs: Maybe<&2, Map<&2, String>>) -> E.X & Coll:
  match hs:
    case None{}:
      (E.XTpl{next, fi}, Coll{(next + 1 : U32), Src{next, fi, body, orig, ""} <> srcs, None{}})
    case Some{+m}:
      +code = code.of(m, body)
      (E.XTpl{next, fi}, Coll{(next + 1 : U32), Src{next, fi, body, orig, code} <> srcs,
                             Some{Map.set(&2, String, m, U32.show(next), code)}})

def c.add.go(+fi: U32, body: E.X, orig: E.X, c: Coll) -> E.X & Coll:
  match c:
    case Coll{+next, srcs, hs}:
      c.named(next, fi, body, orig, srcs, hs)

def c.add(+fi: U32, body: E.X, orig: E.X) -> C(E.X):
  c => c.add.go(fi, body, orig, c)

# Every closure body becomes a template, innermost first, each Defer a
# reference to its template.
def collect(x: E.X) -> C(E.X):
  match x:
    case E.XDefer{fi, +b}:
      do C<E.X>:
        b2 : E.X <- collect(b)
        c.add(fi, b2, b)
    case E.XPair{a, b}:
      do C<E.X>:
        a2 : E.X <- collect(a)
        b2 : E.X <- collect(b)
        return E.XPair{a2, b2}
    case E.XSetEnv{a}:
      do C<E.X>:
        a2 : E.X <- collect(a)
        return E.XSetEnv{a2}
    case E.XLeft{a}:
      do C<E.X>:
        a2 : E.X <- collect(a)
        return E.XLeft{a2}
    case E.XRight{a}:
      do C<E.X>:
        a2 : E.X <- collect(a)
        return E.XRight{a2}
    case other:
      C.pure(E.X, other)

def selector(+tid: U32, +fi: U32, +body: E.X) -> Src:
  Src{tid, fi, body, body, code.of(Map.new(&2, String), body)}

# The gate's selectors and the identity abort gives: templates 0, 1, 2.
def selectors() -> List<&2, Src>:
  [selector(2, E.abort.ind(), E.XEnv{}),
   selector(1, E.right.gate.ind(), E.XRight{E.XEnv{}}),
   selector(0, E.left.gate.ind(), E.XLeft{E.XEnv{}})]

def ser.wire.at(lower: Bool, +p: U32, +q: U32, s: Ser) -> Ser:
  match lower:
    case True{}:
      match s:
        case Ser{nodes, wires, w}:
          Ser{nodes, (q - 4 : U32) <> (p - 4 : U32) <> wires, (w + 1 : U32)}
    case False{}:
      s

def ser.wire(+p: U32, +q: U32, s: Ser) -> Ser:
  ser.wire.at(U32.is_lt(p, q), p, q, s)

def ser.wire.if(yes: Bool, +p: U32, +q: U32, s: Ser) -> Ser:
  match yes:
    case True{}:
      ser.wire(p, q, s)
    case False{}:
      s

def ser.wires(+ar: U32, +id: U32, +p0: U32, +p1: U32, +p2: U32, s: Ser) -> Ser:
  ser.wire.if(U32.is_gt(ar, 2), (id * 4 + 2 : U32), p2,
    ser.wire.if(U32.is_gt(ar, 1), (id * 4 + 1 : U32), p1,
      ser.wire.if(True{}, (id * 4 : U32), p0, s)))

def ser.add(+k: U32, +a: U32, +b: U32, s: Ser) -> Ser:
  match s:
    case Ser{nodes, wires, w}:
      Ser{b <> a <> k <> nodes, wires, w}

# Read agents id.. of the scratch net into a template.
def ser.nodes(n: Nat, +id: U32, s: Ser) -> M(Ser):
  match n:
    case 0n:
      M.pure(Ser, s)
    case 1n+k:
      do M<Ser>:
        +kind : U32 <- m.rd((id * 8 : U32))
        a : U32 <- m.rd((id * 8 + 4 : U32))
        b : U32 <- m.rd((id * 8 + 5 : U32))
        p0 : U32 <- m.peer((id * 4 : U32))
        p1 : U32 <- m.peer((id * 4 + 1 : U32))
        p2 : U32 <- m.peer((id * 4 + 2 : U32))
        ser.nodes(k, (id + 1 : U32), ser.add(kind, a, b, ser.wires(arity(kind), id, p0, p1, p2, s)))

def c.spent(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      spent

def c.emsg(c: Ctl) -> String:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      emsg

def c.msgs(c: Ctl) -> List<&2, String>:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      msgs

def tpl.assemble(+c: Ctl, s: Ser) -> List<&2, U32>:
  match s:
    case Ser{nodes, wires, w}:
      (c.bump(c) - 1 : U32) <> 0 <> c.label(c) <> w
        <> List.append(&2, U32, List.reverse(&2, U32, nodes), List.reverse(&2, U32, wires))

# One template's words: its body compiled in a fresh scratch net, read out.
def tpl.words(+x: E.X) -> M(List<&2, U32>):
  do M<List<&2, U32>>:
    ext : U32 <- body(x)
    +c : Ctl <- m.ctl()
    s : Ser <- ser.nodes(U32.to_nat((c.bump(c) - 1 : U32)), 1, Ser{[], [], 0})
    return tpl.assemble(c, s)

def reset.ctl(c: Ctl, +fuel: U32) -> Ctl:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, old, spent, err, emsg, cap}:
      Ctl{[], [], 0, 1, 0, 0, fuel, 0, 0, "", cap}

# A net emptied for a new run: no agents, all fuel.
def reset(net: Net, +fuel: U32) -> Net:
  match net:
    case Net{mem, tpl, ctl}:
      Net{mem, tpl, reset.ctl(ctl, fuel)}

def cs.net(cs: CS) -> Net:
  match cs:
    case CS{net, q}:
      net

def src.body(s: Src) -> E.X:
  match s:
    case Src{tid, fi, body, orig, code}:
      body

# Every template's words, in template order.
def tpls(srcs: List<&2, Src>, r: CS & List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match srcs:
    case Nil{}:
      (cs, last) = r
      List.reverse(&2, List<&2, U32>, last <> acc)
    case Con{s, rest}:
      (cs, last) = r
      tpls(rest, tpl.words(src.body(s))(CS{reset(cs.net(cs), 0), Map.new(&2, List<&2, U32>)}), last <> acc)

def lens(ws: List<&2, List<&2, U32>>, +at: U32) -> List<&2, U32>:
  match ws:
    case Nil{}:
      []
    case Con{w, rest}:
      at <> lens(rest, (at + U32.from_nat(List.length(&2, U32, w)) : U32))

def max.k.of(w: List<&2, U32>) -> U32:
  match w:
    case Con{k, rest}:
      k
    case Nil{}:
      0

def max.k(ws: List<&2, List<&2, U32>>, +m: U32) -> U32:
  match ws:
    case Nil{}:
      m
    case Con{w, rest}:
      max.k(rest, U32.max(m, max.k.of(w)))

# Plans
# -----

# The words a capture shape takes in the store.
def shape.size(s: Lf.Shape) -> U32:
  match s:
    case Lf.CapPair{a, b}:
      (2 + shape.size(a) + shape.size(b) : U32)
    case _:
      1

# A capture shape's words, placed at offset at.
def shape.words(s: Lf.Shape, +at: U32) -> List<&2, U32>:
  match s:
    case Lf.CapData{}:
      [1]
    case Lf.CapCode{}:
      [2]
    case Lf.CapOther{}:
      [3]
    case Lf.CapPair{+a, b}:
      +at2 = (at + 2 + shape.size(a) : U32)
      4 <> at2 <> List.append(&2, U32, shape.words(a, (at + 2 : U32)), shape.words(b, at2))

def plan.pick(has: Bool, +code: String, g: Map<&2, Lf.Shape>) -> Maybe<&2, Lf.Shape>:
  match has:
    case True{}:
      Some{Pair.snd(Map<&2, Lf.Shape>, Lf.Shape, Map.get(Lf.Shape, Lf.CapOther{}, g, code))}
    case False{}:
      None{}

def plan.has(+code: String, r: Map<&2, Lf.Shape> & Bool) -> Maybe<&2, Lf.Shape>:
  (g, has) = r
  plan.pick(has, code, g)

# Each template's closures' shape, when EAL published a capture layout for
# its code (ealCaptureLayouts, by hash).
def plans(+g: Map<&2, Lf.Shape>, srcs: List<&2, Src>) -> List<&2, Maybe<&2, Lf.Shape>>:
  match srcs:
    case Nil{}:
      []
    case Con{s, rest}:
      match s:
        case Src{tid, fi, body, orig, +code}:
          plan.has(code, Map.has(&2, Lf.Shape, g, code)) <> plans(g, rest)

def plan.offs(ps: List<&2, Maybe<&2, Lf.Shape>>, +at: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      []
    case Con{p, rest}:
      match p:
        case None{}:
          0 <> plan.offs(rest, at)
        case Some{s}:
          at <> plan.offs(rest, (at + 3 + shape.size(s) : U32))

def plan.words(ps: List<&2, Maybe<&2, Lf.Shape>>, +at: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      []
    case Con{p, rest}:
      match p:
        case None{}:
          plan.words(rest, at)
        case Some{+s}:
          List.append(&2, U32, shape.words(Lf.CapPair{Lf.CapCode{}, s}, at),
            plan.words(rest, (at + 3 + shape.size(s) : U32)))

# The store's words: count, map base, template offsets, plan offsets,
# templates, plans.
def store(+ws: List<&2, List<&2, U32>>, +ps: List<&2, Maybe<&2, Lf.Shape>>) -> List<&2, U32>:
  +t = U32.from_nat(List.length(&2, List<&2, U32>, ws))
  +flat = List.concat(&2, U32, ws)
  +at = (2 + 2 * t + U32.from_nat(List.length(&2, U32, flat)) : U32)
  +pw = plan.words(ps, at)
  t <> (at + U32.from_nat(List.length(&2, U32, pw)) : U32)
    <> List.append(&2, U32, lens(ws, (2 + 2 * t : U32)),
         List.append(&2, U32, plan.offs(ps, at), List.append(&2, U32, flat, pw)))

def bodies(srcs: List<&2, Src>, acc: Map<&2, E.X>) -> Map<&2, E.X>:
  match srcs:
    case Nil{}:
      acc
    case Con{s, rest}:
      match s:
        case Src{tid, fi, body, orig, code}:
          bodies(rest, Map.set(&2, E.X, acc, U32.show(tid), orig))

def depth.of(+n: U32) -> Nat:
  1n+U32.log2(n)

def scratch() -> Net:
  Net{Array.new(U32, 16n, 0), Array.new(U32, 2n, 0), Ctl{[], [], 0, 1, 0, 0, 0, 0, 0, "", 8192}}

def prepared.with(+g: Map<&2, Lf.Shape>, entry: E.X, +srcs: List<&2, Src>) -> Prog:
  +ws = tpls(srcs, (CS{scratch(), Map.new(&2, List<&2, U32>)}, []), [])
  Prog{entry, bodies(srcs, Map.new(&2, E.X)),
       store(List.drop(&2, List<&2, U32>, ws, 1n), plans(g, srcs)), max.k(ws, 0)}

def prepared(+g: Map<&2, Lf.Shape>, r: E.X & Coll) -> Prog:
  (entry, c) = r
  match c:
    case Coll{next, srcs, hs}:
      prepared.with(g, entry, List.reverse(&2, Src, srcs))

# Hashes only guidance looks up by: none without it.
def hashes.for(g: Map<&2, Lf.Shape>) -> Maybe<&2, Map<&2, String>>:
  match g:
    case MTip{}:
      None{}
    case _:
      Some{Map.new(&2, String)}

# prepareIC: the sized program applied to the environment, its closures
# compiled into templates, each with its plan from EAL's capture layouts
# (ealCaptureLayouts), keyed by code hash.
def prepare(sized: E.X, +g: Map<&2, Lf.Shape>) -> Prog:
  prepared(g, collect(E.app(sized, E.XEnv{}))(Coll{3, selectors(), hashes.for(g)}))

# A closed term on its own, as icEvalDetailed runs one: prepared like a
# program, unguided, then run on an input it never looks at.
def prepare.closed(t: E.X) -> Prog:
  prepared(Map.new(&2, Lf.Shape), collect(t)(Coll{3, selectors(), None{}}))

# A net ready for runs: room for agents, the template store filled in.
def fill(ws: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match ws:
    case Nil{}:
      a
    case Con{w, rest}:
      fill(rest, (i + 1 : U32), a[i] <- w)

def net.new(p: Prog) -> Net:
  match p:
    case Prog{entry, bodies, +words, +maxk}:
      Net{Array.new(U32, 21n, 0),
          fill(words, 0, Array.new(U32, depth.of((U32.from_nat(List.length(&2, U32, words)) + maxk + 2 : U32)), 0)),
          Ctl{[], [], 0, 1, 0, 0, 0, 0, 0, "", 262144}}

# Running
# -------

def attach(same: Bool, +env: U32, +res: U32, +root: U32, +v: U32) -> M(Unit):
  match same:
    case True{}:
      m.connect((root * 4 : U32), v)
    case False{}:
      do M<Unit>:
        u : Unit <- m.connect(env, v)
        m.connect(res, (root * 4 : U32))

# The entry net around the input, and a root to read the result from
# (initializeIC); the root.
def start(+entry: E.X, input: E.X) -> M(U32):
  do M<U32>:
    +ext : U32 <- body(entry)
    +env : U32 <- m.peer((ext * 4 : U32))
    res : U32 <- m.peer((ext * 4 + 1 : U32))
    +root : U32 <- m.alloc(root(), 0, 0)
    v : U32 <- compile(fuel(), CTerm{input})
    u : Unit <- m.delete(ext)
    u2 : Unit <- attach(U32.is_eq(node.of(env), ext), env, res, root, v)
    return root

# Reading back
# ------------

def body.of(+bodies: Map<&2, E.X>, +tid: U32) -> E.X:
  Pair.snd(Map<&2, E.X>, E.X, Map.get(E.X, E.XZero{}, bodies, U32.show(tid)))

def rb.stuck(net: Net, +a: U32) -> Net & RB:
  match net:
    case Net{mem, tpl, +ctl}:
      (Net{mem, tpl, ctl}, RBErr{"ICStuck " ++ Sh.string(msg.at(c.msgs(ctl), c.nmsg(ctl), a))})

def rb.first(vals: List<&2, E.X>) -> RB:
  match vals:
    case Con{x, rest}:
      RBOk{x}
    case Nil{}:
      RBErr{"ICInternal \"readback: nothing read\""}

# The value at a port, as a CompiledExpr (readback); under Aborted only
# data counts, anything else reads as 0 (readbackData).
def readback(fuel: Nat, +bodies: Map<&2, E.X>, st: RSt) -> Net & RB:
  match fuel:
    case 0n:
      match st:
        case RLoop{net, jobs, vals}:
          (net, RBErr{"ICInternal \"readback: too deep\""})
        case RSeen{data, r, jobs, vals}:
          (net, ni) = r
          (net, RBErr{"ICInternal \"readback: too deep\""})
    case 1n+f:
      match st:
        case RLoop{net, jobs, vals}:
          match jobs:
            case Nil{}:
              (net, rb.first(vals))
            case Con{RVisit{+p, data}, rest}:
              readback(f, bodies, RSeen{data, info(net, node.of(p)), rest, vals})
            case Con{RMkPair{}, rest}:
              match vals:
                case Con{b, Con{a, more}}:
                  readback(f, bodies, RLoop{net, rest, E.XPair{a, b} <> more})
                case _:
                  (net, RBErr{"ICInternal \"readback: pair\""})
            case Con{RMkAborted{}, rest}:
              match vals:
                case Con{m, more}:
                  readback(f, bodies, RLoop{net, rest, E.XAborted{m} <> more})
                case _:
                  (net, RBErr{"ICInternal \"readback: aborted\""})
        case RSeen{data, r, jobs, vals}:
          match data:
            case True{}:
              (net, ni) = r
              match ni:
                case NI{8, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, RVisit{p1, True{}} <> RVisit{p2, True{}} <> RMkPair{} <> jobs, vals})
                case NI{4, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, jobs, E.XZero{} <> vals})
                case _:
                  readback(f, bodies, RLoop{net, jobs, E.XZero{} <> vals})
            case False{}:
              (net, ni) = r
              match ni:
                case NI{4, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, jobs, E.XZero{} <> vals})
                case NI{8, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, RVisit{p1, False{}} <> RVisit{p2, False{}} <> RMkPair{} <> jobs, vals})
                case NI{7, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, jobs, E.XDefer{b, body.of(bodies, a)} <> vals})
                case NI{5, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, jobs, E.XGate{} <> vals})
                case NI{6, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, jobs, E.XAbort{} <> vals})
                case NI{9, a, b, p1, p2}:
                  readback(f, bodies, RLoop{net, RVisit{p1, True{}} <> RMkAborted{} <> jobs, vals})
                case NI{18, a, b, p1, p2}:
                  rb.stuck(net, a)
                case NI{k, +a, +b, p1, p2}:
                  (net, RBErr{"ICStuck " ++ Sh.string("result contains a non-value: " ++ show.kind(k, a, b))})

def c.stop(c: Ctl) -> U32:
  match c:
    case Ctl{stk, msgs, nmsg, bump, free, label, fuel, spent, err, emsg, cap}:
      err

def finish.read(+spent: U32, r: Net & RB) -> Run:
  (net, out) = r
  Run{net, out, spent}

def finish.err(+err: U32, +bodies: Map<&2, E.X>, +root: U32, +c: Ctl, net: Net) -> Run:
  match err:
    case 0:
      finish.read(c.spent(c), readback(U32.to_nat(4294967295), bodies,
        RLoop{net, [RVisit{(root * 4 : U32), False{}}], []}))
    case 1:
      Run{net, RBErr{"ICFuelExhausted " ++ U32.show(c.spent(c))}, c.spent(c)}
    case _:
      Run{net, RBErr{"ICInternal " ++ Sh.string(c.emsg(c))}, c.spent(c)}

def finish.ctl(+bodies: Map<&2, E.X>, +p: U32, r: Net & Ctl) -> Run:
  (net, +c) = r
  finish.err(c.stop(c), bodies, node.of(p), c, net)

def finish.root(+bodies: Map<&2, E.X>, +root: U32, r: Net & U32) -> Run:
  (net, p) = r
  finish.ctl(bodies, p, ctl.of(net))

def finish(+bodies: Map<&2, E.X>, r: CS & U32) -> Run:
  (cs, +root) = r
  finish.root(bodies, root, peer(reduce(U32.to_nat(4294967295), pop(cs.net(cs))), (root * 4 : U32)))

# runICProgram: one iteration on input, at the given fuel.
def run(p: Prog, net: Net, input: E.X, +fuel: U32) -> Run:
  match p:
    case Prog{entry, +bodies, words, maxk}:
      finish(bodies, start(entry, input)(CS{reset(net, fuel), Map.new(&2, List<&2, U32>)}))

# defaultFuel: interactions per iteration.
def default.fuel() -> U32:
  10000000
