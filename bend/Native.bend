import Base
import ./Core.bend as Co
import ./IC.bend as IC
import ./Main.bend as M

# The telomare command with the IC's loop in C: Main.bend's command, its
# runs made by `run` below instead of IC.run. bend/effs/ic.c fires the
# pairs it can, on IC.bend's net, by IC.bend's rules, and hands back the
# first pair it leaves to Bend (a rule that makes a stuck value, an
# unbounded recursion's step under --fast, a pair no rule fires), which
# IC.bend's `fire` fires; then the C goes on. So a run here is IC.run's,
# word for word, only faster.
#
# A def with a foreign body is a promise to the proof gate, so nothing that
# Everything.bend imports imports this file: Main.bend's own main runs
# IC.run, and stays checked.

# IC.bend's reduce in C, on the net's words (Net and Ctl, less Ctl's cold
# part), and why it stopped if a rule failed (1, 2: the messages below).
def nt.reduce(
  mem: Array<U32>, tpl: Array<U32>, sp: U32, bump: U32, free: U32, label: U32, fuel: U32, err: U32,
  cap: U32
) -> IO(Array<U32> & Array<U32> & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32):
  import "./effs/ic.c"
  import "./effs/ic.js"

def why(+w: U32) -> String:
  Bool.pick(String, U32.is_eq(w, 1), "dupRegion: nothing to pair", "dup-closure: no copies")

def failed.if(ok: Bool, net: IC.Net, +w: U32) -> IC.Net:
  match ok:
    case True{}:
      net
    case False{}:
      IC.fail(net, why(w))

def failed(+w: U32, net: IC.Net) -> IC.Net:
  failed.if(U32.is_zero(w), net, w)

def back(cold: List<&2, IC.Cold>, r: Array<U32> & Array<U32> & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32) -> IC.Net:
  (mem, r1) = r
  (tpl, r2) = r1
  (sp, r3) = r2
  (bump, r4) = r3
  (free, r5) = r4
  (label, r6) = r5
  (fuel, r7) = r6
  (err, r8) = r7
  (cap, w) = r8
  failed(w, IC.Net{mem, tpl, IC.Ctl{sp, cold, bump, free, label, fuel, err, cap}})

# Where the loop is: every pair fired, or more to fire.
type Step is Type:
  Fired{net: IC.Net}
  Firing{net: IC.Net}

# What C left: no pair (done), or Bend's pair, which IC.bend fires.
def step(p: IC.Popped) -> Step:
  match p:
    case IC.PEmpty{net}:
      Fired{net}
    case IC.PStale{net}:
      Firing{net}
    case IC.PPair{net, a, b}:
      Firing{IC.fire(net, a, b)}

def net.of(s: Step) -> IC.Net:
  match s:
    case Fired{net}:
      net
    case Firing{net}:
      net

def loop(n: Nat, s: Step) -> IO(IC.Net):
  match n:
    case 0n:
      IO.pure(IC.Net, net.of(s))
    case 1n+f:
      match s:
        case Fired{net}:
          IO.pure(IC.Net, net)
        case Firing{net}:
          match net:
            case IC.Net{mem, tpl, ctl}:
              match ctl:
                case IC.Ctl{sp, cold, bump, free, label, left, err, cap}:
                  do IO<IC.Net>:
                    r : Array<U32> & Array<U32> & U32 & U32 & U32 & U32 & U32 & U32 & U32 & U32 <- nt.reduce(mem, tpl, sp, bump, free, label, left, err, cap)
                    loop(f, step(IC.pop(back(cold, r))))

def finish(+bodies: IC.Read, r: IC.CS & U32) -> IO(IC.Run):
  (cs, +root) = r
  do IO<IC.Run>:
    net : IC.Net <- loop(U32.to_nat(4294967295), Firing{IC.cs.net(cs)})
    return IC.finish.root(bodies, root, IC.peer(net, (root * 4 : U32)))

# IC.run, with the loop in C.
def run(p: IC.Prog, net: IC.Net, input: Co.D, fuel: U32) -> IO(IC.Run):
  match p:
    case IC.Prog{entry, +bodies, words, maxk, +os}:
      finish(IC.Read{bodies, os}, IC.start(entry, input)(IC.CS{IC.reset(net, fuel), Map.new(&2, List<&2, U32>)}))

def main() -> IO(Unit):
  M.app(~run)
