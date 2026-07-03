# telomare-bend emitter: CompiledExpr -> generated Bend source.
#
# The runtime backend that replaces the tree-walking interpreter for
# executing compiled programs: the sized expression is emitted as a
# standalone .bend program and HVM2 executes it natively. Match arms are
# lazily selected by the runtime, which supplies exactly the demand-driven
# gate behavior GHC gives the Haskell evaluator (see PORT.md).
#
# Value encoding in generated programs:
#   type TV: Z | P{f,s} | F{fn: TV -> TV} | A{p}
# Z/P mirror the IR's Zero/Pair; F wraps a defer body compiled to a named
# function `d<fid>`; A is the abort poison (Aborted payload), propagated by
# every eliminator per abortStep's rules.
#
# Structure of an emitted program:
#   <static prelude: TV type + tvL/tvR/tvApp/tvCall/tvAbort helpers>
#   def d<fid>(env: TV) -> TV: ...        # one per unique Defer fid
#   def g<n>(env: TV) -> TV: ...          # one per lifted GateSwitch
#   def tel_main() -> TV: ...             # the compiled top-level expr
#   def inputs() -> List(TV): ...         # embedded input lines as TV data
#   def main() -> IO(u24): ...            # evalLoop transcript driver
#
# Text is built in DIFFERENCE-LIST style: every emitter conses its
# fragments onto an `after` continuation (O(1) per fragment) and the whole
# program is joined exactly once — a naive append-per-node version was
# quadratic and hung on real programs.

from ./util import *
from ./ir import *

# ---------------------------------------------------------------------------
# fragment helpers
# ---------------------------------------------------------------------------

def frags_join(l: List(String)) -> String:
  match l:
    case List/Nil:
      return ""
    case List/Cons:
      return str_cat(l.head, frags_join(l.tail))

def frags_append(a: List(String), b: List(String)) -> List(String):
  match a:
    case List/Nil:
      return b
    case List/Cons:
      return List/Cons(a.head, frags_append(a.tail, b))

# ---------------------------------------------------------------------------
# collect unique defer fids (bodies are identical per fid by construction)
# ---------------------------------------------------------------------------

def fid_member(l: List(u24), n: u24) -> u24:
  match l:
    case List/Nil:
      return 0
    case List/Cons:
      if l.head == n:
        return 1
      else:
        return fid_member(l.tail, n)

# slot of a fid in the collected list (dense index for tvDispatch)
def fid_slot(fids: List(u24), fid: u24) -> u24:
  match fids:
    case List/Nil:
      return 16777215
    case List/Cons:
      if fids.head == fid:
        return 0
      else:
        return 1 + fid_slot(fids.tail, fid)

# returns (fids, bodies) as parallel lists, first occurrence wins
def collect_defers(e: Expr, fids: List(u24), bodies: List(Expr)) -> (List(u24), List(Expr)):
  match e:
    case Expr/Defer:
      if fid_member(fids, e.fid):
        return (fids, bodies)
      else:
        return collect_defers(e.body, List/Cons(e.fid, fids), List/Cons(e.body, bodies))
    case Expr/Pair:
      (f1, b1) = collect_defers(e.fst, fids, bodies)
      return collect_defers(e.snd, f1, b1)
    case Expr/SetEnv:
      return collect_defers(e.inner, fids, bodies)
    case Expr/Gate:
      (f1, b1) = collect_defers(e.lft, fids, bodies)
      return collect_defers(e.rgt, f1, b1)
    case Expr/PLeft:
      return collect_defers(e.inner, fids, bodies)
    case Expr/PRight:
      return collect_defers(e.inner, fids, bodies)
    case _:
      return (fids, bodies)

# ---------------------------------------------------------------------------
# emit-time validation: the sized expr may contain only
# Zero/Pair/Env/SetEnv/Defer/Gate/PLeft/PRight/Abort/Aborted.
# ---------------------------------------------------------------------------

def emit_valid(e: Expr) -> u24:
  match e:
    case Expr/Zero:
      return 1
    case Expr/Env:
      return 1
    case Expr/Pair:
      return emit_valid(e.fst) & emit_valid(e.snd)
    case Expr/SetEnv:
      return emit_valid(e.inner)
    case Expr/Defer:
      return emit_valid(e.body)
    case Expr/Gate:
      return emit_valid(e.lft) & emit_valid(e.rgt)
    case Expr/PLeft:
      return emit_valid(e.inner)
    case Expr/PRight:
      return emit_valid(e.inner)
    case Expr/Abort:
      return 1
    case Expr/Aborted:
      return 1
    case _:
      return 0

# ---------------------------------------------------------------------------
# expression compilation
#
# ce(e, after, gdefs, gidx) -> (frags, gdefs', gidx')
#   `env` names the enclosing function's parameter.
# Special shapes:
#   SetEnv(Pair(Gate(l,r), s)) — GateSwitch: lifted to a generated function
#     g<idx>(env) whose body is a native `match` (HVM evaluates only the
#     selected arm — the demand-driven laziness this backend exists for).
#   SetEnv(Pair(Defer fid, e)) -> direct call d<fid>(<e>)
#   SetEnv(Pair(Abort, e))     -> tvAbort(<e>)
#   generic SetEnv(x)          -> tvApp(<x>)
# ---------------------------------------------------------------------------

def u24_name(prefix: String, n: u24) -> String:
  return str_cat(prefix, u24_show(n))

def ce(e: Expr, after: List(String), gdefs: List(String), gidx: u24, fids: List(u24)) -> (List(String), List(String), u24):
  match e:
    case Expr/Zero:
      return (List/Cons("TV/Z", after), gdefs, gidx)
    case Expr/Env:
      return (List/Cons("env", after), gdefs, gidx)
    case Expr/Pair:
      (fb, g1, i1) = ce(e.snd, List/Cons(")", after), gdefs, gidx, fids)
      (fa, g2, i2) = ce(e.fst, List/Cons(", ", fb), g1, i1, fids)
      return (List/Cons("TV/P(", fa), g2, i2)
    case Expr/PLeft:
      (fi, g1, i1) = ce(e.inner, List/Cons(")", after), gdefs, gidx, fids)
      return (List/Cons("tvL(", fi), g1, i1)
    case Expr/PRight:
      (fi, g1, i1) = ce(e.inner, List/Cons(")", after), gdefs, gidx, fids)
      return (List/Cons("tvR(", fi), g1, i1)
    case Expr/Defer:
      # DEFUNCTIONALIZED: HVM2 cannot soundly duplicate non-affine
      # functions flowing through data (lambda clones silently corrupt;
      # ref clones are refused or re-expanded). Closures therefore carry a
      # plain slot NUMBER and the generated tvDispatch maps it back to the
      # function — numbers duplicate freely. See PORT.md.
      return (List/Cons(str_cat3("TV/F(", u24_show(fid_slot(fids, e.fid)), ")"), after), gdefs, gidx)
    case Expr/Abort:
      # bare Abort only occurs under SetEnv(Pair(Abort, _)), special-cased
      return (List/Cons("TV/A(TV/Z)", after), gdefs, gidx)
    case Expr/Aborted:
      inner = ce_basic(e.val, List/Cons(")", after))
      return (List/Cons("TV/A(", inner), gdefs, gidx)
    case Expr/Gate:
      # a gate outside a SetEnv switch is not produced by the compiler
      return (List/Cons("TV/A(TV/Z)", after), gdefs, gidx)
    case Expr/SetEnv:
      match e.inner:
        case Expr/Pair:
          f = e.inner.fst
          en = e.inner.snd
          match f:
            case Expr/Gate:
              # lift the switch to g<idx>(env) with a lazy match
              (fr, g1, i1) = ce(f.rgt, ["\n    case TV/A:\n      return sv0\n    case TV/F:\n      return TV/A(TV/Z)\n\n"], gdefs, gidx, fids)
              (fl, g2, i2) = ce(f.lft, List/Cons("\n    case TV/P:\n      return ", fr), g1, i1, fids)
              (fs, g3, i3) = ce(en, List/Cons(":\n    case TV/Z:\n      return ", fl), g2, i2, fids)
              gname = u24_name("g", i3)
              header = str_cat3("def ", gname, "(env: TV) -> TV:\n  match sv0 = ")
              new_gdefs = frags_append(List/Cons(header, fs), g3)
              return (List/Cons(str_cat(gname, "(env)"), after), new_gdefs, i3 + 1)
            case Expr/Defer:
              (fe, g1, i1) = ce(en, List/Cons(")", after), gdefs, gidx, fids)
              return (List/Cons(str_cat(u24_name("d", f.fid), "("), fe), g1, i1)
            case Expr/Abort:
              (fe, g1, i1) = ce(en, List/Cons(")", after), gdefs, gidx, fids)
              return (List/Cons("tvAbort(", fe), g1, i1)
            case _:
              (fp, g1, i1) = ce(Expr/Pair(f, en), List/Cons(")", after), gdefs, gidx, fids)
              return (List/Cons("tvApp(", fp), g1, i1)
        case _:
          (fi, g1, i1) = ce(e.inner, List/Cons(")", after), gdefs, gidx, fids)
          return (List/Cons("tvApp(", fi), g1, i1)
    case _:
      return (List/Cons("TV/A(TV/Z)", after), gdefs, gidx)

# basic-only tree (abort payloads, embedded input data)
def ce_basic(e: Expr, after: List(String)) -> List(String):
  match e:
    case Expr/Zero:
      return List/Cons("TV/Z", after)
    case Expr/Pair:
      inner = ce_basic(e.fst, List/Cons(", ", ce_basic(e.snd, List/Cons(")", after))))
      return List/Cons("TV/P(", inner)
    case _:
      return List/Cons("TV/Z", after)

# ---------------------------------------------------------------------------
# defer-function emission (fragment lists, same style)
# ---------------------------------------------------------------------------

def emit_defer_defs2(fids: List(u24), bodies: List(Expr), gdefs: List(String), gidx: u24, all_fids: List(u24)) -> (List(String), List(String), u24):
  match fids:
    case List/Nil:
      return (List/Nil, gdefs, gidx)
    case List/Cons:
      match bodies:
        case List/Nil:
          return (List/Nil, gdefs, gidx)
        case List/Cons:
          (rest, g1, i1) = emit_defer_defs2(fids.tail, bodies.tail, gdefs, gidx, all_fids)
          (bf, g2, i2) = ce(bodies.head, List/Cons("\n\n", rest), g1, i1, all_fids)
          header = str_cat3("def ", u24_name("d", fids.head), "(env: TV) -> TV:\n  return ")
          return (List/Cons(header, bf), g2, i2)

# ---------------------------------------------------------------------------
# static prelude of every generated program
# ---------------------------------------------------------------------------

def emitted_prelude_0() -> String:
  return "# generated by telomare-bend (bend/emitter.bend) -- do not edit\n\ntype TV:\n  Z\n  P { f: TV, s: TV }\n  F { fid: u24 }\n  A { p: TV }\n\ndef tvL(v: TV) -> TV:\n  match v:\n    case TV/Z:\n      return TV/Z\n    case TV/P:\n      return v.f\n    case TV/A:\n      return TV/A(v.p)\n    case TV/F:\n      return TV/A(TV/Z)\n\ndef tvR(v: TV) -> TV:\n  match v:\n    case TV/Z:\n    "

def emitted_prelude_1() -> String:
  return "  return TV/Z\n    case TV/P:\n      return v.s\n    case TV/A:\n      return TV/A(v.p)\n    case TV/F:\n      return TV/A(TV/Z)\n\ndef tvId(v: TV) -> TV:\n  return v\n\n# truncate to the Zero/Pair skeleton (abortStep payload rule)\ndef tvTrunc(v: TV) -> TV:\n  match v:\n    case TV/Z:\n      return TV/Z\n    case TV/P:\n      return TV/P(tvTrunc(v.f), tvTrunc(v.s))\n    case T"

def emitted_prelude_2() -> String:
  return "V/A:\n      return TV/Z\n    case TV/F:\n      return TV/Z\n\n# FillFunction Abort x; slot 16777215 is out of dispatch range -> tvId\ndef tvAbort(v: TV) -> TV:\n  match v:\n    case TV/Z:\n      return TV/F(16777215)\n    case TV/P:\n      return TV/A(tvTrunc(TV/P(v.f, v.s)))\n    case TV/A:\n      return TV/A(v.p)\n    case TV/F:\n      return TV/A(TV/Z)\n\n# generic applicati"

def emitted_prelude_3() -> String:
  return "on: SetEnv on an evaluated pair (defunctionalized)\ndef tvApp(v: TV) -> TV:\n  match v:\n    case TV/P:\n      f = v.f\n      match f:\n        case TV/F:\n          return tvDispatch(f.fid, v.s)\n        case TV/A:\n          return TV/A(f.p)\n        case TV/Z:\n          return TV/A(TV/Z)\n        case TV/P:\n          return TV/A(TV/Z)\n    case TV/A:\n      return TV/A(v.p"

def emitted_prelude_4() -> String:
  return ")\n    case TV/Z:\n      return TV/A(TV/Z)\n    case TV/F:\n      return TV/A(TV/Z)\n\n# closure call with telomare's appB convention: the callee is a closure\n# Pair(code, captured); the body runs with env = (arg, captured).\ndef tvCall(c: TV, i: TV) -> TV:\n  match c:\n    case TV/P:\n      code = c.f\n      match code:\n        case TV/F:\n          return tvDispatch(code.fi"

def emitted_prelude_5() -> String:
  return "d, TV/P(i, c.s))\n        case TV/A:\n          return TV/A(code.p)\n        case TV/Z:\n          return TV/A(TV/Z)\n        case TV/P:\n          return TV/A(TV/Z)\n    case TV/A:\n      return TV/A(c.p)\n    case TV/Z:\n      return TV/A(TV/Z)\n    case TV/F:\n      return TV/A(TV/Z)\n\n"

def emitted_prelude() -> String:
  return frags_join(List/Cons(emitted_prelude_0(), List/Cons(emitted_prelude_1(), List/Cons(emitted_prelude_2(), List/Cons(emitted_prelude_3(), List/Cons(emitted_prelude_4(), List/Cons(emitted_prelude_5(), List/Nil)))))))

def emitted_driver_0() -> String:
  return "# ---- driver ----\n\ndef tv_b2i(v: TV, acc: u24) -> (u24, u24):\n  match v:\n    case TV/Z:\n      return (1, acc)\n    case TV/P:\n      match sv0 = v.s:\n        case TV/Z:\n          return tv_b2i(v.f, acc + 1)\n        case TV/P:\n          return (0, 0)\n        case TV/A:\n          return (0, 0)\n        case TV/F:\n          return (0, 0)\n    case TV/A:\n      return (0, 0)\n    case TV/"

def emitted_driver_1() -> String:
  return "F:\n      return (0, 0)\n\ndef tv_b2s(v: TV) -> String:\n  match v:\n    case TV/Z:\n      return \"\"\n    case TV/P:\n      (ok, c) = tv_b2i(v.f, 0)\n      if ok:\n        return String/Cons(c, tv_b2s(v.s))\n      else:\n        return \"\"\n    case TV/A:\n      return \"\"\n    case TV/F:\n      return \"\"\n\ndef sc(a: String, b: String) -> String:\n  match a:\n    case String/Nil:\n      ret"

def emitted_driver_2() -> String:
  return "urn b\n    case String/Cons:\n      return String/Cons(a.head, sc(a.tail, b))\n\ndef one_iter(inp: TV) -> (String, TV, u24):\n  r = tvCall(tel_main(), inp)\n  match r:\n    case TV/P:\n      disp = tv_b2s(r.f)\n      match nsv0 = r.s:\n        case TV/Z:\n          return (disp, TV/Z, 2)\n        case TV/P:\n          return (disp, TV/P(nsv0.f, nsv0.s), 1)\n        case TV/A:\n          return (di"

def emitted_driver_3() -> String:
  return "sp, TV/Z, 0)\n        case TV/F:\n          return (disp, TV/F(nsv0.fid), 1)\n    case TV/A:\n      return (\"aborted\", TV/Z, 0)\n    case TV/Z:\n      return (\"aborted\", TV/Z, 0)\n    case TV/F:\n      return (\"runtime error\", TV/Z, 0)\n\ndef loop_go(state: TV, first: u24, ins: List(TV), acc: String) -> String:\n  if first:\n    (disp, ns, ok) = one_iter(TV/Z)\n    return loop_cont(disp, ns, "

def emitted_driver_4() -> String:
  return "ok, ins, acc)\n  else:\n    match ins:\n      case List/Nil:\n        return acc\n      case List/Cons:\n        (disp, ns, ok) = one_iter(TV/P(ins.head, state))\n        return loop_cont(disp, ns, ok, ins.tail, acc)\n\ndef loop_cont(disp: String, ns: TV, ok: u24, rest: List(TV), acc: String) -> String:\n  new_acc = sc(acc, sc(disp, \"\\n\"))\n  switch ok:\n    case 0:\n      return new_acc\n    c"

def emitted_driver_5() -> String:
  return "ase 1:\n      return loop_go(ns, 0, rest, new_acc)\n    case _:\n      return new_acc\n\ndef main() -> String:\n  return sc(loop_go(TV/Z, 1, inputs(), \"\"), \"\")\n"

def emitted_driver() -> String:
  return frags_join(List/Cons(emitted_driver_0(), List/Cons(emitted_driver_1(), List/Cons(emitted_driver_2(), List/Cons(emitted_driver_3(), List/Cons(emitted_driver_4(), List/Cons(emitted_driver_5(), List/Nil)))))))

# embedded input lines: each line as s2b-style TV data
def emit_inputs(lines: List(String)) -> String:
  return str_cat3("def inputs() -> List(TV):\n  return [", frags_join(emit_input_items(lines)), "]\n\n")

def emit_input_items(lines: List(String)) -> List(String):
  match lines:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match lines.tail:
        case List/Nil:
          return ce_basic(s2b_static(lines.head), List/Nil)
        case List/Cons:
          rest = emit_input_items(List/Cons(lines.tail.head, lines.tail.tail))
          return ce_basic(s2b_static(lines.head), List/Cons(", ", rest))

def s2b_static(s: String) -> Expr:
  match s:
    case String/Nil:
      return Expr/Zero
    case String/Cons:
      return Expr/Pair(i2b(s.head), s2b_static(s.tail))

# ---------------------------------------------------------------------------
# top level: sized expr + input lines -> full program text (or "" on
# validation failure)
# ---------------------------------------------------------------------------

# the generated dispatcher: slot number -> function call. Slot k = the
# k-th collected fid; out-of-range slots resolve to tvId (used by tvAbort).
def emit_dispatch(fids: List(u24), slot: u24) -> List(String):
  match fids:
    case List/Nil:
      return ["    case _:\n      return tvId(env)\n\n"]
    case List/Cons:
      rest = emit_dispatch(fids.tail, slot + 1)
      arm = str_cat3(str_cat3("    case ", u24_show(slot), ":\n      return "), u24_name("d", fids.head), "(env)\n")
      switch slot:
        case 0:
          return List/Cons("def tvDispatch(slot: u24, env: TV) -> TV:\n  switch slot:\n", List/Cons(arm, rest))
        case _:
          return List/Cons(arm, rest)

def emit_program(sized: Expr, unused_inputs: List(String)) -> String:
  if emit_valid(sized):
    (fids, bodies) = collect_defers(sized, List/Nil, List/Nil)
    (main_frags, gdefs1, gi1) = ce(sized, ["\n\n"], List/Nil, 0, fids)
    (defer_frags, gdefs2, gi2) = emit_defer_defs2(fids, bodies, gdefs1, gi1, fids)
    # env binding: gate functions lifted from top-level positions take an
    # env argument; outside any defer body the environment is Zero.
    dispatch_frags = emit_dispatch(fids, 0)
    all_frags = frags_append(defer_frags,
                frags_append(gdefs2,
                frags_append(dispatch_frags,
                List/Cons("def tel_main() -> TV:\n  env = TV/Z\n  return ", main_frags))))
    body = frags_join(all_frags)
    # NOTE: `def inputs()` is NOT embedded — the compiled program is
    # input-independent, so the driver appends the inputs def per run and
    # caches this text (compile once, replay cheaply).
    # trailing str_cat with "" forces the whole chain: run-rs's lazy
    # readback leaves nullary global refs (e.g. emitted_driver) unexpanded
    # in tail position otherwise
    full = str_cat(emitted_prelude(), str_cat(body, emitted_driver()))
    return str_cat(full, "")
  else:
    return ""
