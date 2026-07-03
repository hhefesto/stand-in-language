# telomare-bend resolver: PTerm modules -> named Term1 (TT) -> de Bruijn
# Term2 -> Expr (Term3-equivalent IR with UnsizedStub/RefinementWrapper).
#
# Ports the `process` path of src/Telomare/Resolver.hs:
#   resolveMain    -> resolve_program (Prelude binds + module binds + builtins,
#                     everything INLINED like validateVariables)
#   addBuiltins + optimizeBuiltinFunctions
#                  -> builtin env entries + the syntactic App(left,x)->Lft x
#                     rewrite (applied during resolution)
#   validateVariables -> resolve (inline defs; {x,y,z} t r b becomes
#                     App (Recur t' r' b') Repeater; Int/String/List sugar)
#   debruijinize   -> debru (names to indices, innermost = 0; the process
#                     path leaves every lambda Open, so all lambdas -> lam_s)
#   splitExpr      -> split (state-threaded (next_fid, next_urt); appS
#                     allocates a fresh twiddle defer per application site;
#                     ChurchF n -> i2CB; RecursionF -> unsizedRecursionWrapper;
#                     TUnsizedRepeaterF -> fresh token + repeaterAndAbort;
#                     CheckF -> RefinementWrapper)
#
# Allocation-order fidelity: fid/token counters are threaded in exactly the
# order of Haskell's monadic sequencing (pairS a b runs a then b; appS c i
# runs twiddle, then i, then c; lamS/clamS run the body before the defer).
# This keeps UnsizedRecursionToken numbering identical to the oracle.
#
# Haskell FunctionIndex starts at 0; we start at fid_user_base (16) to keep
# 1..9 for the eval/sizing-generated defers (ir.bend).
#
# Skipped Haskell features (not exercised by Prelude.tel + tictactoe.tel):
# case/patterns (removeCaseUPs), UDT list assignments, HashF, qualified
# imports, letsToApps/debruijinizeApp (wLet path), topological reordering of
# forward references (both files bind before use; missing names error).

from ./util import *
from ./parser import *
from ./ir import *

# ---------------------------------------------------------------------------
# TT: Term1/Term2 union (VarN = named, VarI = de Bruijn index)
# ---------------------------------------------------------------------------

type TT:
  TZero
  TPair { fst: TT, snd: TT }
  VarN { name: String }
  VarI { idx: u24 }
  TApp { fn: TT, arg: TT }
  TLam { pname: String, body: TT }
  TLamC { pname: String, body: TT }
  TLamLet { count: u24, pname: String, body: TT }
  TIte { cond: TT, thn: TT, els: TT }
  TLeft { inner: TT }
  TRight { inner: TT }
  TChurch { num: u24 }
  TRecur { tst: TT, rec: TT, bas: TT }
  TRepeater
  TCheck { tc: TT, val: TT }
  TErr { msg: String }

# i2t: Int -> nested-pair nat ; s2t: String -> list of char nats
def i2t(n: u24) -> TT:
  switch n:
    case 0:
      return TT/TZero
    case _:
      return TT/TPair(i2t(n - 1), TT/TZero)

def s2t(s: String) -> TT:
  match s:
    case String/Nil:
      return TT/TZero
    case String/Cons:
      return TT/TPair(i2t(s.head), s2t(s.tail))

# ---------------------------------------------------------------------------
# Environment: assoc list, most recent first (shadowing).
# ---------------------------------------------------------------------------

type REnv:
  RNil
  RCons { name: String, val: TT, rest: REnv }

def env_lookup(env: REnv, name: String) -> TT:
  match env:
    case REnv/RNil:
      return TT/TErr(str_cat("undefined identifier ", name))
    case REnv/RCons:
      if str_eq(env.name, name):
        return env.val
      else:
        return env_lookup(env.rest, name)

# addBuiltins: outermost bindings (user defs shadow them).
# HTraceF is identity in splitExpr, so trace = \x -> x.
def builtins_env() -> REnv:
  lft = TT/TLam("x", TT/TLeft(TT/VarN("x")))
  rgt = TT/TLam("x", TT/TRight(TT/VarN("x")))
  trc = TT/TLam("x", TT/VarN("x"))
  return REnv/RCons("left", lft, REnv/RCons("right", rgt, REnv/RCons("trace", trc, REnv/RCons("zero", TT/TZero, REnv/RNil))))

# ---------------------------------------------------------------------------
# resolve: PTerm -> TT with full inlining (validateVariables)
# ---------------------------------------------------------------------------

def resolve(p: PTerm, env: REnv) -> TT:
  match p:
    case PTerm/Var:
      return env_lookup(env, p.name)
    case PTerm/App:
      # optimizeBuiltinFunctions: App(left,x) -> Lft x etc. (syntactic)
      match p.fn:
        case PTerm/Var:
          if str_eq(p.fn.name, "left"):
            return TT/TLeft(resolve(p.arg, env))
          else:
            if str_eq(p.fn.name, "right"):
              return TT/TRight(resolve(p.arg, env))
            else:
              if str_eq(p.fn.name, "trace"):
                return resolve(p.arg, env)
              else:
                return TT/TApp(env_lookup(env, p.fn.name), resolve(p.arg, env))
        case _:
          return TT/TApp(resolve(p.fn, env), resolve(p.arg, env))
    case PTerm/Lam:
      body = resolve(p.body, REnv/RCons(p.param, TT/VarN(p.param), env))
      return TT/TLam(p.param, body)
    case PTerm/TNum:
      return i2t(p.num)
    case PTerm/TStr:
      return s2t(p.text)
    case PTerm/PairT:
      return TT/TPair(resolve(p.fst, env), resolve(p.snd, env))
    case PTerm/ListT:
      return resolve_list(p.items, env)
    case PTerm/Let:
      return resolve_let(p.binds, p.body, env)
    case PTerm/Ite:
      return TT/TIte(resolve(p.cond, env), resolve(p.thn, env), resolve(p.els, env))
    case PTerm/Church:
      return TT/TChurch(p.num)
    case PTerm/Recur:
      rt = resolve(p.tst, env)
      rr = resolve(p.rec, env)
      rb = resolve(p.bas, env)
      return TT/TApp(TT/TRecur(rt, rr, rb), TT/TRepeater)
    case PTerm/Check:
      return TT/TCheck(resolve(p.chk, env), resolve(p.val, env))

def resolve_list(items: List(PTerm), env: REnv) -> TT:
  match items:
    case List/Nil:
      return TT/TZero
    case List/Cons:
      return TT/TPair(resolve(items.head, env), resolve_list(items.tail, env))

def resolve_let(binds: List(PBind), body: PTerm, env: REnv) -> TT:
  match binds:
    case List/Nil:
      return resolve(body, env)
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          v = resolve(binds.head.val, env)
          return resolve_let(binds.tail, body, REnv/RCons(binds.head.name, v, env))

# resolve a module's top-level binds sequentially into the env
def resolve_binds(binds: List(PBind), env: REnv) -> REnv:
  match binds:
    case List/Nil:
      return env
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          v = resolve(binds.head.val, env)
          return resolve_binds(binds.tail, REnv/RCons(binds.head.name, v, env))

# ---------------------------------------------------------------------------
# pruneBindings (Resolver.hs resolveMain): keep only definitions transitively
# reachable from `main`. Without this, eagerly inlining all of Prelude OOMs
# HVM (Haskell shares thunks; HVM's strict dup-copies materialize the full
# inlined tree of EVERY def). Name collection over-approximates (ignores
# shadowing) — that only keeps extra defs, never drops needed ones.
# ---------------------------------------------------------------------------

def pt_names(p: PTerm, acc: List(String)) -> List(String):
  match p:
    case PTerm/Var:
      return List/Cons(p.name, acc)
    case PTerm/App:
      return pt_names(p.fn, pt_names(p.arg, acc))
    case PTerm/Lam:
      return pt_names(p.body, acc)
    case PTerm/TNum:
      return acc
    case PTerm/TStr:
      return acc
    case PTerm/PairT:
      return pt_names(p.fst, pt_names(p.snd, acc))
    case PTerm/ListT:
      return pt_names_list(p.items, acc)
    case PTerm/Let:
      return pt_names_binds(p.binds, pt_names(p.body, acc))
    case PTerm/Ite:
      return pt_names(p.cond, pt_names(p.thn, pt_names(p.els, acc)))
    case PTerm/Church:
      return acc
    case PTerm/Recur:
      return pt_names(p.tst, pt_names(p.rec, pt_names(p.bas, acc)))
    case PTerm/Check:
      return pt_names(p.chk, pt_names(p.val, acc))

def pt_names_list(l: List(PTerm), acc: List(String)) -> List(String):
  match l:
    case List/Nil:
      return acc
    case List/Cons:
      return pt_names(l.head, pt_names_list(l.tail, acc))

def pt_names_binds(l: List(PBind), acc: List(String)) -> List(String):
  match l:
    case List/Nil:
      return acc
    case List/Cons:
      match l.head:
        case PBind/Bind:
          return pt_names(l.head.val, pt_names_binds(l.tail, acc))

def str_member(l: List(String), s: String) -> u24:
  match l:
    case List/Nil:
      return 0
    case List/Cons:
      if str_eq(l.head, s):
        return 1
      else:
        return str_member(l.tail, s)

def lookup_bind(binds: List(PBind), name: String) -> (u24, PTerm):
  match binds:
    case List/Nil:
      return (0, PTerm/TNum(0))
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          if str_eq(binds.head.name, name):
            return (1, binds.head.val)
          else:
            return lookup_bind(binds.tail, name)

# BFS closure: worklist of names still to expand, visited accumulator.
def needed_names(binds: List(PBind), work: List(String), visited: List(String)) -> List(String):
  match work:
    case List/Nil:
      return visited
    case List/Cons:
      if str_member(visited, work.head):
        return needed_names(binds, work.tail, visited)
      else:
        (found, def_val) = lookup_bind(binds, work.head)
        if found:
          new_work = pt_names(def_val, work.tail)
          return needed_names(binds, new_work, List/Cons(work.head, visited))
        else:
          return needed_names(binds, work.tail, visited)

def filter_binds(binds: List(PBind), keep: List(String)) -> List(PBind):
  match binds:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          if str_member(keep, binds.head.name):
            return List/Cons(PBind/Bind(binds.head.name, binds.head.val), filter_binds(binds.tail, keep))
          else:
            return filter_binds(binds.tail, keep)

# resolveMain: prelude binds ++ module binds, pruned to main's transitive
# deps, resolved in order; result = resolved `main`.
def resolve_program(prelude_binds: List(PBind), module_binds: List(PBind)) -> TT:
  all_binds = append_binds(prelude_binds, module_binds)
  keep = needed_names(all_binds, ["main"], List/Nil)
  pruned = filter_binds(all_binds, keep)
  env = resolve_binds(pruned, builtins_env())
  return env_lookup(env, "main")

def append_binds(a: List(PBind), b: List(PBind)) -> List(PBind):
  match a:
    case List/Nil:
      return b
    case List/Cons:
      return List/Cons(a.head, append_binds(a.tail, b))

# ---------------------------------------------------------------------------
# debruijinize: VarN -> VarI (innermost lambda = 0)
# ---------------------------------------------------------------------------

def debru(t: TT, stack: List(String)) -> TT:
  match t:
    case TT/TZero:
      return TT/TZero
    case TT/TPair:
      return TT/TPair(debru(t.fst, stack), debru(t.snd, stack))
    case TT/VarN:
      return debru_var(t.name, stack, 0)
    case TT/VarI:
      return TT/VarI(t.idx)
    case TT/TApp:
      return TT/TApp(debru(t.fn, stack), debru(t.arg, stack))
    case TT/TLam:
      return TT/TLam("", debru(t.body, List/Cons(t.pname, stack)))
    case TT/TLamC:
      return TT/TLamC("", debru(t.body, List/Cons(t.pname, stack)))
    case TT/TLamLet:
      return TT/TLam("", debru(t.body, List/Cons(t.pname, stack)))
    case TT/TIte:
      return TT/TIte(debru(t.cond, stack), debru(t.thn, stack), debru(t.els, stack))
    case TT/TLeft:
      return TT/TLeft(debru(t.inner, stack))
    case TT/TRight:
      return TT/TRight(debru(t.inner, stack))
    case TT/TChurch:
      return TT/TChurch(t.num)
    case TT/TRecur:
      return TT/TRecur(debru(t.tst, stack), debru(t.rec, stack), debru(t.bas, stack))
    case TT/TRepeater:
      return TT/TRepeater
    case TT/TCheck:
      return TT/TCheck(debru(t.tc, stack), debru(t.val, stack))
    case TT/TErr:
      return TT/TErr(t.msg)

def debru_var(name: String, stack: List(String), depth: u24) -> TT:
  match stack:
    case List/Nil:
      return TT/TErr(str_cat("undefined identifier ", name))
    case List/Cons:
      if str_eq(stack.head, name):
        return TT/VarI(depth)
      else:
        return debru_var(name, stack.tail, depth + 1)

# scan for TErr; "" = no error
def tt_first_err(t: TT) -> String:
  match t:
    case TT/TErr:
      return t.msg
    case TT/TPair:
      return first_nonempty(tt_first_err(t.fst), tt_first_err(t.snd))
    case TT/TApp:
      return first_nonempty(tt_first_err(t.fn), tt_first_err(t.arg))
    case TT/TLam:
      return tt_first_err(t.body)
    case TT/TLamC:
      return tt_first_err(t.body)
    case TT/TLamLet:
      return tt_first_err(t.body)
    case TT/TIte:
      return first_nonempty(tt_first_err(t.cond), first_nonempty(tt_first_err(t.thn), tt_first_err(t.els)))
    case TT/TLeft:
      return tt_first_err(t.inner)
    case TT/TRight:
      return tt_first_err(t.inner)
    case TT/TRecur:
      return first_nonempty(tt_first_err(t.tst), first_nonempty(tt_first_err(t.rec), tt_first_err(t.bas)))
    case TT/TCheck:
      return first_nonempty(tt_first_err(t.tc), tt_first_err(t.val))
    case _:
      return ""

def first_nonempty(a: String, b: String) -> String:
  match a:
    case String/Nil:
      return b
    case String/Cons:
      return String/Cons(a.head, a.tail)

# ---------------------------------------------------------------------------
# splitExpr: TT (de Bruijn) -> Expr, threading (next_fid, next_urt)
# ---------------------------------------------------------------------------

# twiddle body (twiddleS): (left (right env), (left env, right (right env)))
def twiddle_body() -> Expr:
  return Expr/Pair(Expr/PLeft(Expr/PRight(Expr/Env)),
                   Expr/Pair(Expr/PLeft(Expr/Env),
                             Expr/PRight(Expr/PRight(Expr/Env))))

# appS c i = SetEnv (SetEnv (Pair (Defer tw twiddle) (Pair i c)))
def mk_app(tw: u24, i_expr: Expr, c_expr: Expr) -> Expr:
  return Expr/SetEnv(Expr/SetEnv(Expr/Pair(Expr/Defer(tw, twiddle_body()), Expr/Pair(i_expr, c_expr))))

# iteB_ i t e = SetEnv (Pair (Gate e t) i)
def mk_ite(i_expr: Expr, t_expr: Expr, e_expr: Expr) -> Expr:
  return Expr/SetEnv(Expr/Pair(Expr/Gate(e_expr, t_expr), i_expr))

def setenvs(n: u24, x: Expr) -> Expr:
  switch n:
    case 0:
      return x
    case _:
      return Expr/SetEnv(setenvs(n - 1, x))

# repeatFunctionS (Telomare.hs:758). Allocation order: rf1, rf2, body defer,
# inner lamS defer, outer lamS defer, clamS defer.
# rf body: (left env, (left env, (left (right env), (SetEnv (right env), right (right (right env))))))
def rf_body() -> Expr:
  apply_f = Expr/SetEnv(Expr/PRight(Expr/Env))
  env3 = Expr/PRight(Expr/PRight(Expr/PRight(Expr/Env)))
  return Expr/Pair(Expr/PLeft(Expr/Env),
                   Expr/Pair(Expr/PLeft(Expr/Env),
                             Expr/Pair(Expr/PLeft(Expr/PRight(Expr/Env)),
                                       Expr/Pair(apply_f, env3))))

# returns (expr, next_fid)
def repeat_function(fid: u24) -> (Expr, u24):
  rf1 = Expr/Defer(fid, rf_body())
  rf2 = Expr/Defer(fid + 1, rf_body())
  r = Expr/PLeft(Expr/PLeft(Expr/PRight(Expr/PRight(Expr/Env))))
  x = Expr/PLeft(Expr/Env)
  fp = Expr/PLeft(Expr/PLeft(Expr/PRight(Expr/Env)))
  fenv = Expr/PRight(Expr/PLeft(Expr/PRight(Expr/Env)))
  frame_setup = Expr/Pair(rf1, Expr/Pair(rf2, Expr/Pair(fp, Expr/Pair(x, fenv))))
  body = Expr/SetEnv(Expr/Pair(r, frame_setup))
  inner_lam = Expr/Pair(Expr/Defer(fid + 2, body), Expr/Env)
  outer_lam = Expr/Pair(Expr/Defer(fid + 3, inner_lam), Expr/Env)
  clam = Expr/Pair(Expr/Defer(fid + 4, outer_lam), Expr/Zero)
  return (clam, fid + 5)

# i2CB: appS (repeatFunctionS) (clamS (left (right^3 (SetEnv^n Env)))).
# Order: twiddle, clam defer, repeatFunction's 5.
def split_church(n: u24, fid: u24) -> (Expr, u24):
  tw = fid
  core = Expr/PLeft(Expr/PRight(Expr/PRight(Expr/PRight(setenvs(n, Expr/Env)))))
  clam = Expr/Pair(Expr/Defer(fid + 1, core), Expr/Zero)
  (rep, fid2) = repeat_function(fid + 2)
  return (mk_app(tw, clam, rep), fid2)

# repeaterAndAbort (Telomare.hs:778). Order: unsizedRepeater's clam defer,
# then abrt: appS twiddle, abrt defer.
def split_repeater(tok: u24, fid: u24) -> (Expr, u24):
  stub_core = Expr/PLeft(Expr/PRight(Expr/PRight(Expr/PRight(Expr/UnsizedStub(tok, Expr/Env)))))
  unsized_rep = Expr/Pair(Expr/Defer(fid, stub_core), Expr/Zero)
  app_e = mk_app(fid + 1, var_b(0), var_b(1))
  abort_token = Expr/Pair(Expr/Zero, i2b(tok))
  abrt_body = Expr/SetEnv(Expr/Pair(Expr/SetEnv(Expr/Pair(Expr/Abort, abort_token)), app_e))
  abrt = Expr/Defer(fid + 2, abrt_body)
  return (Expr/Pair(unsized_rep, abrt), fid + 3)

# rWrap: nsLamS (lamS (iteB_ A B C)) where
#   A = appS (varB 4) (varB 0)              -> twA
#   B = appS (appS (varB 3) (varB 1)) (varB 0) -> twB_out (outer), twB_in
#   C = appS (varB 2) (varB 0)              -> twC
# then lamS defer, then nsLamS defer (paired with (right env)).
def mk_rwrap(fid: u24) -> (Expr, u24):
  a_e = mk_app(fid, var_b(0), var_b(4))
  b_inner = mk_app(fid + 2, var_b(1), var_b(3))
  b_e = mk_app(fid + 1, var_b(0), b_inner)
  c_e = mk_app(fid + 3, var_b(0), var_b(2))
  ite_e = mk_ite(a_e, b_e, c_e)
  lam1 = Expr/Pair(Expr/Defer(fid + 4, ite_e), Expr/Env)
  nslam = Expr/Pair(Expr/Defer(fid + 5, lam1), Expr/PRight(Expr/Env))
  return (nslam, fid + 6)

# ---------------------------------------------------------------------------
# split: the main state-threaded conversion. Returns (expr, fid, urt).
# ---------------------------------------------------------------------------

def split(t: TT, fid: u24, urt: u24) -> (Expr, u24, u24):
  match t:
    case TT/TZero:
      return (Expr/Zero, fid, urt)
    case TT/TPair:
      (a_e, fid1, urt1) = split(t.fst, fid, urt)
      (b_e, fid2, urt2) = split(t.snd, fid1, urt1)
      return (Expr/Pair(a_e, b_e), fid2, urt2)
    case TT/VarI:
      return (var_b(t.idx), fid, urt)
    case TT/VarN:
      return (Expr/EvalError(err_unhandled()), fid, urt)
    case TT/TApp:
      tw = fid
      (i_e, fid1, urt1) = split(t.arg, fid + 1, urt)
      (c_e, fid2, urt2) = split(t.fn, fid1, urt1)
      return (mk_app(tw, i_e, c_e), fid2, urt2)
    case TT/TLam:
      (b_e, fid1, urt1) = split(t.body, fid, urt)
      return (Expr/Pair(Expr/Defer(fid1, b_e), Expr/Env), fid1 + 1, urt1)
    case TT/TLamC:
      # clamS: closed lambda pairs its defer with Zero
      (b_e, fid1, urt1) = split(t.body, fid, urt)
      return (Expr/Pair(Expr/Defer(fid1, b_e), Expr/Zero), fid1 + 1, urt1)
    case TT/TLamLet:
      # eliminated by debru2 (becomes TLam); direct split treats as open
      (b_e, fid1, urt1) = split(t.body, fid, urt)
      return (Expr/Pair(Expr/Defer(fid1, b_e), Expr/Env), fid1 + 1, urt1)
    case TT/TIte:
      (i_e, fid1, urt1) = split(t.cond, fid, urt)
      (t_e, fid2, urt2) = split(t.thn, fid1, urt1)
      (e_e, fid3, urt3) = split(t.els, fid2, urt2)
      return (mk_ite(i_e, t_e, e_e), fid3, urt3)
    case TT/TLeft:
      (x_e, fid1, urt1) = split(t.inner, fid, urt)
      return (Expr/PLeft(x_e), fid1, urt1)
    case TT/TRight:
      (x_e, fid1, urt1) = split(t.inner, fid, urt)
      return (Expr/PRight(x_e), fid1, urt1)
    case TT/TChurch:
      (e, fid1) = split_church(t.num, fid)
      return (e, fid1, urt)
    case TT/TRepeater:
      tok = urt
      (e, fid1) = split_repeater(tok, fid)
      return (e, fid1, urt + 1)
    case TT/TRecur:
      # unsizedRecursionWrapper. bigApp allocations first:
      # tw3 (outer app), [i3 = abrt: pure], then c3 = appS(appS(repeatFn,
      # repeater), rWrap): tw2, i2 = rWrap allocs, c2: tw1, [i1 pure],
      # c1 = repeatFn's 5. Then bigApp defer. Then trb: b, r, tWrap.
      tw3 = fid
      tw2 = fid + 1
      (rwrap_e, fid1) = mk_rwrap(fid + 2)
      tw1 = fid1
      (repfn_e, fid2) = repeat_function(fid1 + 1)
      repeater = Expr/PLeft(Expr/PLeft(Expr/Env))
      abrt = Expr/Pair(Expr/PRight(Expr/PLeft(Expr/Env)), Expr/Env)
      c1_app = mk_app(tw1, repeater, repfn_e)
      c2_app = mk_app(tw2, rwrap_e, c1_app)
      big_app = mk_app(tw3, abrt, c2_app)
      big_defer = Expr/Defer(fid2, big_app)
      # trb = pairS b (pairS r (pairS tWrap (pure Zero)))
      # pairS order: b allocs, then r, then tWrap (tw, defer, then t).
      (b_e, fid3, urt1) = split(t.bas, fid2 + 1, urt)
      (r_e, fid4, urt2) = split(t.rec, fid3, urt1)
      tw_t = fid4
      tdef_body = mk_app(fid4, var_b(0), var_b(1))
      tdef = Expr/Defer(fid4 + 1, tdef_body)
      (t_e, fid5, urt3) = split(t.tst, fid4 + 2, urt2)
      twrap = Expr/Pair(tdef, Expr/Pair(t_e, Expr/Zero))
      trb = Expr/Pair(b_e, Expr/Pair(r_e, Expr/Pair(twrap, Expr/Zero)))
      return (Expr/Pair(big_defer, trb), fid5, urt3)
    case TT/TCheck:
      (tc_e, fid1, urt1) = split(t.tc, fid, urt)
      (c_e, fid2, urt2) = split(t.val, fid1, urt1)
      return (Expr/RefinementWrapper(0, tc_e, c_e), fid2, urt2)
    case TT/TErr:
      return (Expr/EvalError(err_unhandled()), fid, urt)

# ---------------------------------------------------------------------------
# full pipeline for one program: prelude binds + module binds -> Expr
# Result: (expr, err_msg, n_tokens); err_msg "" when OK.
# ---------------------------------------------------------------------------

def compile_to_ir(prelude_binds: List(PBind), module_binds: List(PBind)) -> (Expr, String, u24):
  t1 = resolve_program(prelude_binds, module_binds)
  t2 = debru(t1, List/Nil)
  err = tt_first_err(t2)
  match err:
    case String/Cons:
      return (Expr/Zero, String/Cons(err.head, err.tail), 0)
    case String/Nil:
      (e, fid, urt) = split(t2, fid_user_base(), 0)
      return (e, "", urt)

# ===========================================================================
# SHARED path — the pipeline compileMain ACTUALLY uses (main2Term3let):
#   annotateUnsizedCount + letsToApps + debruijinizeApp (LetBinding vars
#   apply k repeater tokens at each use) + closeLams + splitExpr.
# Definitions stay shared as `App (Lam name inner) def` brackets instead of
# being inlined — this is also what keeps the term small enough for HVM.
# The inline path above (compile_to_ir) matches main2Term3, which Haskell
# only uses for type checking; it is kept for the small-case tests.
# ===========================================================================

def refs_delete(refs: List(String), name: String) -> List(String):
  match refs:
    case List/Nil:
      return List/Nil
    case List/Cons:
      if str_eq(refs.head, name):
        return refs_delete(refs.tail, name)
      else:
        return List/Cons(refs.head, refs_delete(refs.tail, name))

def refs_union(a: List(String), b: List(String)) -> List(String):
  match a:
    case List/Nil:
      return b
    case List/Cons:
      if str_member(b, a.head):
        return refs_union(a.tail, b)
      else:
        return List/Cons(a.head, refs_union(a.tail, b))

# colon-var name for annotation sites
def colon_name(m: u24) -> String:
  return String/Cons(58, u24_show(m))

# l2a: PTerm -> (TT, free refs, site counter). Ports buildRefs +
# annotateUnsizedCount in one pass. Lambdas with no free refs -> TLamC
# (buildRefs Closed rule; cap lambdas added by l2a_bind stay open).
def l2a(p: PTerm, ctr: u24) -> (TT, List(String), u24):
  match p:
    case PTerm/Var:
      return (TT/VarN(p.name), [p.name], ctr)
    case PTerm/App:
      # optimizeBuiltinFunctions syntactic rewrites
      match p.fn:
        case PTerm/Var:
          if str_eq(p.fn.name, "left"):
            (x, r, c1) = l2a(p.arg, ctr)
            return (TT/TLeft(x), r, c1)
          else:
            if str_eq(p.fn.name, "right"):
              (x, r, c1) = l2a(p.arg, ctr)
              return (TT/TRight(x), r, c1)
            else:
              if str_eq(p.fn.name, "trace"):
                (x, r, c1) = l2a(p.arg, ctr)
                return (x, r, c1)
              else:
                (x, r, c1) = l2a(p.arg, ctr)
                return (TT/TApp(TT/VarN(p.fn.name), x), refs_union([p.fn.name], r), c1)
        case _:
          (f, r1, c1) = l2a(p.fn, ctr)
          (x, r2, c2) = l2a(p.arg, c1)
          return (TT/TApp(f, x), refs_union(r1, r2), c2)
    case PTerm/Lam:
      (b, r, c1) = l2a(p.body, ctr)
      nr = refs_delete(r, p.param)
      match nr:
        case List/Nil:
          return (TT/TLamC(p.param, b), List/Nil, c1)
        case List/Cons:
          return (TT/TLam(p.param, b), List/Cons(nr.head, nr.tail), c1)
    case PTerm/TNum:
      return (i2t(p.num), List/Nil, ctr)
    case PTerm/TStr:
      return (s2t(p.text), List/Nil, ctr)
    case PTerm/PairT:
      (a, r1, c1) = l2a(p.fst, ctr)
      (b, r2, c2) = l2a(p.snd, c1)
      return (TT/TPair(a, b), refs_union(r1, r2), c2)
    case PTerm/ListT:
      return l2a_list(p.items, ctr)
    case PTerm/Let:
      return l2a_let(p.binds, p.body, ctr)
    case PTerm/Ite:
      (i, r1, c1) = l2a(p.cond, ctr)
      (t, r2, c2) = l2a(p.thn, c1)
      (e, r3, c3) = l2a(p.els, c2)
      return (TT/TIte(i, t, e), refs_union(r1, refs_union(r2, r3)), c3)
    case PTerm/Church:
      return (TT/TChurch(p.num), List/Nil, ctr)
    case PTerm/Recur:
      # children annotated first, THEN this site gets the next index
      (t, r1, c1) = l2a(p.tst, ctr)
      (r, r2, c2) = l2a(p.rec, c1)
      (b, r3, c3) = l2a(p.bas, c2)
      site = colon_name(c3)
      wrapped = TT/TApp(TT/TRecur(t, r, b), TT/VarN(site))
      return (wrapped, refs_union(r1, refs_union(r2, refs_union(r3, [site]))), c3 + 1)
    case PTerm/Check:
      (tc, r1, c1) = l2a(p.chk, ctr)
      (v, r2, c2) = l2a(p.val, c1)
      return (TT/TCheck(tc, v), refs_union(r1, r2), c2)

def l2a_list(items: List(PTerm), ctr: u24) -> (TT, List(String), u24):
  match items:
    case List/Nil:
      return (TT/TZero, List/Nil, ctr)
    case List/Cons:
      (h, r1, c1) = l2a(items.head, ctr)
      (t, r2, c2) = l2a_list(items.tail, c1)
      return (TT/TPair(h, t), refs_union(r1, r2), c2)

# an annotated binding: (name, capped def, external refs, cap count)
type ABind:
  Mk { name: String, def_tt: TT, refs: List(String), count: u24 }

# annotate one binding: own counter from 0; wrap count cap lambdas
# (":0" outermost, per Haskell's foldr over ascending vs).
def l2a_bind(name: String, def_pt: PTerm) -> ABind:
  (d, refs, k) = l2a(def_pt, 0)
  capped = wrap_caps(0, k, d)
  return ABind/Mk(name, capped, strip_colon_refs(refs), k)

def wrap_caps(i: u24, k: u24, body: TT) -> TT:
  if i < k:
    return TT/TLam(colon_name(i), wrap_caps(i + 1, k, body))
  else:
    return body

def strip_colon_refs(refs: List(String)) -> List(String):
  match refs:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match refs.head:
        case String/Cons:
          if refs.head.head == 58:
            return strip_colon_refs(refs.tail)
          else:
            return List/Cons(String/Cons(refs.head.head, refs.head.tail), strip_colon_refs(refs.tail))
        case String/Nil:
          return strip_colon_refs(refs.tail)

def l2a_binds(binds: List(PBind)) -> List(ABind):
  match binds:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          return List/Cons(l2a_bind(binds.head.name, binds.head.val), l2a_binds(binds.tail))

# transitive-closure pruning over ABind refs, preserving original order
def abind_lookup(abs: List(ABind), name: String) -> (u24, List(String)):
  match abs:
    case List/Nil:
      return (0, List/Nil)
    case List/Cons:
      match abs.head:
        case ABind/Mk:
          if str_eq(abs.head.name, name):
            return (1, abs.head.refs)
          else:
            return abind_lookup(abs.tail, name)

def abind_closure(abs: List(ABind), work: List(String), visited: List(String)) -> List(String):
  match work:
    case List/Nil:
      return visited
    case List/Cons:
      if str_member(visited, work.head):
        return abind_closure(abs, work.tail, visited)
      else:
        (found, refs) = abind_lookup(abs, work.head)
        if found:
          return abind_closure(abs, refs_union(refs, work.tail), List/Cons(work.head, visited))
        else:
          return abind_closure(abs, work.tail, visited)

def abind_filter(abs: List(ABind), keep: List(String)) -> List(ABind):
  match abs:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match abs.head:
        case ABind/Mk:
          if str_member(keep, abs.head.name):
            return List/Cons(ABind/Mk(abs.head.name, abs.head.def_tt, abs.head.refs, abs.head.count), abind_filter(abs.tail, keep))
          else:
            return abind_filter(abs.tail, keep)

# letsToApps chain: bindings in dependency order b1..bn nest as
# App(Lam(b1, App(Lam(b2, ... inner), d2)), d1)
def lets_chain(abs: List(ABind), inner: TT) -> TT:
  match abs:
    case List/Nil:
      return inner
    case List/Cons:
      match abs.head:
        case ABind/Mk:
          return TT/TApp(TT/TLamLet(abs.head.count, abs.head.name, lets_chain(abs.tail, inner)), abs.head.def_tt)

# inner-let version of the above (used from l2a_let)
def l2a_let(binds: List(PBind), body: PTerm, ctr: u24) -> (TT, List(String), u24):
  abinds = l2a_binds(binds)
  (inner, irefs, c1) = l2a(body, ctr)
  keep = abind_closure(abinds, strip_colon_refs(irefs), List/Nil)
  kept = abind_filter(abinds, keep)
  chained = lets_chain(kept, inner)
  out_refs = refs_delete_names(refs_union(all_abind_refs(kept), irefs), kept)
  return (chained, out_refs, c1)

def all_abind_refs(abs: List(ABind)) -> List(String):
  match abs:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match abs.head:
        case ABind/Mk:
          return refs_union(abs.head.refs, all_abind_refs(abs.tail))

def refs_delete_names(refs: List(String), abs: List(ABind)) -> List(String):
  match abs:
    case List/Nil:
      return refs
    case List/Cons:
      match abs.head:
        case ABind/Mk:
          return refs_delete_names(refs_delete(refs, abs.head.name), abs.tail)

# capTop: wrap the whole chained term for the main body's own {x,y,z}
# sites: App(Lam(":0", App(Lam(":1", ...term), Repeater)), Repeater) with
# ":0" outermost (ascending site order — token order matches the counter).
def cap_top(i: u24, k: u24, t: TT) -> TT:
  if i < k:
    return TT/TApp(TT/TLam(colon_name(i), cap_top(i + 1, k, t)), TT/TRepeater)
  else:
    return t

# builtin bindings (addBuiltins); the App(left,x) forms rewrite away, so
# these bodies survive only for bare uses.
def builtin_pbinds() -> List(PBind):
  lft = PBind/Bind("left", PTerm/Lam("x", PTerm/App(PTerm/Var("left"), PTerm/Var("x"))))
  rgt = PBind/Bind("right", PTerm/Lam("x", PTerm/App(PTerm/Var("right"), PTerm/Var("x"))))
  trc = PBind/Bind("trace", PTerm/Lam("x", PTerm/Var("x")))
  zro = PBind/Bind("zero", PTerm/TNum(0))
  return [lft, rgt, trc, zro]

# debru2: de Bruijn with LetBinding repeater application. Stack entries are
# (name, count); a Var hit on count>0 applies the variable to count
# repeaters (debruijinizeApp findElem).
def debru2(t: TT, stack: List((String, u24))) -> TT:
  match t:
    case TT/TZero:
      return TT/TZero
    case TT/TPair:
      return TT/TPair(debru2(t.fst, stack), debru2(t.snd, stack))
    case TT/VarN:
      return debru2_var(t.name, stack, 0)
    case TT/VarI:
      return TT/VarI(t.idx)
    case TT/TApp:
      return TT/TApp(debru2(t.fn, stack), debru2(t.arg, stack))
    case TT/TLam:
      return TT/TLam("", debru2(t.body, List/Cons((t.pname, 0), stack)))
    case TT/TLamC:
      return TT/TLamC("", debru2(t.body, List/Cons((t.pname, 0), stack)))
    case TT/TLamLet:
      return TT/TLam("", debru2(t.body, List/Cons((t.pname, t.count), stack)))
    case TT/TIte:
      return TT/TIte(debru2(t.cond, stack), debru2(t.thn, stack), debru2(t.els, stack))
    case TT/TLeft:
      return TT/TLeft(debru2(t.inner, stack))
    case TT/TRight:
      return TT/TRight(debru2(t.inner, stack))
    case TT/TChurch:
      return TT/TChurch(t.num)
    case TT/TRecur:
      return TT/TRecur(debru2(t.tst, stack), debru2(t.rec, stack), debru2(t.bas, stack))
    case TT/TRepeater:
      return TT/TRepeater
    case TT/TCheck:
      return TT/TCheck(debru2(t.tc, stack), debru2(t.val, stack))
    case TT/TErr:
      return TT/TErr(t.msg)

def debru2_var(name: String, stack: List((String, u24)), depth: u24) -> TT:
  match stack:
    case List/Nil:
      return TT/TErr(str_cat("undefined identifier ", name))
    case List/Cons:
      (nm, count) = stack.head
      if str_eq(nm, name):
        return apply_repeaters(TT/VarI(depth), count)
      else:
        return debru2_var(name, stack.tail, depth + 1)

def apply_repeaters(v: TT, count: u24) -> TT:
  switch count:
    case 0:
      return v
    case _:
      return TT/TApp(apply_repeaters(v, count - 1), TT/TRepeater)

# closeLams: mark naked open lambdas Closed. naked stays true through
# non-lambda nodes; a lambda consumes it (body not naked).
def close_lams(t: TT, naked: u24) -> TT:
  match t:
    case TT/TLam:
      if naked:
        return TT/TLamC("", close_lams(t.body, 0))
      else:
        return TT/TLam("", close_lams(t.body, 0))
    case TT/TLamC:
      return TT/TLamC("", close_lams(t.body, 0))
    case TT/TZero:
      return TT/TZero
    case TT/TPair:
      return TT/TPair(close_lams(t.fst, naked), close_lams(t.snd, naked))
    case TT/VarI:
      return TT/VarI(t.idx)
    case TT/TApp:
      return TT/TApp(close_lams(t.fn, naked), close_lams(t.arg, naked))
    case TT/TIte:
      return TT/TIte(close_lams(t.cond, naked), close_lams(t.thn, naked), close_lams(t.els, naked))
    case TT/TLeft:
      return TT/TLeft(close_lams(t.inner, naked))
    case TT/TRight:
      return TT/TRight(close_lams(t.inner, naked))
    case TT/TChurch:
      return TT/TChurch(t.num)
    case TT/TRecur:
      return TT/TRecur(close_lams(t.tst, naked), close_lams(t.rec, naked), close_lams(t.bas, naked))
    case TT/TRepeater:
      return TT/TRepeater
    case TT/TCheck:
      return TT/TCheck(close_lams(t.tc, naked), close_lams(t.val, naked))
    case TT/TErr:
      return TT/TErr(t.msg)
    case _:
      return t

# find main's PTerm def among module binds
def find_main(binds: List(PBind)) -> (u24, PTerm):
  match binds:
    case List/Nil:
      return (0, PTerm/TNum(0))
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          if str_eq(binds.head.name, "main"):
            return (1, binds.head.val)
          else:
            return find_main(binds.tail)

def drop_main(binds: List(PBind)) -> List(PBind):
  match binds:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          if str_eq(binds.head.name, "main"):
            return drop_main(binds.tail)
          else:
            return List/Cons(PBind/Bind(binds.head.name, binds.head.val), drop_main(binds.tail))

# compile_shared: the full main2Term3let-equivalent pipeline.
# Returns (expr, err_msg, n_tokens).
def compile_shared(prelude_binds: List(PBind), module_binds: List(PBind)) -> (Expr, String, u24):
  (found, main_pt) = find_main(module_binds)
  if found:
    all_pb = append_binds(builtin_pbinds(), append_binds(prelude_binds, drop_main(module_binds)))
    abinds = l2a_binds(all_pb)
    (inner, irefs, k) = l2a(main_pt, 0)
    keep = abind_closure(abinds, strip_colon_refs(irefs), List/Nil)
    kept = abind_filter(abinds, keep)
    chained = cap_top(0, k, lets_chain(kept, inner))
    t2 = close_lams(debru2(chained, List/Nil), 1)
    err = tt_first_err(t2)
    match err:
      case String/Cons:
        return (Expr/Zero, String/Cons(err.head, err.tail), 0)
      case String/Nil:
        (e, fid, urt) = split(t2, fid_user_base(), 0)
        return (e, "", urt)
  else:
    return (Expr/Zero, "no main function", 0)
