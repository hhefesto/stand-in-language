# telomare-bend sizer: faithful port of the Possible.hs abstract
# interpreter that infers {x,y,z} recursion bounds (sizeTermM and its whole
# support cast). See bend/PORT.md for the map to the Haskell source.
#
# Monad translation: StrictAccum SizedRecursion becomes explicit pair
# threading — every stepping function returns (Expr, SR) and parents merge.
# SizedRecursion = assoc list (token, bound) merged with max (the Haskell
# Map.unionWith (liftM2 max) — all values in the M path are Just n).
# Sets of input indices = ascending-unordered List(u24) with member/filter
# helpers. Maybe-tags on EitherP: 0 = Nothing, n+1 = Just n (ir.bend).
#
# Haskell `error` cases become Expr/EvalError (checked by callers/tests).

from ./util import *
from ./ir import *

# ---------------------------------------------------------------------------
# SizedRecursion
# ---------------------------------------------------------------------------

type SR:
  SNil
  SCons { tok: u24, bound: u24, rest: SR }

def sr_merge(a: SR, b: SR) -> SR:
  match a:
    case SR/SNil:
      return b
    case SR/SCons:
      return sr_insert(sr_merge(a.rest, b), a.tok, a.bound)

def sr_insert(s: SR, tok: u24, bound: u24) -> SR:
  match s:
    case SR/SNil:
      return SR/SCons(tok, bound, SR/SNil)
    case SR/SCons:
      if s.tok == tok:
        if s.bound < bound:
          return SR/SCons(tok, bound, s.rest)
        else:
          return SR/SCons(s.tok, s.bound, s.rest)
      else:
        return SR/SCons(s.tok, s.bound, sr_insert(s.rest, tok, bound))

def sr_one(tok: u24, bound: u24) -> SR:
  return SR/SCons(tok, bound, SR/SNil)

def sr_lookup(s: SR, tok: u24) -> (u24, u24):
  match s:
    case SR/SNil:
      return (0, 0)
    case SR/SCons:
      if s.tok == tok:
        return (1, s.bound)
      else:
        return sr_lookup(s.rest, tok)

def sr_show(s: SR) -> String:
  match s:
    case SR/SNil:
      return ""
    case SR/SCons:
      entry = str_cat3(u24_show(s.tok), ":", u24_show(s.bound))
      match s.rest:
        case SR/SNil:
          return entry
        case SR/SCons:
          return str_cat3(entry, ",", sr_show(SR/SCons(s.rest.tok, s.rest.bound, s.rest.rest)))

# ---------------------------------------------------------------------------
# Input-tree positions as BIT PATHS (0 = left, 1 = right) instead of
# Haskell's Integer indices: refinements like `$127 left x` reach depth 127
# (index ~2^128), far beyond u24. decendant x d == d `is_prefix` x.
# A "set" is a List of paths.
# ---------------------------------------------------------------------------

def path_eq(a: List(u24), b: List(u24)) -> u24:
  match a:
    case List/Nil:
      match b:
        case List/Nil:
          return 1
        case List/Cons:
          return 0
    case List/Cons:
      match b:
        case List/Nil:
          return 0
        case List/Cons:
          if a.head == b.head:
            return path_eq(a.tail, b.tail)
          else:
            return 0

# is a a prefix of (or equal to) b?
def is_prefix(a: List(u24), b: List(u24)) -> u24:
  match a:
    case List/Nil:
      return 1
    case List/Cons:
      match b:
        case List/Nil:
          return 0
        case List/Cons:
          if a.head == b.head:
            return is_prefix(a.tail, b.tail)
          else:
            return 0

def path_snoc(p: List(u24), bit: u24) -> List(u24):
  match p:
    case List/Nil:
      return [bit]
    case List/Cons:
      return List/Cons(p.head, path_snoc(p.tail, bit))

def set_member(s: List(List(u24)), n: List(u24)) -> u24:
  match s:
    case List/Nil:
      return 0
    case List/Cons:
      if path_eq(s.head, n):
        return 1
      else:
        return set_member(s.tail, n)

def set_insert(s: List(List(u24)), n: List(u24)) -> List(List(u24)):
  if set_member(s, n):
    return s
  else:
    return List/Cons(n, s)

def set_union(a: List(List(u24)), b: List(List(u24))) -> List(List(u24)):
  match a:
    case List/Nil:
      return b
    case List/Cons:
      return set_insert(set_union(a.tail, b), a.head)

# isUnbounded: unbounded iff NO member of s lies at-or-below n
def is_unbounded(s: List(List(u24)), n: List(u24)) -> u24:
  match s:
    case List/Nil:
      return 1
    case List/Cons:
      if is_prefix(n, s.head):
        return 0
      else:
        return is_unbounded(s.tail, n)

# any member of `pairs` at-or-below n
def any_dec_of(pairs: List(List(u24)), n: List(u24)) -> u24:
  match pairs:
    case List/Nil:
      return 0
    case List/Cons:
      if is_prefix(n, pairs.head):
        return 1
      else:
        return any_dec_of(pairs.tail, n)

# One-pass scan: does e contain any EitherP whose tag makes filter_left /
# filter_right non-identity? Returns (has_left_work, has_right_work).
# Haskell can afford to always "apply" the filters because they are lazy
# thunks; strictly materializing two env copies per application level makes
# env size double per unroll level (2^k blowup — see PORT.md). Filtering
# only when the scan says so keeps the common case a shared pass-through.
def super_filter_work(n: List(u24), e: Expr) -> (u24, u24):
  match e:
    case Expr/EitherP:
      (l1, r1) = super_filter_work(n, e.lft)
      (l2, r2) = super_filter_work(n, e.rgt)
      return ((just_dec(e.tag, n) | l1) | l2, (just_dec(n, e.tag) | r1) | r2)
    case Expr/Pair:
      (l1, r1) = super_filter_work(n, e.fst)
      (l2, r2) = super_filter_work(n, e.snd)
      return (l1 | l2, r1 | r2)
    case Expr/SetEnv:
      return super_filter_work(n, e.inner)
    case Expr/Gate:
      (l1, r1) = super_filter_work(n, e.lft)
      (l2, r2) = super_filter_work(n, e.rgt)
      return (l1 | l2, r1 | r2)
    case Expr/PLeft:
      return super_filter_work(n, e.inner)
    case Expr/PRight:
      return super_filter_work(n, e.inner)
    case Expr/Defer:
      return super_filter_work(n, e.body)
    case Expr/RecursionTest:
      return super_filter_work(n, e.inner)
    case Expr/SizeStage:
      return super_filter_work(n, e.inner)
    case Expr/SizeStepStub:
      return super_filter_work(n, e.inner)
    case Expr/UnsizedStub:
      return super_filter_work(n, e.inner)
    case _:
      return (0, 0)

# both args Just-tags (1:path): is a's path a descendant of b's path?
def just_dec(a: List(u24), b: List(u24)) -> u24:
  match a:
    case List/Nil:
      return 0
    case List/Cons:
      match b:
        case List/Nil:
          return 0
        case List/Cons:
          return is_prefix(b.tail, a.tail)

# ---------------------------------------------------------------------------
# Abort payloads (Telomare.hs patterns; payloads are Basic trees)
#   AbortRecursion t = Pair Zero t
#   AbortAny         = Pair (Pair (Pair Zero Zero) Zero) Zero
#   AbortUnsizeable t= Pair (Pair (Pair (Pair Zero Zero) Zero) Zero) t
# ---------------------------------------------------------------------------

def abort_recursion(n: u24) -> Expr:
  return Expr/Aborted(Expr/Pair(Expr/Zero, i2b(n)))

def abort_any() -> Expr:
  return Expr/Aborted(Expr/Pair(Expr/Pair(Expr/Pair(Expr/Zero, Expr/Zero), Expr/Zero), Expr/Zero))

def abort_unsizeable(tok: u24) -> Expr:
  return Expr/Aborted(Expr/Pair(Expr/Pair(Expr/Pair(Expr/Pair(Expr/Zero, Expr/Zero), Expr/Zero), Expr/Zero), i2b(tok)))

# classify an Aborted payload: 0 = other/user, 1 = AbortRecursion(n),
# 2 = AbortAny, 3 = AbortUnsizeable(tok); returns (kind, value)
def classify_abort(v: Expr) -> (u24, u24):
  match v:
    case Expr/Pair:
      match v.fst:
        case Expr/Zero:
          (okn, n) = b2i(v.snd)
          return (1, n)
        case Expr/Pair:
          (kind2, val2) = classify_abort_deep(v.fst, v.snd)
          return (kind2, val2)
        case _:
          return (0, 0)
    case _:
      return (0, 0)

def classify_abort_deep(f: Expr, s: Expr) -> (u24, u24):
  # f = Pair(Pair(Zero,Zero), Zero) with s = Zero        -> AbortAny
  # f = Pair(Pair(Pair(Zero,Zero),Zero), Zero) with s=t  -> AbortUnsizeable t
  match f:
    case Expr/Pair:
      match f.fst:
        case Expr/Pair:
          match f.fst.fst:
            case Expr/Pair:
              (okt, t) = b2i(s)
              return (3, t)
            case Expr/Zero:
              match s:
                case Expr/Zero:
                  return (2, 0)
                case _:
                  return (0, 0)
            case _:
              return (0, 0)
        case _:
          return (0, 0)
    case _:
      return (0, 0)

# ---------------------------------------------------------------------------
# Shallow equality (ShallowEq1) + mergeShallow
# ---------------------------------------------------------------------------

def shallow_eq(a: Expr, b: Expr) -> u24:
  match a:
    case Expr/Zero:
      match b:
        case Expr/Zero:
          return 1
        case _:
          return 0
    case Expr/Defer:
      match b:
        case Expr/Defer:
          return a.fid == b.fid
        case _:
          return 0
    case Expr/Abort:
      match b:
        case Expr/Abort:
          return 1
        case _:
          return 0
    case Expr/Aborted:
      match b:
        case Expr/Aborted:
          return expr_eq(a.val, b.val)
        case _:
          return 0
    case _:
      return 0

def merge_shallow(tag: List(u24), a: Expr, b: Expr) -> Expr:
  if shallow_eq(a, b):
    return a
  else:
    return Expr/EitherP(tag, a, b)

# filterLeft/filterRight (superStepM): full-tree rewrites of the argument.
# tag encoding: 0 = Nothing (no filtering, callers skip), n+1 = Just n.
def filter_left(n: List(u24), e: Expr) -> Expr:
  match e:
    case Expr/EitherP:
      if just_dec(e.tag, n):
        return filter_left(n, e.lft)
      else:
        return Expr/EitherP(e.tag, filter_left(n, e.lft), filter_left(n, e.rgt))
    case Expr/Pair:
      return Expr/Pair(filter_left(n, e.fst), filter_left(n, e.snd))
    case Expr/SetEnv:
      return Expr/SetEnv(filter_left(n, e.inner))
    case Expr/Gate:
      return Expr/Gate(filter_left(n, e.lft), filter_left(n, e.rgt))
    case Expr/PLeft:
      return Expr/PLeft(filter_left(n, e.inner))
    case Expr/PRight:
      return Expr/PRight(filter_left(n, e.inner))
    case Expr/Defer:
      return Expr/Defer(e.fid, filter_left(n, e.body))
    case Expr/RecursionTest:
      return Expr/RecursionTest(e.tok, filter_left(n, e.inner))
    case Expr/SizeStage:
      return Expr/SizeStage(e.tok, e.bound, filter_left(n, e.inner))
    case Expr/SizeStepStub:
      return Expr/SizeStepStub(e.tok, e.num, filter_left(n, e.inner))
    case Expr/UnsizedStub:
      return Expr/UnsizedStub(e.tok, filter_left(n, e.inner))
    case _:
      return e

def filter_right(n: List(u24), e: Expr) -> Expr:
  match e:
    case Expr/EitherP:
      if just_dec(n, e.tag):
        return filter_right(n, e.rgt)
      else:
        return Expr/EitherP(e.tag, filter_right(n, e.lft), filter_right(n, e.rgt))
    case Expr/Pair:
      return Expr/Pair(filter_right(n, e.fst), filter_right(n, e.snd))
    case Expr/SetEnv:
      return Expr/SetEnv(filter_right(n, e.inner))
    case Expr/Gate:
      return Expr/Gate(filter_right(n, e.lft), filter_right(n, e.rgt))
    case Expr/PLeft:
      return Expr/PLeft(filter_right(n, e.inner))
    case Expr/PRight:
      return Expr/PRight(filter_right(n, e.inner))
    case Expr/Defer:
      return Expr/Defer(e.fid, filter_right(n, e.body))
    case Expr/RecursionTest:
      return Expr/RecursionTest(e.tok, filter_right(n, e.inner))
    case Expr/SizeStage:
      return Expr/SizeStage(e.tok, e.bound, filter_right(n, e.inner))
    case Expr/SizeStepStub:
      return Expr/SizeStepStub(e.tok, e.num, filter_right(n, e.inner))
    case Expr/UnsizedStub:
      return Expr/UnsizedStub(e.tok, filter_right(n, e.inner))
    case _:
      return e

# ---------------------------------------------------------------------------
# GateResult
# ---------------------------------------------------------------------------

type GR:
  Mk { lft: u24, rgt: u24, has_o: u24, o: Expr }

# gateBasicResult (gateAbortResult (gateIndexedResult (gateSuperResult ...)))
def gate_result(g: Expr) -> GR:
  match g:
    case Expr/Zero:
      return GR/Mk(1, 0, 0, Expr/Zero)
    case Expr/Pair:
      return GR/Mk(0, 1, 0, Expr/Zero)
    case Expr/Aborted:
      return GR/Mk(0, 0, 1, Expr/Aborted(g.val))
    case Expr/IVar:
      return GR/Mk(1, 1, 0, Expr/Zero)
    case Expr/EitherP:
      ga = gate_result(g.lft)
      gb = gate_result(g.rgt)
      match ga:
        case GR/Mk:
          match gb:
            case GR/Mk:
              if ga.has_o & gb.has_o:
                return GR/Mk(ga.lft | gb.lft, ga.rgt | gb.rgt, 1, Expr/EitherP(g.tag, ga.o, gb.o))
              else:
                if ga.has_o:
                  return GR/Mk(ga.lft | gb.lft, ga.rgt | gb.rgt, 1, ga.o)
                else:
                  return GR/Mk(ga.lft | gb.lft, ga.rgt | gb.rgt, gb.has_o, gb.o)
    case _:
      return GR/Mk(0, 0, 1, Expr/EvalError(err_unhandled()))

def fold_gate_result(tag: List(u24), l: Expr, r: Expr, gr: GR) -> Expr:
  match gr:
    case GR/Mk:
      if gr.lft & gr.rgt:
        if gr.has_o:
          return Expr/EitherP([], gr.o, Expr/EitherP(tag, l, r))
        else:
          return Expr/EitherP(tag, l, r)
      else:
        if gr.lft:
          if gr.has_o:
            return Expr/EitherP([], gr.o, l)
          else:
            return l
        else:
          if gr.rgt:
            if gr.has_o:
              return Expr/EitherP([], gr.o, r)
            else:
              return r
          else:
            if gr.has_o:
              return gr.o
            else:
              return Expr/EvalError(err_unhandled())

# ---------------------------------------------------------------------------
# unsizedTest (sizeTermM variant: indexed + super, fallthrough id)
# ---------------------------------------------------------------------------

def unsized_test(zeros: List(List(u24)), tok: u24, g: Expr) -> Expr:
  match g:
    case Expr/IVar:
      if is_unbounded(zeros, g.path):
        return abort_unsizeable(tok)
      else:
        if set_member(zeros, g.path):
          return Expr/Zero
        else:
          return Expr/IVar(g.path)
    case Expr/EitherP:
      na = unsized_test(zeros, tok, g.lft)
      nb = unsized_test(zeros, tok, g.rgt)
      if is_abort_unsizeable(na):
        return na
      else:
        if is_abort_unsizeable(nb):
          return nb
        else:
          return Expr/EitherP(g.tag, na, nb)
    case _:
      return g

def is_abort_unsizeable(e: Expr) -> u24:
  match e:
    case Expr/Aborted:
      (kind, v) = classify_abort(e.val)
      return kind == 3
    case _:
      return 0

# ---------------------------------------------------------------------------
# sizing-generated IR builders
# ---------------------------------------------------------------------------

def arg_one() -> Expr:
  return Expr/PLeft(Expr/Env)

def arg_two() -> Expr:
  return Expr/PLeft(Expr/PRight(Expr/Env))

def arg_three() -> Expr:
  return Expr/PLeft(Expr/PRight(Expr/PRight(Expr/Env)))

def arg_four() -> Expr:
  return Expr/PLeft(Expr/PRight(Expr/PRight(Expr/PRight(Expr/Env))))

# iteB (LAZY, Possible.hs:483):
#   SetEnv(Pair( SetEnv(Pair(Gate(Defer(E,e), Defer(T,t)), i)) , Env))
def ite_lazy(i: Expr, t: Expr, e: Expr) -> Expr:
  gate = Expr/Gate(Expr/Defer(fid_unsized_e(), e), Expr/Defer(fid_unsized_t(), t))
  return Expr/SetEnv(Expr/Pair(Expr/SetEnv(Expr/Pair(gate, i)), Expr/Env))

def setenv_n(n: u24, x: Expr) -> Expr:
  switch n:
    case 0:
      return x
    case _:
      return Expr/SetEnv(setenv_n(n - 1, x))

# the rfa body generated for SizeStepStub tok (n+1) inner
def size_step_body(tok: u24, next_n: u24, stub_inner: Expr) -> Expr:
  return ite_lazy(app_b(arg_four(), arg_one()),
                  app_b(app_b(arg_three(), Expr/SizeStepStub(tok, next_n, stub_inner)), arg_one()),
                  Expr/SizeStage(tok, next_n, app_b(arg_two(), arg_one())))

# ---------------------------------------------------------------------------
# The sizing evaluator: transformNoDeferM (sizeTermM's evalStep chain).
# sz_eval walks bottom-up (skipping Defer bodies), threading SR.
# sz_body is the defer-application walk (replaceEnv). sz_step is the
# flattened basicStepM (stuckStepM (abortStepM (indexedAbortStepM
# (indexedInputStepM (indexedSuperStepM (superStepM (superAbortStepM
# (unsizedStepM''')))))))) chain, dispatching on evaluated children.
# maxs = maxSizingSize; zeros = input indices known 0.
# ---------------------------------------------------------------------------

def sz_eval(e: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match e:
    case Expr/Defer:
      return (Expr/Defer(e.fid, e.body), SR/SNil)
    case Expr/Zero:
      return (Expr/Zero, SR/SNil)
    case Expr/Env:
      return (Expr/Env, SR/SNil)
    case Expr/Pair:
      (a, s1) = sz_eval(e.fst, maxs, zeros)
      (b, s2) = sz_eval(e.snd, maxs, zeros)
      (r, s3) = sz_step(Expr/Pair(a, b), maxs, zeros)
      return (r, sr_merge(s1, sr_merge(s2, s3)))
    case Expr/SetEnv:
      (i, s1) = sz_eval(e.inner, maxs, zeros)
      (r, s2) = sz_step(Expr/SetEnv(i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/Gate:
      (l, s1) = sz_eval(e.lft, maxs, zeros)
      (r, s2) = sz_eval(e.rgt, maxs, zeros)
      (g, s3) = sz_step(Expr/Gate(l, r), maxs, zeros)
      return (g, sr_merge(s1, sr_merge(s2, s3)))
    case Expr/PLeft:
      (i, s1) = sz_eval(e.inner, maxs, zeros)
      (r, s2) = sz_step(Expr/PLeft(i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/PRight:
      (i, s1) = sz_eval(e.inner, maxs, zeros)
      (r, s2) = sz_step(Expr/PRight(i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/Abort:
      return (Expr/Abort, SR/SNil)
    case Expr/Aborted:
      return (Expr/Aborted(e.val), SR/SNil)
    case Expr/RecursionTest:
      (i, s1) = sz_eval(e.inner, maxs, zeros)
      (r, s2) = sz_step(Expr/RecursionTest(e.tok, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/UnsizedStub:
      (i, s1) = sz_eval(e.inner, maxs, zeros)
      (r, s2) = sz_step(Expr/UnsizedStub(e.tok, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/SizeStepStub:
      (i, s1) = sz_eval(e.inner, maxs, zeros)
      (r, s2) = sz_step(Expr/SizeStepStub(e.tok, e.num, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/SizeStage:
      (i, s1) = sz_eval(e.inner, maxs, zeros)
      (r, s2) = sz_step(Expr/SizeStage(e.tok, e.bound, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/EitherP:
      (a, s1) = sz_eval(e.lft, maxs, zeros)
      (b, s2) = sz_eval(e.rgt, maxs, zeros)
      (r, s3) = sz_step(Expr/EitherP(e.tag, a, b), maxs, zeros)
      return (r, sr_merge(s1, sr_merge(s2, s3)))
    case Expr/IVar:
      return sz_step(Expr/IVar(e.path), maxs, zeros)
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    case _:
      return (Expr/EvalError(err_unhandled()), SR/SNil)

# defer-body walk: Env nodes replaced by env (an evaluated value)
def sz_body(d: Expr, env: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match d:
    case Expr/Defer:
      return (Expr/Defer(d.fid, d.body), SR/SNil)
    case Expr/Env:
      return (env, SR/SNil)
    case Expr/Zero:
      return (Expr/Zero, SR/SNil)
    case Expr/Pair:
      (a, s1) = sz_body(d.fst, env, maxs, zeros)
      (b, s2) = sz_body(d.snd, env, maxs, zeros)
      (r, s3) = sz_step(Expr/Pair(a, b), maxs, zeros)
      return (r, sr_merge(s1, sr_merge(s2, s3)))
    case Expr/SetEnv:
      (i, s1) = sz_body(d.inner, env, maxs, zeros)
      (r, s2) = sz_step(Expr/SetEnv(i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/Gate:
      (l, s1) = sz_body(d.lft, env, maxs, zeros)
      (r, s2) = sz_body(d.rgt, env, maxs, zeros)
      (g, s3) = sz_step(Expr/Gate(l, r), maxs, zeros)
      return (g, sr_merge(s1, sr_merge(s2, s3)))
    case Expr/PLeft:
      (i, s1) = sz_body(d.inner, env, maxs, zeros)
      (r, s2) = sz_step(Expr/PLeft(i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/PRight:
      (i, s1) = sz_body(d.inner, env, maxs, zeros)
      (r, s2) = sz_step(Expr/PRight(i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/Abort:
      return (Expr/Abort, SR/SNil)
    case Expr/Aborted:
      return (Expr/Aborted(d.val), SR/SNil)
    case Expr/RecursionTest:
      (i, s1) = sz_body(d.inner, env, maxs, zeros)
      (r, s2) = sz_step(Expr/RecursionTest(d.tok, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/UnsizedStub:
      (i, s1) = sz_body(d.inner, env, maxs, zeros)
      (r, s2) = sz_step(Expr/UnsizedStub(d.tok, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/SizeStepStub:
      (i, s1) = sz_body(d.inner, env, maxs, zeros)
      (r, s2) = sz_step(Expr/SizeStepStub(d.tok, d.num, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/SizeStage:
      (i, s1) = sz_body(d.inner, env, maxs, zeros)
      (r, s2) = sz_step(Expr/SizeStage(d.tok, d.bound, i), maxs, zeros)
      return (r, sr_merge(s1, s2))
    case Expr/EitherP:
      (a, s1) = sz_body(d.lft, env, maxs, zeros)
      (b, s2) = sz_body(d.rgt, env, maxs, zeros)
      (r, s3) = sz_step(Expr/EitherP(d.tag, a, b), maxs, zeros)
      return (r, sr_merge(s1, sr_merge(s2, s3)))
    case Expr/IVar:
      return sz_step(Expr/IVar(d.path), maxs, zeros)
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    case _:
      return (Expr/EvalError(err_unhandled()), SR/SNil)

# res helper (indexedInputStepM)
def iv_res(zeros: List(List(u24)), n: List(u24)) -> Expr:
  if set_member(zeros, n):
    return Expr/Zero
  else:
    return Expr/IVar(n)

def sz_step(e: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match e:
    # basicStepM: stuck values
    case Expr/Zero:
      return (Expr/Zero, SR/SNil)
    case Expr/Pair:
      return (Expr/Pair(e.fst, e.snd), SR/SNil)
    case Expr/SetEnv:
      return sz_setenv(e.inner, maxs, zeros)
    case Expr/PLeft:
      return sz_left(e.inner, maxs, zeros)
    case Expr/PRight:
      return sz_right(e.inner, maxs, zeros)
    # stuck values
    case Expr/Defer:
      return (Expr/Defer(e.fid, e.body), SR/SNil)
    case Expr/Gate:
      return (Expr/Gate(e.lft, e.rgt), SR/SNil)
    case Expr/Abort:
      return (Expr/Abort, SR/SNil)
    case Expr/Aborted:
      return (Expr/Aborted(e.val), SR/SNil)
    # indexedInputStepM
    case Expr/IVar:
      return (iv_res(zeros, e.path), SR/SNil)
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    # superStepM: stuck superposition
    case Expr/EitherP:
      return (Expr/EitherP(e.tag, e.lft, e.rgt), SR/SNil)
    # unsizedStepM'''
    case Expr/RecursionTest:
      return (unsized_test(zeros, e.tok, e.inner), SR/SNil)
    case Expr/SizeStage:
      return (e.inner, sr_one(e.tok, e.bound))
    case Expr/UnsizedStub:
      return sz_stub(e.tok, e.inner)
    case Expr/SizeStepStub:
      return sz_step_stub(e.tok, e.num, e.inner, maxs)
    case _:
      return (Expr/EvalError(err_unhandled()), SR/SNil)

# UnsizedStubF expansion (unsizedStepM''' first case). inner (after env
# substitution) = Pair(_, Pair(_, Pair(_, Pair(_, env)))) with
# env = Pair(b, Pair(r, Pair(Pair(Defer sid tf, e), Zero))).
def sz_stub(tok: u24, inner: Expr) -> (Expr, SR):
  match inner:
    case Expr/Pair:
      match inner.snd:
        case Expr/Pair:
          match inner.snd.snd:
            case Expr/Pair:
              match inner.snd.snd.snd:
                case Expr/Pair:
                  return sz_stub_env(tok, inner.snd.snd.snd.snd)
                case _:
                  return (Expr/EvalError(err_unhandled()), SR/SNil)
            case _:
              return (Expr/EvalError(err_unhandled()), SR/SNil)
        case _:
          return (Expr/EvalError(err_unhandled()), SR/SNil)
    case _:
      return (Expr/EvalError(err_unhandled()), SR/SNil)

def sz_stub_env(tok: u24, env: Expr) -> (Expr, SR):
  match env:
    case Expr/Pair:
      b = env.fst
      match env.snd:
        case Expr/Pair:
          r = env.snd.fst
          match env.snd.snd:
            case Expr/Pair:
              tp = env.snd.snd.fst
              match tp:
                case Expr/Pair:
                  match tp.fst:
                    case Expr/Defer:
                      sid = tp.fst.fid
                      tf = tp.fst.body
                      ee = tp.snd
                      nt = Expr/Pair(Expr/Defer(sid, Expr/RecursionTest(tok, tf)), ee)
                      trb = Expr/Pair(b, Expr/Pair(r, Expr/Pair(nt, Expr/Zero)))
                      rf = Expr/Defer(fid_unsized_rfa(),
                        ite_lazy(app_b(arg_four(), arg_one()),
                                 app_b(app_b(arg_three(), Expr/SizeStepStub(tok, 1, Expr/Env)), arg_one()),
                                 Expr/SizeStage(tok, 1, app_b(arg_two(), arg_one()))))
                      result = Expr/Pair(Expr/Zero, Expr/Pair(Expr/Zero, Expr/Pair(Expr/Zero, Expr/Pair(Expr/Pair(rf, trb), Expr/Zero))))
                      return (result, SR/SNil)
                    case _:
                      return (Expr/EvalError(err_unhandled()), SR/SNil)
                case _:
                  return (Expr/EvalError(err_unhandled()), SR/SNil)
            case _:
              return (Expr/EvalError(err_unhandled()), SR/SNil)
        case _:
          return (Expr/EvalError(err_unhandled()), SR/SNil)
    case _:
      return (Expr/EvalError(err_unhandled()), SR/SNil)

def sz_step_stub(tok: u24, n: u24, e: Expr, maxs: u24) -> (Expr, SR):
  if n > maxs:
    return (abort_recursion(n), SR/SNil)
  else:
    match e:
      case Expr/Pair:
        es = e.snd
        return (Expr/Pair(Expr/Defer(fid_unsized_rfa(), size_step_body(tok, n + 1, Expr/Pair(e.fst, es))), es), SR/SNil)
      case _:
        return (Expr/EvalError(err_unhandled()), SR/SNil)

# SetEnv dispatch (FillFunction/GateSwitch families across all step layers)
def sz_setenv(i: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match i:
    case Expr/Aborted:
      return (Expr/Aborted(i.val), SR/SNil)
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    case Expr/EitherP:
      # superStepM SetEnvSF: merge of stepping both sides
      (a, s1) = sz_step(Expr/SetEnv(i.lft), maxs, zeros)
      (b, s2) = sz_step(Expr/SetEnv(i.rgt), maxs, zeros)
      return (merge_shallow(i.tag, a, b), sr_merge(s1, s2))
    case Expr/Pair:
      return sz_fill(i.fst, i.snd, maxs, zeros)
    case _:
      return (Expr/EvalError(err_setenv_shape()), SR/SNil)

# FillFunction c e (both evaluated)
def sz_fill(c: Expr, en: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match c:
    case Expr/Defer:
      return sz_body(c.body, en, maxs, zeros)
    case Expr/Gate:
      return sz_gate(c.lft, c.rgt, en, maxs, zeros)
    case Expr/Aborted:
      return (Expr/Aborted(c.val), SR/SNil)
    case Expr/Abort:
      return sz_abort_fill(en, maxs, zeros)
    case Expr/EitherP:
      # superStepM FillFunction: filter env per side when tag is Just.
      # Only materialize a filtered copy when the scan finds matching
      # superpositions in the env (else pass the shared env through).
      match c.tag:
        case List/Cons:
          tg = List/Cons(c.tag.head, c.tag.tail)
          (wl, wr) = super_filter_work(tg, en)
          if wl:
            el = filter_left(tg, en)
          else:
            el = en
          if wr:
            er = filter_right(tg, en)
          else:
            er = en
          (a, s1) = sz_step(Expr/SetEnv(Expr/Pair(c.lft, el)), maxs, zeros)
          (b, s2) = sz_step(Expr/SetEnv(Expr/Pair(c.rgt, er)), maxs, zeros)
          return (merge_shallow(tg, a, b), sr_merge(s1, s2))
        case List/Nil:
          (a, s1) = sz_step(Expr/SetEnv(Expr/Pair(c.lft, en)), maxs, zeros)
          (b, s2) = sz_step(Expr/SetEnv(Expr/Pair(c.rgt, en)), maxs, zeros)
          return (merge_shallow(List/Nil, a, b), sr_merge(s1, s2))
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    case _:
      return (Expr/EvalError(err_fill_shape()), SR/SNil)

# GateSwitch l r s (s evaluated)
def sz_gate(l: Expr, r: Expr, s: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match s:
    case Expr/Zero:
      return (l, SR/SNil)
    case Expr/Pair:
      return (r, SR/SNil)
    case Expr/Aborted:
      return (Expr/Aborted(s.val), SR/SNil)
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    case Expr/IVar:
      # indexedSuperStepM: superpose both branches, tagged by the input var
      return (Expr/EitherP(List/Cons(1, s.path), l, r), SR/SNil)
    case Expr/EitherP:
      return (fold_gate_result(s.tag, l, r, gate_result(Expr/EitherP(s.tag, s.lft, s.rgt))), SR/SNil)
    case _:
      return (Expr/EvalError(err_gate_shape()), SR/SNil)

# FillFunction Abort en
def sz_abort_fill(en: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match en:
    case Expr/Aborted:
      return (Expr/Aborted(en.val), SR/SNil)
    case Expr/Zero:
      return (Expr/Defer(fid_abort(), Expr/Env), SR/SNil)
    case Expr/Pair:
      return (Expr/Aborted(truncate_basic(Expr/Pair(en.fst, en.snd))), SR/SNil)
    case Expr/IVar:
      # indexedAbortStepM
      return (abort_any(), SR/SNil)
    case Expr/EitherP:
      # superAbortStepM
      (a, s1) = sz_step(Expr/SetEnv(Expr/Pair(Expr/Abort, en.lft)), maxs, zeros)
      (b, s2) = sz_step(Expr/SetEnv(Expr/Pair(Expr/Abort, en.rgt)), maxs, zeros)
      return (merge_shallow(en.tag, a, b), sr_merge(s1, s2))
    case _:
      return (Expr/EvalError(err_fill_shape()), SR/SNil)

# PLeft dispatch
def sz_left(i: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match i:
    case Expr/Zero:
      return (Expr/Zero, SR/SNil)
    case Expr/Pair:
      return (i.fst, SR/SNil)
    case Expr/Aborted:
      return (Expr/Aborted(i.val), SR/SNil)
    case Expr/IVar:
      return (iv_res(zeros, path_snoc(i.path, 0)), SR/SNil)
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    case Expr/EitherP:
      (a, s1) = sz_step(Expr/PLeft(i.lft), maxs, zeros)
      (b, s2) = sz_step(Expr/PLeft(i.rgt), maxs, zeros)
      return (merge_shallow(i.tag, a, b), sr_merge(s1, s2))
    case _:
      return (Expr/EvalError(err_left_shape()), SR/SNil)

# PRight dispatch
def sz_right(i: Expr, maxs: u24, zeros: List(List(u24))) -> (Expr, SR):
  match i:
    case Expr/Zero:
      return (Expr/Zero, SR/SNil)
    case Expr/Pair:
      return (i.snd, SR/SNil)
    case Expr/Aborted:
      return (Expr/Aborted(i.val), SR/SNil)
    case Expr/IVar:
      return (iv_res(zeros, path_snoc(i.path, 1)), SR/SNil)
    case Expr/AnyE:
      return (Expr/AnyE, SR/SNil)
    case Expr/EitherP:
      (a, s1) = sz_step(Expr/PRight(i.lft), maxs, zeros)
      (b, s2) = sz_step(Expr/PRight(i.rgt), maxs, zeros)
      return (merge_shallow(i.tag, a, b), sr_merge(s1, s2))
    case _:
      return (Expr/EvalError(err_right_shape()), SR/SNil)

# ---------------------------------------------------------------------------
# Input limits (getInputLimits): find guaranteed-Zero / guaranteed-Pair input
# paths from refinement checks. InputRestrictions = (zeroes, pairs).
# ---------------------------------------------------------------------------

# convert for input-sizing: UnsizedStub -> AnyE, RecursionTest -> strip
def convert_il(e: Expr) -> Expr:
  match e:
    case Expr/UnsizedStub:
      return Expr/AnyE
    case Expr/RecursionTest:
      return convert_il(e.inner)
    case Expr/Pair:
      return Expr/Pair(convert_il(e.fst), convert_il(e.snd))
    case Expr/SetEnv:
      return Expr/SetEnv(convert_il(e.inner))
    case Expr/Gate:
      return Expr/Gate(convert_il(e.lft), convert_il(e.rgt))
    case Expr/PLeft:
      return Expr/PLeft(convert_il(e.inner))
    case Expr/PRight:
      return Expr/PRight(convert_il(e.inner))
    case Expr/Defer:
      return Expr/Defer(e.fid, convert_il(e.body))
    case Expr/RefinementWrapper:
      return Expr/RefinementWrapper(e.loc, convert_il(e.tc), convert_il(e.chk))
    case _:
      return e

# il_eval: transformNoDeferM with the input-limits chain, accumulating
# (zeroes, pairs). Chain: basic/stuck/abort/indexedInput(∅)/
# indexedInputIgnoreSwitch/findInputLimit.
def il_eval(e: Expr) -> (Expr, List(List(u24)), List(List(u24))):
  match e:
    case Expr/Defer:
      return (Expr/Defer(e.fid, e.body), List/Nil, List/Nil)
    case Expr/Zero:
      return (Expr/Zero, List/Nil, List/Nil)
    case Expr/Env:
      return (Expr/Env, List/Nil, List/Nil)
    case Expr/Pair:
      (a, z1, p1) = il_eval(e.fst)
      (b, z2, p2) = il_eval(e.snd)
      (r, z3, p3) = il_step(Expr/Pair(a, b))
      return (r, set_union(z1, set_union(z2, z3)), set_union(p1, set_union(p2, p3)))
    case Expr/SetEnv:
      (i, z1, p1) = il_eval(e.inner)
      (r, z2, p2) = il_step(Expr/SetEnv(i))
      return (r, set_union(z1, z2), set_union(p1, p2))
    case Expr/Gate:
      (l, z1, p1) = il_eval(e.lft)
      (r, z2, p2) = il_eval(e.rgt)
      (g, z3, p3) = il_step(Expr/Gate(l, r))
      return (g, set_union(z1, set_union(z2, z3)), set_union(p1, set_union(p2, p3)))
    case Expr/PLeft:
      (i, z1, p1) = il_eval(e.inner)
      (r, z2, p2) = il_step(Expr/PLeft(i))
      return (r, set_union(z1, z2), set_union(p1, p2))
    case Expr/PRight:
      (i, z1, p1) = il_eval(e.inner)
      (r, z2, p2) = il_step(Expr/PRight(i))
      return (r, set_union(z1, z2), set_union(p1, p2))
    case Expr/Abort:
      return (Expr/Abort, List/Nil, List/Nil)
    case Expr/Aborted:
      return (Expr/Aborted(e.val), List/Nil, List/Nil)
    case Expr/RefinementWrapper:
      (tc, z1, p1) = il_eval(e.tc)
      (c, z2, p2) = il_eval(e.chk)
      (z3, p3) = find_input_limits(tc, c)
      return (c, set_union(z1, set_union(z2, z3)), set_union(p1, set_union(p2, p3)))
    case Expr/IVar:
      return (Expr/IVar(e.path), List/Nil, List/Nil)
    case Expr/AnyE:
      return (Expr/AnyE, List/Nil, List/Nil)
    case _:
      return (Expr/EvalError(err_unhandled()), List/Nil, List/Nil)

def il_body(d: Expr, env: Expr) -> (Expr, List(List(u24)), List(List(u24))):
  match d:
    case Expr/Defer:
      return (Expr/Defer(d.fid, d.body), List/Nil, List/Nil)
    case Expr/Env:
      return (env, List/Nil, List/Nil)
    case Expr/Zero:
      return (Expr/Zero, List/Nil, List/Nil)
    case Expr/Pair:
      (a, z1, p1) = il_body(d.fst, env)
      (b, z2, p2) = il_body(d.snd, env)
      (r, z3, p3) = il_step(Expr/Pair(a, b))
      return (r, set_union(z1, set_union(z2, z3)), set_union(p1, set_union(p2, p3)))
    case Expr/SetEnv:
      (i, z1, p1) = il_body(d.inner, env)
      (r, z2, p2) = il_step(Expr/SetEnv(i))
      return (r, set_union(z1, z2), set_union(p1, p2))
    case Expr/Gate:
      (l, z1, p1) = il_body(d.lft, env)
      (r, z2, p2) = il_body(d.rgt, env)
      (g, z3, p3) = il_step(Expr/Gate(l, r))
      return (g, set_union(z1, set_union(z2, z3)), set_union(p1, set_union(p2, p3)))
    case Expr/PLeft:
      (i, z1, p1) = il_body(d.inner, env)
      (r, z2, p2) = il_step(Expr/PLeft(i))
      return (r, set_union(z1, z2), set_union(p1, p2))
    case Expr/PRight:
      (i, z1, p1) = il_body(d.inner, env)
      (r, z2, p2) = il_step(Expr/PRight(i))
      return (r, set_union(z1, z2), set_union(p1, p2))
    case Expr/Abort:
      return (Expr/Abort, List/Nil, List/Nil)
    case Expr/Aborted:
      return (Expr/Aborted(d.val), List/Nil, List/Nil)
    case Expr/RefinementWrapper:
      (tc, z1, p1) = il_body(d.tc, env)
      (c, z2, p2) = il_body(d.chk, env)
      (z3, p3) = find_input_limits(tc, c)
      return (c, set_union(z1, set_union(z2, z3)), set_union(p1, set_union(p2, p3)))
    case Expr/IVar:
      return (Expr/IVar(d.path), List/Nil, List/Nil)
    case Expr/AnyE:
      return (Expr/AnyE, List/Nil, List/Nil)
    case _:
      return (Expr/EvalError(err_unhandled()), List/Nil, List/Nil)

def il_step(e: Expr) -> (Expr, List(List(u24)), List(List(u24))):
  match e:
    case Expr/Zero:
      return (Expr/Zero, List/Nil, List/Nil)
    case Expr/Pair:
      return (Expr/Pair(e.fst, e.snd), List/Nil, List/Nil)
    case Expr/SetEnv:
      return il_setenv(e.inner)
    case Expr/PLeft:
      return il_left(e.inner)
    case Expr/PRight:
      return il_right(e.inner)
    case Expr/Defer:
      return (Expr/Defer(e.fid, e.body), List/Nil, List/Nil)
    case Expr/Gate:
      return (Expr/Gate(e.lft, e.rgt), List/Nil, List/Nil)
    case Expr/Abort:
      return (Expr/Abort, List/Nil, List/Nil)
    case Expr/Aborted:
      return (Expr/Aborted(e.val), List/Nil, List/Nil)
    case Expr/IVar:
      return (Expr/IVar(e.path), List/Nil, List/Nil)
    case Expr/AnyE:
      return (Expr/AnyE, List/Nil, List/Nil)
    case _:
      return (Expr/EvalError(err_unhandled()), List/Nil, List/Nil)

def il_setenv(i: Expr) -> (Expr, List(List(u24)), List(List(u24))):
  match i:
    case Expr/Aborted:
      return (Expr/Aborted(i.val), List/Nil, List/Nil)
    case Expr/AnyE:
      return (Expr/AnyE, List/Nil, List/Nil)
    case Expr/Pair:
      f = i.fst
      en = i.snd
      match f:
        case Expr/Defer:
          return il_body(f.body, en)
        case Expr/Gate:
          match en:
            case Expr/Zero:
              return (f.lft, List/Nil, List/Nil)
            case Expr/Pair:
              return (f.rgt, List/Nil, List/Nil)
            case Expr/Aborted:
              return (Expr/Aborted(en.val), List/Nil, List/Nil)
            case Expr/IVar:
              # indexedInputIgnoreSwitchStepM
              return (Expr/AnyE, List/Nil, List/Nil)
            case Expr/AnyE:
              return (Expr/AnyE, List/Nil, List/Nil)
            case _:
              return (Expr/EvalError(err_gate_shape()), List/Nil, List/Nil)
        case Expr/Aborted:
          return (Expr/Aborted(f.val), List/Nil, List/Nil)
        case Expr/Abort:
          match en:
            case Expr/Aborted:
              return (Expr/Aborted(en.val), List/Nil, List/Nil)
            case Expr/Zero:
              return (Expr/Defer(fid_abort(), Expr/Env), List/Nil, List/Nil)
            case Expr/Pair:
              return (Expr/Aborted(truncate_basic(Expr/Pair(en.fst, en.snd))), List/Nil, List/Nil)
            case _:
              return (Expr/EvalError(err_fill_shape()), List/Nil, List/Nil)
        case Expr/AnyE:
          return (Expr/AnyE, List/Nil, List/Nil)
        case _:
          return (Expr/EvalError(err_fill_shape()), List/Nil, List/Nil)
    case _:
      return (Expr/EvalError(err_setenv_shape()), List/Nil, List/Nil)

def il_left(i: Expr) -> (Expr, List(List(u24)), List(List(u24))):
  match i:
    case Expr/Zero:
      return (Expr/Zero, List/Nil, List/Nil)
    case Expr/Pair:
      return (i.fst, List/Nil, List/Nil)
    case Expr/Aborted:
      return (Expr/Aborted(i.val), List/Nil, List/Nil)
    case Expr/IVar:
      return (Expr/IVar(path_snoc(i.path, 0)), List/Nil, List/Nil)
    case Expr/AnyE:
      return (Expr/AnyE, List/Nil, List/Nil)
    case _:
      return (Expr/EvalError(err_left_shape()), List/Nil, List/Nil)

def il_right(i: Expr) -> (Expr, List(List(u24)), List(List(u24))):
  match i:
    case Expr/Zero:
      return (Expr/Zero, List/Nil, List/Nil)
    case Expr/Pair:
      return (i.snd, List/Nil, List/Nil)
    case Expr/Aborted:
      return (Expr/Aborted(i.val), List/Nil, List/Nil)
    case Expr/IVar:
      return (Expr/IVar(path_snoc(i.path, 1)), List/Nil, List/Nil)
    case Expr/AnyE:
      return (Expr/AnyE, List/Nil, List/Nil)
    case _:
      return (Expr/EvalError(err_right_shape()), List/Nil, List/Nil)

# findInputLimitStepM: run the refinement check performTC =
# SetEnv(Pair(Abort, app_b(tc, c))) through the pure barrier evaluator,
# strip barriers, extract restrictions.
def find_input_limits(tc: Expr, c: Expr) -> (List(List(u24)), List(List(u24))):
  perform = Expr/SetEnv(Expr/Pair(Expr/Abort, app_b(tc, c)))
  r = strip_barriers(pv_eval(perform))
  (has, z, p) = extract_ir(0, r)
  return (z, p)

def strip_barriers(e: Expr) -> Expr:
  match e:
    case Expr/Barrier:
      return strip_barriers(e.inner)
    case Expr/Pair:
      return Expr/Pair(strip_barriers(e.fst), strip_barriers(e.snd))
    case Expr/SetEnv:
      return Expr/SetEnv(strip_barriers(e.inner))
    case Expr/Gate:
      return Expr/Gate(strip_barriers(e.lft), strip_barriers(e.rgt))
    case Expr/PLeft:
      return Expr/PLeft(strip_barriers(e.inner))
    case Expr/PRight:
      return Expr/PRight(strip_barriers(e.inner))
    case Expr/Defer:
      return Expr/Defer(e.fid, strip_barriers(e.body))
    case Expr/ManyLefts:
      return Expr/ManyLefts(e.num, strip_barriers(e.inner))
    case Expr/ManyRights:
      return Expr/ManyRights(e.num, strip_barriers(e.inner))
    case Expr/Aborted:
      return Expr/Aborted(e.val)
    case _:
      return e

# ---------------------------------------------------------------------------
# pure barrier evaluator (findInputLimitStepM's inner ev): basicStep/
# stuckStep/abortStep/deferredEvalStep/abortDeferredStep/
# indexedInputStep'(∅, wrapDefer)
# ---------------------------------------------------------------------------

def pv_eval(e: Expr) -> Expr:
  match e:
    case Expr/Defer:
      return Expr/Defer(e.fid, e.body)
    case Expr/Zero:
      return Expr/Zero
    case Expr/Env:
      return Expr/Env
    case Expr/Pair:
      return pv_step(Expr/Pair(pv_eval(e.fst), pv_eval(e.snd)))
    case Expr/SetEnv:
      return pv_step(Expr/SetEnv(pv_eval(e.inner)))
    case Expr/Gate:
      return pv_step(Expr/Gate(pv_eval(e.lft), pv_eval(e.rgt)))
    case Expr/PLeft:
      return pv_step(Expr/PLeft(pv_eval(e.inner)))
    case Expr/PRight:
      return pv_step(Expr/PRight(pv_eval(e.inner)))
    case Expr/Abort:
      return Expr/Abort
    case Expr/Aborted:
      return Expr/Aborted(e.val)
    case Expr/IVar:
      return Expr/IVar(e.path)
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      return pv_step(Expr/Barrier(pv_eval(e.inner)))
    case Expr/ManyLefts:
      return Expr/ManyLefts(e.num, e.inner)
    case Expr/ManyRights:
      return Expr/ManyRights(e.num, e.inner)
    case _:
      return Expr/EvalError(err_unhandled())

def pv_body(d: Expr, env: Expr) -> Expr:
  match d:
    case Expr/Defer:
      return Expr/Defer(d.fid, d.body)
    case Expr/Env:
      return env
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return pv_step(Expr/Pair(pv_body(d.fst, env), pv_body(d.snd, env)))
    case Expr/SetEnv:
      return pv_step(Expr/SetEnv(pv_body(d.inner, env)))
    case Expr/Gate:
      return pv_step(Expr/Gate(pv_body(d.lft, env), pv_body(d.rgt, env)))
    case Expr/PLeft:
      return pv_step(Expr/PLeft(pv_body(d.inner, env)))
    case Expr/PRight:
      return pv_step(Expr/PRight(pv_body(d.inner, env)))
    case Expr/Abort:
      return Expr/Abort
    case Expr/Aborted:
      return Expr/Aborted(d.val)
    case Expr/IVar:
      return Expr/IVar(d.path)
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      return pv_step(Expr/Barrier(pv_body(d.inner, env)))
    case Expr/ManyLefts:
      return Expr/ManyLefts(d.num, d.inner)
    case Expr/ManyRights:
      return Expr/ManyRights(d.num, d.inner)
    case _:
      return Expr/EvalError(err_unhandled())

def pv_step(e: Expr) -> Expr:
  match e:
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return Expr/Pair(e.fst, e.snd)
    case Expr/SetEnv:
      return pv_setenv(e.inner)
    case Expr/PLeft:
      return pv_left(e.inner)
    case Expr/PRight:
      return pv_right(e.inner)
    case Expr/Defer:
      return Expr/Defer(e.fid, e.body)
    case Expr/Gate:
      return Expr/Gate(e.lft, e.rgt)
    case Expr/Abort:
      return Expr/Abort
    case Expr/Aborted:
      return Expr/Aborted(e.val)
    case Expr/IVar:
      return Expr/IVar(e.path)
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      return Expr/Barrier(e.inner)
    case Expr/ManyLefts:
      return Expr/ManyLefts(e.num, e.inner)
    case Expr/ManyRights:
      return Expr/ManyRights(e.num, e.inner)
    case _:
      return Expr/EvalError(err_unhandled())

def pv_setenv(i: Expr) -> Expr:
  match i:
    case Expr/Aborted:
      return Expr/Aborted(i.val)
    case Expr/Barrier:
      # deferredEvalStep: SetEnv(Barrier x) -> Barrier(SetEnv x)
      return Expr/Barrier(Expr/SetEnv(i.inner))
    case Expr/Pair:
      f = i.fst
      en = i.snd
      match f:
        case Expr/Defer:
          return pv_body(f.body, en)
        case Expr/Gate:
          match en:
            case Expr/Zero:
              return f.lft
            case Expr/Pair:
              return f.rgt
            case Expr/Aborted:
              return Expr/Aborted(en.val)
            case Expr/IVar:
              # wrapDefer: barrier the switch, evaluating both branches
              return Expr/Barrier(Expr/SetEnv(Expr/Pair(Expr/Gate(pv_eval(f.lft), pv_eval(f.rgt)), Expr/IVar(en.path))))
            case Expr/Barrier:
              return Expr/Barrier(Expr/SetEnv(Expr/Pair(Expr/Gate(f.lft, f.rgt), en.inner)))
            case _:
              return Expr/EvalError(err_gate_shape())
        case Expr/Aborted:
          return Expr/Aborted(f.val)
        case Expr/Abort:
          match en:
            case Expr/Aborted:
              return Expr/Aborted(en.val)
            case Expr/Zero:
              return Expr/Defer(fid_abort(), Expr/Env)
            case Expr/Pair:
              return Expr/Aborted(truncate_basic(Expr/Pair(en.fst, en.snd)))
            case Expr/Barrier:
              # abortDeferredStep
              return Expr/Barrier(Expr/SetEnv(Expr/Pair(Expr/Abort, en.inner)))
            case _:
              return Expr/EvalError(err_fill_shape())
        case Expr/Barrier:
          # FillFunction (Barrier c) e -> Barrier (FillFunction c e)
          return Expr/Barrier(Expr/SetEnv(Expr/Pair(f.inner, en)))
        case _:
          return Expr/EvalError(err_fill_shape())
    case _:
      return Expr/EvalError(err_setenv_shape())

def pv_left(i: Expr) -> Expr:
  match i:
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return i.fst
    case Expr/Aborted:
      return Expr/Aborted(i.val)
    case Expr/IVar:
      return Expr/IVar(path_snoc(i.path, 0))
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      # deferredEvalStep barrier combining
      match i.inner:
        case Expr/ManyLefts:
          return Expr/Barrier(Expr/ManyLefts(i.inner.num + 1, i.inner.inner))
        case _:
          return Expr/Barrier(Expr/ManyLefts(1, i.inner))
    case _:
      return Expr/EvalError(err_left_shape())

def pv_right(i: Expr) -> Expr:
  match i:
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return i.snd
    case Expr/Aborted:
      return Expr/Aborted(i.val)
    case Expr/IVar:
      return Expr/IVar(path_snoc(i.path, 1))
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      match i.inner:
        case Expr/ManyRights:
          return Expr/Barrier(Expr/ManyRights(i.inner.num + 1, i.inner.inner))
        case _:
          return Expr/Barrier(Expr/ManyRights(1, i.inner))
    case _:
      return Expr/EvalError(err_right_shape())

# ---------------------------------------------------------------------------
# extractInputRestrictions. expected: 0 = Nothing, 1 = Just False (must not
# be zero), 2 = Just True (must be pair... note Haskell: Just True on Zero
# fails, Just False on Pair fails; IVar with Just False -> zero restriction,
# Just True -> pair restriction). Returns (has_result, zeroes, pairs).
# ---------------------------------------------------------------------------

def extract_ir(expected: u24, e: Expr) -> (u24, List(List(u24)), List(List(u24))):
  match e:
    case Expr/Zero:
      if expected == 2:
        return (0, List/Nil, List/Nil)
      else:
        return (1, List/Nil, List/Nil)
    case Expr/Pair:
      if expected == 1:
        return (0, List/Nil, List/Nil)
      else:
        return (1, List/Nil, List/Nil)
    case Expr/IVar:
      if expected == 1:
        return (1, [e.path], List/Nil)
      else:
        if expected == 2:
          return (1, List/Nil, [e.path])
        else:
          return (1, List/Nil, List/Nil)
    case Expr/SetEnv:
      # FillFunction (Abort) i  /  GateSwitch l r s
      match e.inner:
        case Expr/Pair:
          f = e.inner.fst
          i = e.inner.snd
          match f:
            case Expr/Abort:
              return extract_ir(1, i)
            case Expr/Gate:
              return extract_ir_gate(expected, f.lft, f.rgt, i)
            case _:
              return (0, List/Nil, List/Nil)
        case _:
          return (0, List/Nil, List/Nil)
    case _:
      return (0, List/Nil, List/Nil)

def extract_ir_gate(expected: u24, l: Expr, r: Expr, s: Expr) -> (u24, List(List(u24)), List(List(u24))):
  (hl, zl, pl) = extract_ir(expected, l)
  (hr, zr, pr) = extract_ir(expected, r)
  if hl & hr:
    (hs, zs, ps) = extract_ir(0, s)
    if hs:
      # both branches possible: only what BOTH require + scrutinee's own
      return (1, set_union(zs, set_intersect(zl, zr)), set_union(ps, set_intersect(pl, pr)))
    else:
      return (0, List/Nil, List/Nil)
  else:
    if hl:
      # only left survives: scrutinee must be Zero
      (hs, zs, ps) = extract_ir(1, s)
      if hs:
        return (1, set_union(zl, zs), set_union(pl, ps))
      else:
        return (0, List/Nil, List/Nil)
    else:
      if hr:
        (hs, zs, ps) = extract_ir(2, s)
        if hs:
          return (1, set_union(zr, zs), set_union(pr, ps))
        else:
          return (0, List/Nil, List/Nil)
      else:
        return (0, List/Nil, List/Nil)

# NOTE: Haskell's irIntersection is actually a UNION of both sides' sets
# (see Possible.hs:804 — (za <> zb)); the name is misleading. Mirror it.
def set_intersect(a: List(List(u24)), b: List(List(u24))) -> List(List(u24)):
  return set_union(a, b)

# ---------------------------------------------------------------------------
# removeRefinementWrappers, capMain, initialInput
# ---------------------------------------------------------------------------

def remove_refinement_wrappers(e: Expr) -> Expr:
  match e:
    case Expr/RefinementWrapper:
      inner_tc = app_b(Expr/PLeft(Expr/Env), Expr/PRight(Expr/Env))
      perform = Expr/Defer(fid_remove_refinement_tc(),
        Expr/SetEnv(Expr/Pair(Expr/SetEnv(Expr/Pair(Expr/Abort, inner_tc)), Expr/PRight(Expr/Env))))
      return Expr/SetEnv(Expr/Pair(perform, Expr/Pair(remove_refinement_wrappers(e.tc), remove_refinement_wrappers(e.chk))))
    case Expr/Pair:
      return Expr/Pair(remove_refinement_wrappers(e.fst), remove_refinement_wrappers(e.snd))
    case Expr/SetEnv:
      return Expr/SetEnv(remove_refinement_wrappers(e.inner))
    case Expr/Gate:
      return Expr/Gate(remove_refinement_wrappers(e.lft), remove_refinement_wrappers(e.rgt))
    case Expr/PLeft:
      return Expr/PLeft(remove_refinement_wrappers(e.inner))
    case Expr/PRight:
      return Expr/PRight(remove_refinement_wrappers(e.inner))
    case Expr/Defer:
      return Expr/Defer(e.fid, remove_refinement_wrappers(e.body))
    case Expr/UnsizedStub:
      return Expr/UnsizedStub(e.tok, remove_refinement_wrappers(e.inner))
    case _:
      return e

def cap_main(i: Expr, c: Expr) -> Expr:
  return app_b(c, i)

def initial_input(pairs: List(List(u24))) -> Expr:
  return initial_input_go([], pairs)

def initial_input_go(n: List(u24), pairs: List(List(u24))) -> Expr:
  if any_dec_of(pairs, n):
    return Expr/Pair(initial_input_go(path_snoc(n, 0), pairs), initial_input_go(path_snoc(n, 1), pairs))
  else:
    return Expr/IVar(n)

# ---------------------------------------------------------------------------
# setSizes + final conversion
# ---------------------------------------------------------------------------

# UnsizedStub tok _ -> SetEnv^(n+1) Env when sized; SetEnv Env otherwise.
def set_sizes(sm: SR, e: Expr) -> Expr:
  match e:
    case Expr/UnsizedStub:
      (found, n) = sr_lookup(sm, e.tok)
      if found:
        return setenv_n(n + 1, Expr/Env)
      else:
        return Expr/SetEnv(Expr/Env)
    case Expr/Pair:
      return Expr/Pair(set_sizes(sm, e.fst), set_sizes(sm, e.snd))
    case Expr/SetEnv:
      return Expr/SetEnv(set_sizes(sm, e.inner))
    case Expr/Gate:
      return Expr/Gate(set_sizes(sm, e.lft), set_sizes(sm, e.rgt))
    case Expr/PLeft:
      return Expr/PLeft(set_sizes(sm, e.inner))
    case Expr/PRight:
      return Expr/PRight(set_sizes(sm, e.inner))
    case Expr/Defer:
      return Expr/Defer(e.fid, set_sizes(sm, e.body))
    case _:
      return e

# uncap: AppEE c _ -> c. The appB structure is
# SetEnv(SetEnv(Pair(Defer tw twiddle, Pair(i, c)))) — extract c.
def uncap(e: Expr) -> Expr:
  match e:
    case Expr/SetEnv:
      match e.inner:
        case Expr/SetEnv:
          match e.inner.inner:
            case Expr/Pair:
              match e.inner.inner.snd:
                case Expr/Pair:
                  return e.inner.inner.snd.snd
                case _:
                  return Expr/EvalError(err_unhandled())
            case _:
              return Expr/EvalError(err_unhandled())
        case _:
          return Expr/EvalError(err_unhandled())
    case _:
      return Expr/EvalError(err_unhandled())

# foldAborted: scan for Aborted(AbortRecursion/AbortAny/AbortUnsizeable).
# returns (found_kind, value): kind 0 = none.
def fold_aborted(e: Expr) -> (u24, u24):
  match e:
    case Expr/Aborted:
      (kind, v) = classify_abort(e.val)
      return (kind, v)
    case Expr/Pair:
      (k1, v1) = fold_aborted(e.fst)
      if k1 > 0:
        return (k1, v1)
      else:
        return fold_aborted(e.snd)
    case Expr/SetEnv:
      return fold_aborted(e.inner)
    case Expr/Gate:
      (k1, v1) = fold_aborted(e.lft)
      if k1 > 0:
        return (k1, v1)
      else:
        return fold_aborted(e.rgt)
    case Expr/PLeft:
      return fold_aborted(e.inner)
    case Expr/PRight:
      return fold_aborted(e.inner)
    case Expr/Defer:
      return fold_aborted(e.body)
    case Expr/EitherP:
      (k1, v1) = fold_aborted(e.lft)
      if k1 > 0:
        return (k1, v1)
      else:
        return fold_aborted(e.rgt)
    case Expr/SizeStage:
      return fold_aborted(e.inner)
    case Expr/RecursionTest:
      return fold_aborted(e.inner)
    case Expr/SizeStepStub:
      return fold_aborted(e.inner)
    case Expr/UnsizedStub:
      return fold_aborted(e.inner)
    case Expr/ManyLefts:
      return fold_aborted(e.inner)
    case Expr/ManyRights:
      return fold_aborted(e.inner)
    case Expr/Barrier:
      return fold_aborted(e.inner)
    case _:
      return (0, 0)

# scan a compiled term for leftover EvalError (clean/verify equivalent)
def has_eval_error(e: Expr) -> u24:
  match e:
    case Expr/EvalError:
      return 1
    case Expr/Pair:
      return has_eval_error(e.fst) | has_eval_error(e.snd)
    case Expr/SetEnv:
      return has_eval_error(e.inner)
    case Expr/Gate:
      return has_eval_error(e.lft) | has_eval_error(e.rgt)
    case Expr/PLeft:
      return has_eval_error(e.inner)
    case Expr/PRight:
      return has_eval_error(e.inner)
    case Expr/Defer:
      return has_eval_error(e.body)
    case Expr/Aborted:
      return has_eval_error(e.val)
    case _:
      return 0

# convertNakedEnvs (sizeTermM, doCap = False): naked Env outside defer
# bodies becomes Zero.
def convert_naked_envs(e: Expr) -> Expr:
  match e:
    case Expr/Env:
      return Expr/Zero
    case Expr/Defer:
      return Expr/Defer(e.fid, e.body)
    case Expr/Pair:
      return Expr/Pair(convert_naked_envs(e.fst), convert_naked_envs(e.snd))
    case Expr/SetEnv:
      return Expr/SetEnv(convert_naked_envs(e.inner))
    case Expr/Gate:
      return Expr/Gate(convert_naked_envs(e.lft), convert_naked_envs(e.rgt))
    case Expr/PLeft:
      return Expr/PLeft(convert_naked_envs(e.inner))
    case Expr/PRight:
      return Expr/PRight(convert_naked_envs(e.inner))
    case Expr/RefinementWrapper:
      return Expr/RefinementWrapper(e.loc, convert_naked_envs(e.tc), convert_naked_envs(e.chk))
    case Expr/UnsizedStub:
      return Expr/UnsizedStub(e.tok, convert_naked_envs(e.inner))
    case _:
      return e

# ---------------------------------------------------------------------------
# sizeTermM. do_cap = 1 for main-function sizing (input capped with IVar 0),
# 0 for unit-test terms (naked Envs zeroed, no uncap).
# Returns (status, compiled, sizes, err_val):
#   status 0 = OK; 1 = recursion limit hit (err_val = count);
#   2 = AbortAny; 3 = unsizeable (err_val = token); 4 = internal error.
# ---------------------------------------------------------------------------

def size_term(maxs: u24, do_cap: u24, x: Expr) -> (u24, Expr, SR, u24):
  if do_cap:
    cmp = cap_main(Expr/IVar([]), x)
    (ilr, zeros, prs) = il_eval(convert_il(cmp))
    cm = remove_refinement_wrappers(cmp)
    mx = remove_refinement_wrappers(cap_main(initial_input(prs), x))
    (r, sm) = sz_eval(mx, maxs, zeros)
    (kind, v) = fold_aborted(r)
    if kind == 0:
      sized = uncap(set_sizes(sm, cm))
      if has_eval_error(sized):
        return (4, Expr/Zero, sm, 0)
      else:
        return (0, sized, sm, 0)
    else:
      return (kind, Expr/Zero, sm, v)
  else:
    (ilr, zeros, prs) = il_eval(convert_il(x))
    cm = remove_refinement_wrappers(x)
    mx = remove_refinement_wrappers(convert_naked_envs(x))
    (r, sm) = sz_eval(mx, maxs, zeros)
    (kind, v) = fold_aborted(r)
    if kind == 0:
      sized = set_sizes(sm, cm)
      if has_eval_error(sized):
        return (4, Expr/Zero, sm, 0)
      else:
        return (0, sized, sm, 0)
    else:
      return (kind, Expr/Zero, sm, v)


# ---------------------------------------------------------------------------
# Diagnostics: node count of the abstract result (perf investigation).
# ---------------------------------------------------------------------------

def expr_nodes(e: Expr) -> u24:
  match e:
    case Expr/Pair:
      return 1 + expr_nodes(e.fst) + expr_nodes(e.snd)
    case Expr/SetEnv:
      return 1 + expr_nodes(e.inner)
    case Expr/Gate:
      return 1 + expr_nodes(e.lft) + expr_nodes(e.rgt)
    case Expr/PLeft:
      return 1 + expr_nodes(e.inner)
    case Expr/PRight:
      return 1 + expr_nodes(e.inner)
    case Expr/Defer:
      return 1 + expr_nodes(e.body)
    case Expr/Aborted:
      return 1 + expr_nodes(e.val)
    case Expr/EitherP:
      return 1 + expr_nodes(e.lft) + expr_nodes(e.rgt)
    case Expr/RecursionTest:
      return 1 + expr_nodes(e.inner)
    case Expr/UnsizedStub:
      return 1 + expr_nodes(e.inner)
    case Expr/SizeStepStub:
      return 1 + expr_nodes(e.inner)
    case Expr/SizeStage:
      return 1 + expr_nodes(e.inner)
    case Expr/RefinementWrapper:
      return 1 + expr_nodes(e.tc) + expr_nodes(e.chk)
    case Expr/Barrier:
      return 1 + expr_nodes(e.inner)
    case Expr/ManyLefts:
      return 1 + expr_nodes(e.inner)
    case Expr/ManyRights:
      return 1 + expr_nodes(e.inner)
    case _:
      return 1

# like size_term (doCap=1) but reports the abstract result's node count
def size_term_diag(maxs: u24, x: Expr) -> (u24, u24, SR):
  cmp = cap_main(Expr/IVar([]), x)
  (ilr, zeros, prs) = il_eval(convert_il(cmp))
  mx = remove_refinement_wrappers(cap_main(initial_input(prs), x))
  (r, sm) = sz_eval(mx, maxs, zeros)
  (kind, v) = fold_aborted(r)
  return (kind, expr_nodes(r), sm)
