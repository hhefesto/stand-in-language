# telomare-bend IR: port of the telomare core IR and evaluator.
#
# Haskell sources being ported (line refs at time of port):
#   src/Telomare.hs        BasicExprF / StuckF / AbortableF / CompiledExprF
#   src/Telomare/Possible.hs
#     transformNoDefer (125), basicStep (109), stuckStep (139),
#     abortStep (423), AbstractRunTime CompiledExpr eval (1176)
#
# Haskell composes these families with typeclasses over `Fix` functors; Bend
# has neither, so the whole family union is ONE `Expr` ADT and the
# `basicStep (stuckStep (abortStep ...))` chain is flattened into `step_expr`.
#
# FunctionIndex encoding: Haskell uses negative indices -1..-9 for defers
# generated during eval/sizing and non-negative ones for user functions.
# u24 has no negatives, so: generated defers take 1..9 (see fid_* below) and
# user-assigned indices start at fid_user_base = 16.
#
# Where Haskell calls `error` (unhandled eval case), we return
# Expr/EvalError{code} — Bend has no exceptions. codes: see step_expr.

# ---------------------------------------------------------------------------
# The Expr ADT: union of every constructor family in the pipeline.
# Families: Basic, Stuck, Abort (evaluator, this file) and the sizing families
# Unsized, Super, Indexed, Deferred (used from M4 on; carried here so a single
# ADT serves the whole pipeline).
#
# Encodings:
#   Aborted.val    — a Basic-only tree (Zero/Pair), like Haskell's BasicExpr.
#   IVar.path      — input-tree position as a BIT PATH from the root
#                    (0 = left, 1 = right). Haskell uses Integer indices
#                    (left = 2n+1, right = 2n+2); refinements like `$127
#                    left x` reach depth 127 (index ~2^128), far beyond u24,
#                    so paths replace numeric indices.
#   EitherP.tag    — Maybe path: [] = Nothing, 1:path = Just path.
#   SizeStage      — in the sizeTermM path every SizeStageF carries a
#                    SINGLETON SizedRecursion (Map.singleton tok (Just n)),
#                    so it is encoded flat as {tok, bound}.
# ---------------------------------------------------------------------------

type Expr:
  # BasicExprF
  Zero
  Pair { fst: Expr, snd: Expr }
  # StuckF
  Env
  SetEnv { inner: Expr }
  Defer { fid: u24, body: Expr }
  Gate { lft: Expr, rgt: Expr }
  PLeft { inner: Expr }
  PRight { inner: Expr }
  # AbortableF
  Abort
  Aborted { val: Expr }
  # UnsizedRecursionF (M4)
  RecursionTest { tok: u24, inner: Expr }
  UnsizedStub { tok: u24, inner: Expr }
  SizeStepStub { tok: u24, num: u24, inner: Expr }
  SizeStage { tok: u24, bound: u24, inner: Expr }
  RefinementWrapper { loc: u24, tc: Expr, chk: Expr }
  # SuperPositionF (M4)
  EitherP { tag: List(u24), lft: Expr, rgt: Expr }
  # IndexedInputF (M4)
  IVar { path: List(u24) }
  AnyE
  # DeferredEvalF (M4)
  Barrier { inner: Expr }
  ManyLefts { num: u24, inner: Expr }
  ManyRights { num: u24, inner: Expr }
  # Haskell `error` equivalent (no exceptions in Bend)
  EvalError { code: u24 }

# Generated-defer indices (Haskell: [-1..-9] in Possible.hs:467).
def fid_twiddle() -> u24:
  return 1
def fid_unsized_e() -> u24:
  return 2
def fid_unsized_t() -> u24:
  return 3
def fid_unsized_a() -> u24:
  return 4
def fid_unsized_rfa() -> u24:
  return 5
def fid_unsized_rfb() -> u24:
  return 6
def fid_unsized_w() -> u24:
  return 7
def fid_remove_refinement_tc() -> u24:
  return 8
def fid_abort() -> u24:
  return 9
# First index available to user functions (parser/resolver-assigned).
def fid_user_base() -> u24:
  return 16

# Eval-error codes.
def err_setenv_shape() -> u24:
  return 1
def err_fill_shape() -> u24:
  return 2
def err_gate_shape() -> u24:
  return 3
def err_left_shape() -> u24:
  return 4
def err_right_shape() -> u24:
  return 5
def err_bare_env() -> u24:
  return 6
def err_unhandled() -> u24:
  return 7

# ---------------------------------------------------------------------------
# The evaluator.
#
# Haskell (Possible.hs):
#   eval = transformNoDefer step
#     where step = basicStep (stuckStep (abortStep unhandledError))
#   transformNoDefer f = c where
#     c  = f . c' . project
#     c' = \case s@(StuckFW (DeferSF _ _)) -> s
#                x                         -> fmap c x
#
# I.e. bottom-up: evaluate all children first (but never descend into a
# Defer body), then apply the step chain to the node. Function application
# (FillFunction = SetEnv (Pair (Defer _ body) env)) re-enters the same walk
# on `body` with Env nodes replaced by `env` (stuckStep's replaceEnv).
# ---------------------------------------------------------------------------

# transformNoDefer step
def eval_expr(e: Expr) -> Expr:
  match e:
    case Expr/Defer:
      # never descend into a defer body; a Defer is a stuck value
      return Expr/Defer(e.fid, e.body)
    case Expr/Zero:
      return Expr/Zero
    case Expr/Env:
      # bare Env outside any function body: Haskell errors
      return Expr/EvalError(err_bare_env())
    case Expr/Pair:
      return Expr/Pair(eval_expr(e.fst), eval_expr(e.snd))
    case Expr/SetEnv:
      return step_setenv(eval_expr(e.inner))
    case Expr/Gate:
      # LAZY branches: Haskell's transformNoDefer evaluates children as
      # thunks that the GateSwitch discards unforced. Strictly evaluating
      # both branches makes sized recursion towers (built with the strict
      # iteB_) exponential. Branches stay code until the switch picks one.
      return Expr/Gate(e.lft, e.rgt)
    case Expr/PLeft:
      return step_pleft(eval_expr(e.inner))
    case Expr/PRight:
      return step_pright(eval_expr(e.inner))
    case Expr/Abort:
      return Expr/Abort
    case Expr/Aborted:
      # payload is data, not code (Haskell: AbortedF BasicExpr, not in functor)
      return Expr/Aborted(e.val)
    case Expr/RecursionTest:
      return step_expr(Expr/RecursionTest(e.tok, eval_expr(e.inner)))
    case Expr/UnsizedStub:
      return step_expr(Expr/UnsizedStub(e.tok, eval_expr(e.inner)))
    case Expr/SizeStepStub:
      return step_expr(Expr/SizeStepStub(e.tok, e.num, eval_expr(e.inner)))
    case Expr/SizeStage:
      return step_expr(Expr/SizeStage(e.tok, e.bound, eval_expr(e.inner)))
    case Expr/RefinementWrapper:
      return step_expr(Expr/RefinementWrapper(e.loc, eval_expr(e.tc), eval_expr(e.chk)))
    case Expr/EitherP:
      return step_expr(Expr/EitherP(e.tag, eval_expr(e.lft), eval_expr(e.rgt)))
    case Expr/IVar:
      return Expr/IVar(e.path)
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      return step_expr(Expr/Barrier(eval_expr(e.inner)))
    case Expr/ManyLefts:
      return step_expr(Expr/ManyLefts(e.num, eval_expr(e.inner)))
    case Expr/ManyRights:
      return step_expr(Expr/ManyRights(e.num, eval_expr(e.inner)))
    case Expr/EvalError:
      return Expr/EvalError(e.code)

# transformNoDefer (step . replaceEnv) on a defer body: same walk, but Env
# nodes are replaced by `env` (which is already an evaluated value).
def eval_body(d: Expr, env: Expr) -> Expr:
  match d:
    case Expr/Defer:
      return Expr/Defer(d.fid, d.body)
    case Expr/Env:
      return env
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return Expr/Pair(eval_body(d.fst, env), eval_body(d.snd, env))
    case Expr/SetEnv:
      return step_setenv(eval_body(d.inner, env))
    case Expr/Gate:
      # substitute the env into the branches WITHOUT evaluating them
      # (lazy gate branches; see eval_expr note)
      return Expr/Gate(subst_env(d.lft, env), subst_env(d.rgt, env))
    case Expr/PLeft:
      return step_pleft(eval_body(d.inner, env))
    case Expr/PRight:
      return step_pright(eval_body(d.inner, env))
    case Expr/Abort:
      return Expr/Abort
    case Expr/Aborted:
      return Expr/Aborted(d.val)
    case Expr/RecursionTest:
      return step_expr(Expr/RecursionTest(d.tok, eval_body(d.inner, env)))
    case Expr/UnsizedStub:
      return step_expr(Expr/UnsizedStub(d.tok, eval_body(d.inner, env)))
    case Expr/SizeStepStub:
      return step_expr(Expr/SizeStepStub(d.tok, d.num, eval_body(d.inner, env)))
    case Expr/SizeStage:
      return step_expr(Expr/SizeStage(d.tok, d.bound, eval_body(d.inner, env)))
    case Expr/RefinementWrapper:
      return step_expr(Expr/RefinementWrapper(d.loc, eval_body(d.tc, env), eval_body(d.chk, env)))
    case Expr/EitherP:
      return step_expr(Expr/EitherP(d.tag, eval_body(d.lft, env), eval_body(d.rgt, env)))
    case Expr/IVar:
      return Expr/IVar(d.path)
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      return step_expr(Expr/Barrier(eval_body(d.inner, env)))
    case Expr/ManyLefts:
      return step_expr(Expr/ManyLefts(d.num, eval_body(d.inner, env)))
    case Expr/ManyRights:
      return step_expr(Expr/ManyRights(d.num, eval_body(d.inner, env)))
    case Expr/EvalError:
      return Expr/EvalError(d.code)

# Structural environment substitution WITHOUT evaluation: replaces Env
# nodes by `env`, skips Defer bodies (their Envs bind at application).
# Used for lazy Gate branches inside defer bodies.
def subst_env(d: Expr, env: Expr) -> Expr:
  match d:
    case Expr/Env:
      return env
    case Expr/Defer:
      return Expr/Defer(d.fid, d.body)
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return Expr/Pair(subst_env(d.fst, env), subst_env(d.snd, env))
    case Expr/SetEnv:
      return Expr/SetEnv(subst_env(d.inner, env))
    case Expr/Gate:
      return Expr/Gate(subst_env(d.lft, env), subst_env(d.rgt, env))
    case Expr/PLeft:
      return Expr/PLeft(subst_env(d.inner, env))
    case Expr/PRight:
      return Expr/PRight(subst_env(d.inner, env))
    case Expr/Abort:
      return Expr/Abort
    case Expr/Aborted:
      return Expr/Aborted(d.val)
    case Expr/RecursionTest:
      return Expr/RecursionTest(d.tok, subst_env(d.inner, env))
    case Expr/UnsizedStub:
      return Expr/UnsizedStub(d.tok, subst_env(d.inner, env))
    case Expr/SizeStepStub:
      return Expr/SizeStepStub(d.tok, d.num, subst_env(d.inner, env))
    case Expr/SizeStage:
      return Expr/SizeStage(d.tok, d.bound, subst_env(d.inner, env))
    case Expr/RefinementWrapper:
      return Expr/RefinementWrapper(d.loc, subst_env(d.tc, env), subst_env(d.chk, env))
    case Expr/EitherP:
      return Expr/EitherP(d.tag, subst_env(d.lft, env), subst_env(d.rgt, env))
    case Expr/IVar:
      return Expr/IVar(d.path)
    case Expr/AnyE:
      return Expr/AnyE
    case Expr/Barrier:
      return Expr/Barrier(subst_env(d.inner, env))
    case Expr/ManyLefts:
      return Expr/ManyLefts(d.num, subst_env(d.inner, env))
    case Expr/ManyRights:
      return Expr/ManyRights(d.num, subst_env(d.inner, env))
    case Expr/EvalError:
      return Expr/EvalError(d.code)

# The flattened basicStep (stuckStep (abortStep unhandled)) chain.
# Children of `e` are already evaluated when this is called.
def step_expr(e: Expr) -> Expr:
  match e:
    # basicStep: stuck values
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return Expr/Pair(e.fst, e.snd)
    # stuckStep + abortStep dispatch on SetEnv
    case Expr/SetEnv:
      return step_setenv(e.inner)
    case Expr/PLeft:
      return step_pleft(e.inner)
    case Expr/PRight:
      return step_pright(e.inner)
    # stuck values
    case Expr/Defer:
      return Expr/Defer(e.fid, e.body)
    case Expr/Gate:
      return Expr/Gate(e.lft, e.rgt)
    case Expr/Abort:
      return Expr/Abort
    case Expr/Aborted:
      return Expr/Aborted(e.val)
    case Expr/EvalError:
      return Expr/EvalError(e.code)
    case _:
      return Expr/EvalError(err_unhandled())

# SetEnv i — i is evaluated. Handles (in Haskell priority order):
#   abortStep:  SetEnv (Aborted)                    -> Aborted
#               FillFunction (Aborted) _            -> Aborted
#               GateSwitch _ _ (Aborted)            -> Aborted
#               FillFunction Abort (Aborted)        -> Aborted
#               FillFunction Abort Zero             -> Defer fid_abort Env
#               FillFunction Abort (Pair ...)       -> Aborted (truncated)
#   stuckStep:  FillFunction (Defer _ body) env     -> eval_body body env
#               GateSwitch l r Zero                 -> l
#               GateSwitch l r (Pair _ _)           -> r
def step_setenv(i: Expr) -> Expr:
  match i:
    case Expr/Aborted:
      return Expr/Aborted(i.val)
    case Expr/Pair:
      f = i.fst
      en = i.snd
      match f:
        case Expr/Defer:
          match en:
            case Expr/Aborted:
              # FillFunction _ (Aborted) is not explicitly in Haskell's chain,
              # but an aborted env can only arise via SetEnv/Left/Right which
              # already propagate; keep the function-application behavior.
              return eval_body(f.body, Expr/Aborted(en.val))
            case _:
              return eval_body(f.body, en)
        case Expr/Gate:
          match en:
            case Expr/Zero:
              return eval_expr(f.lft)
            case Expr/Pair:
              return eval_expr(f.rgt)
            case Expr/Aborted:
              return Expr/Aborted(en.val)
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
            case _:
              return Expr/EvalError(err_fill_shape())
        case _:
          return Expr/EvalError(err_fill_shape())
    case _:
      return Expr/EvalError(err_setenv_shape())

def step_pleft(i: Expr) -> Expr:
  match i:
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return i.fst
    case Expr/Aborted:
      return Expr/Aborted(i.val)
    case _:
      return Expr/EvalError(err_left_shape())

def step_pright(i: Expr) -> Expr:
  match i:
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return i.snd
    case Expr/Aborted:
      return Expr/Aborted(i.val)
    case _:
      return Expr/EvalError(err_right_shape())

# abortStep's payload truncation (cata truncF): keep the Zero/Pair skeleton,
# anything else becomes Zero.
def truncate_basic(e: Expr) -> Expr:
  match e:
    case Expr/Zero:
      return Expr/Zero
    case Expr/Pair:
      return Expr/Pair(truncate_basic(e.fst), truncate_basic(e.snd))
    case _:
      return Expr/Zero

# ---------------------------------------------------------------------------
# IR builders (ports of the combinators in Telomare.hs / Possible.hs).
# ---------------------------------------------------------------------------

# varB n = LeftB (RightB^n EnvB)   — de Bruijn variable access
def var_b(n: u24) -> Expr:
  return Expr/PLeft(var_b_go(n))

def var_b_go(n: u24) -> Expr:
  switch n:
    case 0:
      return Expr/Env
    case _:
      return Expr/PRight(var_b_go(n - 1))

# i2B — church-numeral-ish nat as nested pairs: n = Pair (n-1) Zero
def i2b(n: u24) -> Expr:
  switch n:
    case 0:
      return Expr/Zero
    case _:
      return Expr/Pair(i2b(n - 1), Expr/Zero)

# b2i — inverse of i2b; Option encoded as (found: u24, value: u24)
def b2i_go(e: Expr, acc: u24) -> (u24, u24):
  match e:
    case Expr/Zero:
      return (1, acc)
    case Expr/Pair:
      match e.snd:
        case Expr/Zero:
          return b2i_go(e.fst, acc + 1)
        case _:
          return (0, 0)
    case _:
      return (0, 0)

def b2i(e: Expr) -> (u24, u24):
  return b2i_go(e, 0)

# iteB_ i t e = SetEnv (Pair (Gate e t) i)   — strict if/then/else
def ite_b(i: Expr, t: Expr, e: Expr) -> Expr:
  return Expr/SetEnv(Expr/Pair(Expr/Gate(e, t), i))

def defer_b(fid: u24, x: Expr) -> Expr:
  return Expr/Defer(fid, x)

# lamB n x = Pair (Defer n x) Env
def lam_b(fid: u24, x: Expr) -> Expr:
  return Expr/Pair(Expr/Defer(fid, x), Expr/Env)

# twiddleB — argument-threading defer used by appB
def twiddle_b() -> Expr:
  return Expr/Defer(fid_twiddle(),
    Expr/Pair(Expr/PLeft(Expr/PRight(Expr/Env)),
              Expr/Pair(Expr/PLeft(Expr/Env),
                        Expr/PRight(Expr/PRight(Expr/Env)))))

# appB c i = SetEnv (SetEnv (Pair twiddleB (Pair i c)))
def app_b(c: Expr, i: Expr) -> Expr:
  return Expr/SetEnv(Expr/SetEnv(Expr/Pair(twiddle_b(), Expr/Pair(i, c))))

# ---------------------------------------------------------------------------
# Structural equality (Haskell Eq1: Defer compares only the function index).
# ---------------------------------------------------------------------------

def expr_eq(a: Expr, b: Expr) -> u24:
  match a:
    case Expr/Zero:
      match b:
        case Expr/Zero:
          return 1
        case _:
          return 0
    case Expr/Pair:
      match b:
        case Expr/Pair:
          return expr_eq(a.fst, b.fst) & expr_eq(a.snd, b.snd)
        case _:
          return 0
    case Expr/Env:
      match b:
        case Expr/Env:
          return 1
        case _:
          return 0
    case Expr/SetEnv:
      match b:
        case Expr/SetEnv:
          return expr_eq(a.inner, b.inner)
        case _:
          return 0
    case Expr/Defer:
      match b:
        case Expr/Defer:
          return a.fid == b.fid
        case _:
          return 0
    case Expr/Gate:
      match b:
        case Expr/Gate:
          return expr_eq(a.lft, b.lft) & expr_eq(a.rgt, b.rgt)
        case _:
          return 0
    case Expr/PLeft:
      match b:
        case Expr/PLeft:
          return expr_eq(a.inner, b.inner)
        case _:
          return 0
    case Expr/PRight:
      match b:
        case Expr/PRight:
          return expr_eq(a.inner, b.inner)
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
    case Expr/EvalError:
      match b:
        case Expr/EvalError:
          return a.code == b.code
        case _:
          return 0
    case _:
      return 0

# ---------------------------------------------------------------------------
# Debug rendering
# ---------------------------------------------------------------------------

def show_expr(e: Expr) -> String:
  match e:
    case Expr/Zero:
      return "Z"
    case Expr/Pair:
      return String/Cons(40, show_expr_pair(e.fst, e.snd))
    case Expr/Env:
      return "E"
    case Expr/SetEnv:
      return show_wrap("SetEnv", show_expr(e.inner))
    case Expr/Defer:
      return show_wrap("Defer", show_u24_ir(e.fid))
    case Expr/Gate:
      return show_wrap("Gate", show_expr_pair2(e.lft, e.rgt))
    case Expr/PLeft:
      return show_wrap("L", show_expr(e.inner))
    case Expr/PRight:
      return show_wrap("R", show_expr(e.inner))
    case Expr/Abort:
      return "Abort"
    case Expr/Aborted:
      return show_wrap("Aborted", show_expr(e.val))
    case Expr/EvalError:
      return show_wrap("ERROR", show_u24_ir(e.code))
    case _:
      return "<sizing>"

def show_expr_pair(a: Expr, b: Expr) -> String:
  return str_concat_ir(show_expr(a), String/Cons(44, str_concat_ir(show_expr(b), ")")))

def show_expr_pair2(a: Expr, b: Expr) -> String:
  return str_concat_ir(show_expr(a), String/Cons(44, show_expr(b)))

def show_wrap(name: String, body: String) -> String:
  return str_concat_ir(name, String/Cons(40, str_concat_ir(body, ")")))

def str_concat_ir(a: String, b: String) -> String:
  match a:
    case String/Nil:
      return b
    case String/Cons:
      return String/Cons(a.head, str_concat_ir(a.tail, b))

def show_u24_ir_go(n: u24, acc: String) -> String:
  switch (n < 10):
    case 0:
      return show_u24_ir_go(n / 10, String/Cons(48 + (n % 10), acc))
    case _:
      return String/Cons(48 + n, acc)

def show_u24_ir(n: u24) -> String:
  return show_u24_ir_go(n, String/Nil)
