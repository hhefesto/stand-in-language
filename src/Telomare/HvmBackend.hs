{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | HVM2 emission backend: compile a sized 'CompiledExpr' (the output of
-- Possible.hs recursion sizing) into a standalone Bend program executed
-- natively by HVM2. This is the Haskell twin of @bend/emitter.bend@ and
-- produces the same generated-program contract (see bend/PORT.md):
--
--   * value encoding @type TV: Z | P{f,s} | F{fid: u24} | A{p}@ — closures
--     are DEFUNCTIONALIZED to plain slot numbers dispatched by a generated
--     @tvDispatch@ switch, because HVM2 cannot soundly duplicate non-affine
--     functions flowing through data;
--   * one @def d\<slot\>(env: TV)@ per unique Defer 'FunctionIndex';
--   * @SetEnv (Pair (Gate l r) s)@ (the only gate shape the compiler
--     emits) becomes a lifted @g\<n\>(env)@ whose body is a native @match@ —
--     HVM evaluates only the selected arm, supplying the demand-driven
--     laziness GHC gives the tree-walking evaluator;
--   * the program is input-independent: the driver appends a per-run
--     @def inputs() -> List(TV)@ and the transcript is @main()@'s pure
--     String result (decoded from the HVM Result dump by the shell driver).
module Telomare.HvmBackend where

import Data.Fix (Fix (..))
import Data.Functor.Foldable (project)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Telomare

validateExpr :: CompiledExpr -> Either String ()
validateExpr = go where
  go = \case
    ZeroB -> pure ()
    EnvB -> pure ()
    PairB a b -> go a *> go b
    LeftB x -> go x
    RightB x -> go x
    StuckEE (DeferSF _ body) -> go body
    SetEnvB (PairB (GateB l r) s) -> go l *> go r *> go s
    SetEnvB x -> go x
    AbortB -> pure ()
    GateB _ _ -> Left "Gate appeared outside SetEnv(Pair(Gate left right, scrutinee))"
    AbortEE (AbortedF _) -> pure ()
    _ -> Left "sized expression contains a constructor unsupported by the HVM backend"

-- ---------------------------------------------------------------------------
-- defer collection: unique fids in discovery order (bodies are identical
-- per fid by construction; Eq1 compares Defers by fid only)
-- ---------------------------------------------------------------------------

collectDefers :: CompiledExpr -> [(FunctionIndex, CompiledExpr)]
collectDefers top = reverse . snd $ go (Set.empty, []) top where
  go :: (Set.Set FunctionIndex, [(FunctionIndex, CompiledExpr)])
     -> CompiledExpr
     -> (Set.Set FunctionIndex, [(FunctionIndex, CompiledExpr)])
  go st@(seen, acc) = \case
    StuckEE (DeferSF fid body)
      | Set.member fid seen -> st
      | otherwise -> go (Set.insert fid seen, (fid, body) : acc) body
    e -> foldl' go st (project e)

slotMap :: [(FunctionIndex, CompiledExpr)] -> Map FunctionIndex Int
slotMap defers = Map.fromList $ zip (fst <$> defers) [0 ..]

-- ---------------------------------------------------------------------------
-- expression compilation (ShowS to keep appends O(1); gate switches are
-- lifted to numbered top-level defs, accumulated left-to-right)
-- ---------------------------------------------------------------------------

data EmitState = EmitState
  { emitGateDefs :: ShowS -- lifted g<n> definitions, in assignment order
  , emitGateIdx  :: Int
  }

ce :: Map FunctionIndex Int -> CompiledExpr -> EmitState -> (ShowS, EmitState)
ce slots = go where
  slotOf fid = case Map.lookup fid slots of
    Just s -> s
    _      -> error $ "HvmBackend.ce: uncollected FunctionIndex " <> show fid
  go :: CompiledExpr -> EmitState -> (ShowS, EmitState)
  go expr st = case expr of
    ZeroB -> (showString "TV/Z", st)
    EnvB -> (showString "env", st)
    PairB a b ->
      let (fa, st1) = go a st
          (fb, st2) = go b st1
      in (showString "TV/P(" . fa . showString ", " . fb . showString ")", st2)
    LeftB x -> wrap "tvL(" x st
    RightB x -> wrap "tvR(" x st
    StuckEE (DeferSF fid _) ->
      (showString "TV/F(" . shows (slotOf fid) . showString ")", st)
    -- GateSwitch: lift to g<n>(env) with a lazy native match
    SetEnvB (PairB (GateB l r) s) ->
      let (fs, st1) = go s st
          (fl, st2) = go l st1
          (fr, st3) = go r st2
          gname = showString "g" . shows (emitGateIdx st3)
          gdef = showString "def " . gname . showString "(env: TV) -> TV:\n  match sv0 = "
               . fs . showString ":\n    case TV/Z:\n      return "
               . fl . showString "\n    case TV/P:\n      return "
               . fr . showString "\n    case TV/A:\n      return sv0\n    case TV/F:\n      return TV/A(TV/Z)\n\n"
          st4 = EmitState (emitGateDefs st3 . gdef) (emitGateIdx st3 + 1)
      in (gname . showString "(env)", st4)
    -- statically known callee: direct call
    SetEnvB (PairB (StuckEE (DeferSF fid _)) e) ->
      let (fe, st1) = go e st
      in (showString "d" . shows (slotOf fid) . showString "(" . fe . showString ")", st1)
    SetEnvB (PairB AbortB e) -> wrap "tvAbort(" e st
    SetEnvB x -> wrap "tvApp(" x st
    -- bare Abort/Gate outside their SetEnv shapes are not produced by the
    -- compiler; poison defensively (mirrors bend/emitter.bend)
    AbortB -> (showString "TV/A(TV/Z)", st)
    GateB _ _ -> (showString "TV/A(TV/Z)", st)
    AbortEE (AbortedF v) -> (showString "TV/A(" . ceBasic v . showString ")", st)
    _ -> error "HvmBackend.ce: unexpected CompiledExpr constructor"
  wrap prefix x st =
    let (fx, st1) = go x st
    in (showString prefix . fx . showString ")", st1)

-- basic-only trees (abort payloads)
ceBasic :: BasicExpr -> ShowS
ceBasic = \case
  Fix ZeroSF -> showString "TV/Z"
  Fix (PairSF a b) -> showString "TV/P(" . ceBasic a . showString ", " . ceBasic b . showString ")"

-- ---------------------------------------------------------------------------
-- top level
-- ---------------------------------------------------------------------------

-- | Sized expression -> complete generated Bend program (sans @inputs()@,
-- which the driver appends per run).
emitProgram :: CompiledExpr -> String
emitProgram sized =
  case validateExpr sized of
    Left err -> error $ "HvmBackend.emitProgram: " <> err
    Right () ->
      let defers = collectDefers sized
      slots = slotMap defers
      st0 = EmitState id 0
      emitDefer ((_, body), slot) (frags, st) =
        let (fb, st') = ce slots body st
            def = showString "def d" . shows (slot :: Int)
                . showString "(env: TV) -> TV:\n  return " . fb . showString "\n\n"
        in (def . frags, st')
      (deferFrags, st1) = foldr emitDefer (id, st0) (zip defers [0 ..])
      (mainFrags, st2) = ce slots sized st1
      dispatchArm slot = showString "    case " . shows (slot :: Int)
                       . showString ":\n      return d" . shows slot . showString "(env)\n"
      dispatch = showString "def tvDispatch(slot: u24, env: TV) -> TV:\n  switch slot:\n"
               . foldr (\s acc -> dispatchArm s . acc) id [0 .. length defers - 1]
               . showString "    case _:\n      return tvId(env)\n\n"
      telMain = showString "def tel_main() -> TV:\n  env = TV/Z\n  return "
               . mainFrags . showString "\n\n"
      in ( showString emittedPrelude
         . deferFrags
         . emitGateDefs st2
         . dispatch
         . telMain
         . showString emittedDriver
         ) ""

-- ---------------------------------------------------------------------------
-- static text: prelude + driver of every generated program (identical to
-- the text emitted by bend/emitter.bend, which is verified against
-- `bend gen-hvm | hvm run-c`)
-- ---------------------------------------------------------------------------

emittedPrelude :: String
emittedPrelude = unlines
  [ "# generated by telomare --emit-hvm (src/Telomare/HvmBackend.hs) -- do not edit"
  , ""
  , "type TV:"
  , "  Z"
  , "  P { f: TV, s: TV }"
  , "  F { fid: u24 }"
  , "  A { p: TV }"
  , ""
  , "def tvL(v: TV) -> TV:"
  , "  match v:"
  , "    case TV/Z:"
  , "      return TV/Z"
  , "    case TV/P:"
  , "      return v.f"
  , "    case TV/A:"
  , "      return TV/A(v.p)"
  , "    case TV/F:"
  , "      return TV/A(TV/Z)"
  , ""
  , "def tvR(v: TV) -> TV:"
  , "  match v:"
  , "    case TV/Z:"
  , "      return TV/Z"
  , "    case TV/P:"
  , "      return v.s"
  , "    case TV/A:"
  , "      return TV/A(v.p)"
  , "    case TV/F:"
  , "      return TV/A(TV/Z)"
  , ""
  , "def tvId(v: TV) -> TV:"
  , "  return v"
  , ""
  , "# truncate to the Zero/Pair skeleton (abortStep payload rule)"
  , "def tvTrunc(v: TV) -> TV:"
  , "  match v:"
  , "    case TV/Z:"
  , "      return TV/Z"
  , "    case TV/P:"
  , "      return TV/P(tvTrunc(v.f), tvTrunc(v.s))"
  , "    case TV/A:"
  , "      return TV/Z"
  , "    case TV/F:"
  , "      return TV/Z"
  , ""
  , "# FillFunction Abort x; slot 16777215 is out of dispatch range -> tvId"
  , "def tvAbort(v: TV) -> TV:"
  , "  match v:"
  , "    case TV/Z:"
  , "      return TV/F(16777215)"
  , "    case TV/P:"
  , "      return TV/A(tvTrunc(TV/P(v.f, v.s)))"
  , "    case TV/A:"
  , "      return TV/A(v.p)"
  , "    case TV/F:"
  , "      return TV/A(TV/Z)"
  , ""
  , "# generic application: SetEnv on an evaluated pair (defunctionalized)"
  , "def tvApp(v: TV) -> TV:"
  , "  match v:"
  , "    case TV/P:"
  , "      f = v.f"
  , "      match f:"
  , "        case TV/F:"
  , "          return tvDispatch(f.fid, v.s)"
  , "        case TV/A:"
  , "          return TV/A(f.p)"
  , "        case TV/Z:"
  , "          return TV/A(TV/Z)"
  , "        case TV/P:"
  , "          return TV/A(TV/Z)"
  , "    case TV/A:"
  , "      return TV/A(v.p)"
  , "    case TV/Z:"
  , "      return TV/A(TV/Z)"
  , "    case TV/F:"
  , "      return TV/A(TV/Z)"
  , ""
  , "# closure call with telomare's appB convention: the callee is a closure"
  , "# Pair(code, captured); the body runs with env = (arg, captured)."
  , "def tvCall(c: TV, i: TV) -> TV:"
  , "  match c:"
  , "    case TV/P:"
  , "      code = c.f"
  , "      match code:"
  , "        case TV/F:"
  , "          return tvDispatch(code.fid, TV/P(i, c.s))"
  , "        case TV/A:"
  , "          return TV/A(code.p)"
  , "        case TV/Z:"
  , "          return TV/A(TV/Z)"
  , "        case TV/P:"
  , "          return TV/A(TV/Z)"
  , "    case TV/A:"
  , "      return TV/A(c.p)"
  , "    case TV/Z:"
  , "      return TV/A(TV/Z)"
  , "    case TV/F:"
  , "      return TV/A(TV/Z)"
  , ""
  ]

emittedDriver :: String
emittedDriver = unlines
  [ "# ---- driver ----"
  , ""
  , "def tv_b2i(v: TV, acc: u24) -> (u24, u24):"
  , "  match v:"
  , "    case TV/Z:"
  , "      return (1, acc)"
  , "    case TV/P:"
  , "      match sv0 = v.s:"
  , "        case TV/Z:"
  , "          return tv_b2i(v.f, acc + 1)"
  , "        case TV/P:"
  , "          return (0, 0)"
  , "        case TV/A:"
  , "          return (0, 0)"
  , "        case TV/F:"
  , "          return (0, 0)"
  , "    case TV/A:"
  , "      return (0, 0)"
  , "    case TV/F:"
  , "      return (0, 0)"
  , ""
  , "def tv_b2s(v: TV) -> String:"
  , "  match v:"
  , "    case TV/Z:"
  , "      return \"\""
  , "    case TV/P:"
  , "      (ok, c) = tv_b2i(v.f, 0)"
  , "      if ok:"
  , "        return String/Cons(c, tv_b2s(v.s))"
  , "      else:"
  , "        return \"\""
  , "    case TV/A:"
  , "      return \"\""
  , "    case TV/F:"
  , "      return \"\""
  , ""
  , "def sc(a: String, b: String) -> String:"
  , "  match a:"
  , "    case String/Nil:"
  , "      return b"
  , "    case String/Cons:"
  , "      return String/Cons(a.head, sc(a.tail, b))"
  , ""
  , "def one_iter(inp: TV) -> (String, TV, u24):"
  , "  r = tvCall(tel_main(), inp)"
  , "  match r:"
  , "    case TV/P:"
  , "      disp = tv_b2s(r.f)"
  , "      match nsv0 = r.s:"
  , "        case TV/Z:"
  , "          return (disp, TV/Z, 2)"
  , "        case TV/P:"
  , "          return (disp, TV/P(nsv0.f, nsv0.s), 1)"
  , "        case TV/A:"
  , "          return (disp, TV/Z, 0)"
  , "        case TV/F:"
  , "          return (disp, TV/F(nsv0.fid), 1)"
  , "    case TV/A:"
  , "      return (\"aborted\", TV/Z, 0)"
  , "    case TV/Z:"
  , "      return (\"aborted\", TV/Z, 0)"
  , "    case TV/F:"
  , "      return (\"runtime error\", TV/Z, 0)"
  , ""
  , "def loop_go(state: TV, first: u24, ins: List(TV), acc: String) -> String:"
  , "  if first:"
  , "    (disp, ns, ok) = one_iter(TV/Z)"
  , "    return loop_cont(disp, ns, ok, ins, acc)"
  , "  else:"
  , "    match ins:"
  , "      case List/Nil:"
  , "        return acc"
  , "      case List/Cons:"
  , "        (disp, ns, ok) = one_iter(TV/P(ins.head, state))"
  , "        return loop_cont(disp, ns, ok, ins.tail, acc)"
  , ""
  , "def loop_cont(disp: String, ns: TV, ok: u24, rest: List(TV), acc: String) -> String:"
  , "  new_acc = sc(acc, sc(disp, \"\\n\"))"
  , "  switch ok:"
  , "    case 0:"
  , "      return new_acc"
  , "    case 1:"
  , "      return loop_go(ns, 0, rest, new_acc)"
  , "    case _:"
  , "      return new_acc"
  , ""
  , "def main() -> String:"
  , "  return sc(loop_go(TV/Z, 1, inputs(), \"\"), \"\")"
  ]
