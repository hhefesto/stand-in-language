{-# LANGUAGE LambdaCase          #-}
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
    -- a statically-known unary-nat chain P^n(Z) is emitted directly as TV/N(n)
    -- instead of n nested mkP calls that only collapse to the same value at
    -- runtime (each runtime collapse costs ~n interactions; large literals
    -- like the church constants in gate arms were ~122 mkP deep).
    PairB a b
      | Just n <- compiledNatDepth (PairB a b) ->
          (showString "TV/N(" . shows n . showString ")", st)
    PairB a b ->
      let (fa, st1) = go a st
          (fb, st2) = go b st1
      -- mkP normalizes a clean unary-nat chain P(nat|Z, Z) into an N leaf
      in (showString "mkP(" . fa . showString ", " . fb . showString ")", st2)
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
               . fr . showString "\n    case TV/N:\n      return "
               . fr . showString "\n    case TV/A:\n      return sv0\n    case TV/F:\n      return TV/A(TV/Z)\n\n"
          st4 = EmitState (emitGateDefs st3 . gdef) (emitGateIdx st3 + 1)
      in (gname . showString "(env)", st4)
    -- appB let/application `SetEnv(SetEnv(Pair(twiddle, Pair(i, c))))`: force
    -- the bound value i to NF once here, when it carries real computation, so a
    -- body that reads it several times (e.g. tictactoe's newBoard, read by
    -- drawBoard/whoWon/fullBoard) copies realized data instead of recomputing.
    SetEnvB (SetEnvB (PairB tw@(StuckEE (DeferSF _ twbody)) (PairB i c)))
      | isTwiddleBody twbody, worthForcing i ->
          let (ftw, st1) = go tw st
              (fi, st2)  = go i st1
              (fc, st3)  = go c st2
          in ( showString "tvApp(tvApp(mkP(" . ftw . showString ", mkP(tvNF("
             . fi . showString "), " . fc . showString "))))"
             , st3 )
    -- statically known callee: direct call
    SetEnvB (PairB (StuckEE (DeferSF fid _)) e) ->
      let (fe, st1) = go e st
      in (showString "d" . shows (slotOf fid) . showString "(" . fe . showString ")", st1)
    SetEnvB (PairB AbortB e) -> wrap "tvAbort(" e st
    -- a pure church spine SetEnv^k Env (sized-recursion / church-numeral core)
    -- is emitted as a native counted loop instead of k nested tvApp layers:
    -- the count is a free-to-copy u24 and the loop body is shared code, so the
    -- term flows through a dup as one small node, not k unreduced application
    -- layers (the copies-of-copies source). Depth 1 stays inline (no benefit).
    SetEnvB x -> case setEnvSpineDepth expr of
      Just k | k >= 2 ->
        (showString "iter_setenv(" . shows k . showString ", env)", st)
      _ -> wrap "tvApp(" x st
    -- bare Abort/Gate outside their SetEnv shapes are not produced by the
    -- compiler; poison defensively (mirrors bend/emitter.bend)
    AbortB -> (showString "TV/A(TV/Z)", st)
    GateB _ _ -> (showString "TV/A(TV/Z)", st)
    AbortEE (AbortedF v) -> (showString "TV/A(" . ceBasic v . showString ")", st)
    _ -> error "HvmBackend.ce: unexpected CompiledExpr constructor"
  wrap prefix x st =
    let (fx, st1) = go x st
    in (showString prefix . fx . showString ")", st1)


-- | A pure church spine @SetEnv (SetEnv (... Env))@ of depth k (k >= 1),
-- with NO intervening Pair. This is the shape produced by 'setSizes'
-- (@iterate (StuckEE . SetEnvSF) EnvB !! (n+1)@) for a sized recursion site
-- and by the church-numeral core inside @i2CB@. Anything else is 'Nothing'.
setEnvSpineDepth :: CompiledExpr -> Maybe Int
setEnvSpineDepth = go 0 where
  go :: Int -> CompiledExpr -> Maybe Int
  go k EnvB        = if k == 0 then Nothing else Just k
  go k (SetEnvB x) = go (k + 1) x
  go _ _           = Nothing

-- ---------------------------------------------------------------------------
-- native repeat recognition: ALL telomare recursion (map/foldr/d2c/$k towers)
-- funnels through ONE builder, repeatFunctionS (Telomare.hs:758), whose
-- innermost lambda body (RFBody, below) drives a church numeral through
-- frame rebuilds that re-project (= duplicate, on HVM2) the whole frame per
-- step (~0.5M interactions per map element, measured). One frame step is
-- exactly tvCall(f, x), so we emit a native counted loop instead. The count
-- k is usually NOT visible at the call site: it arrives at runtime as a
-- closure whose CODE is a Defer with body L.R.R.R(SetEnv^k Env) — but the
-- emitter statically knows every defer body, so a generated fid->k table
-- (churchK) recovers k at runtime in O(1).
-- ---------------------------------------------------------------------------

-- | Matches RFBody, the innermost lambda body of any repeatFunctionS copy:
-- @SetEnv (Pair rcode (Pair rf (Pair rf (Pair f' (Pair x fenv)))))@ with
-- rcode/f'/x/fenv the fixed env projections and both rf Defers having the
-- frame-rebuilder body ('isRfBody'). fid-agnostic: the two rf defers carry
-- distinct fids (verified empirically) but identical bodies. The slow
-- fallback reuses the exact original 'ce' emission, so we need no fids here.
isRepeatBody :: CompiledExpr -> Bool
isRepeatBody
  (SetEnvB (PairB
    (LeftB (LeftB (RightB (RightB EnvB))))
    (PairB (StuckEE (DeferSF _ rf1))
      (PairB (StuckEE (DeferSF _ rf2))
        (PairB (LeftB (LeftB (RightB EnvB)))
          (PairB (LeftB EnvB)
                 (RightB (LeftB (RightB EnvB)))))))))
  = isRfBody rf1 && isRfBody rf2
isRepeatBody _ = False

-- | The repeatFunctionS frame rebuilder rf (Telomare.hs:763):
-- @(rf, (rf, (f', (applyF, fenv))))@ re-selected from the incoming frame.
isRfBody :: CompiledExpr -> Bool
isRfBody
  (PairB (LeftB EnvB)
    (PairB (LeftB EnvB)
      (PairB (LeftB (RightB EnvB))
        (PairB (SetEnvB (RightB EnvB))
               (RightB (RightB (RightB EnvB))))))) = True
isRfBody _ = False

-- | A church-numeral code body @L.R.R.R (SetEnv^k Env)@, k >= 0 ($0 is k=0;
-- a sized {t,r,b} site is k=n+1 via setSizes). Any defer with this body
-- behaves as church-k when driven by the repeat machinery, so recognizing by
-- shape (not provenance) is sound.
matchChurchCode :: CompiledExpr -> Maybe Int
matchChurchCode (LeftB (RightB (RightB (RightB spine)))) = go 0 spine
  where
    go :: Int -> CompiledExpr -> Maybe Int
    go k EnvB        = Just k
    go k (SetEnvB x) = go (k + 1) x
    go _ _           = Nothing
matchChurchCode _ = Nothing

-- | Does this defer body match rWrap, the step of a @{t,r,b}@ sized recursion
-- (unsizedRecursionWrapper: @\r i -> if t i then step recur i else b i@)?
-- rWrap is the curried lambda whose CODE flows as the repeated function of the
-- recursion; tagging it routes those recursions to the O(n) 'tvFixApply'
-- driver instead of the church-count tower ('tvRepeat'). Sizing restructures
-- the exact tree (clamS/lamS wrappings), so we detect it robustly as a curried
-- lambda (a @Pair (Defer inner) _@ closure-returning body) that unwraps to the
-- @if@ GateSwitch — the @d >= 1@ guard excludes a bare (non-recursive) @if@.
isRWrapDefer :: CompiledExpr -> Bool
isRWrapDefer = go (0 :: Int) where
  go :: Int -> CompiledExpr -> Bool
  go d _ | d > 8                                   = False
  go d (SetEnvB (PairB (GateB _ _) _))             = d >= 1
  go d (PairB (StuckEE (DeferSF _ inner)) _)       = go (d + 1) inner
  go _ _                                           = False

-- | The 'twiddleB' rearranger body (Possible.hs:477) that appB wraps around a
-- let/application binding.
isTwiddleBody :: CompiledExpr -> Bool
isTwiddleBody
  (PairB (LeftB (RightB EnvB)) (PairB (LeftB EnvB) (RightB (RightB EnvB)))) = True
isTwiddleBody _ = False

-- | Is a bound value worth forcing to NF at its binding site? Only when it
-- carries a real reduction (a non-spine @SetEnvB@ = an application/recursion),
-- so trivial bindings (projections, closures, literals) are not forced.
worthForcing :: CompiledExpr -> Bool
worthForcing = go where
  go :: CompiledExpr -> Bool
  go (SetEnvB _) = True
  go (PairB a b) = go a || go b
  go (LeftB x)   = go x
  go (RightB x)  = go x
  go _           = False

-- | How many times the appB closure body reads its argument (the value at
-- @Left env@), NOT descending into nested Defer scopes (which rebind env).
-- Used to force a let-bound computation only when it is read multiply — the
-- dense-sharing / compounding case (e.g. tictactoe's @newBoard@ read by
-- drawBoard/whoWon/fullBoard) — while leaving single-read bindings alone
-- (forcing those is pure overhead; it regressed non-compounding programs).
argReadCount :: CompiledExpr -> Int
argReadCount = go where
  go :: CompiledExpr -> Int
  go (LeftB EnvB)            = 1
  go (LeftB x)               = go x
  go (RightB x)              = go x
  go (SetEnvB x)             = go x
  go (PairB a b)             = go a + go b
  go (GateB a b)             = go a + go b
  go (StuckEE (DeferSF _ _)) = 0   -- nested scope: its Left env is a different arg
  go _                       = 0

-- | Read count of the argument inside the appB closure (the @c@ of @appB c i@).
closureArgReads :: CompiledExpr -> Int
closureArgReads (StuckEE (DeferSF _ cbody)) = argReadCount cbody
closureArgReads _                           = 0

-- | Depth of a clean unary-nat chain @P^d(Z)@ (d >= 1), else Nothing.
-- d=1 is @P(Z,Z)@; d is @P(chain_{d-1}, Z)@. Matches 'mkP' exactly so a
-- statically-built and a runtime-built copy of the same value take the
-- same match arm everywhere.
basicNatDepth :: BasicExpr -> Maybe Int
basicNatDepth = go (0 :: Int) where
  go k (Fix ZeroSF)                  = if k == 0 then Nothing else Just k
  go k (Fix (PairSF a (Fix ZeroSF))) = go (k + 1) a
  go _ _                             = Nothing

-- | 'basicNatDepth' over 'CompiledExpr' (built from ZeroB/PairB only).
compiledNatDepth :: CompiledExpr -> Maybe Int
compiledNatDepth = go (0 :: Int) where
  go :: Int -> CompiledExpr -> Maybe Int
  go k ZeroB           = if k == 0 then Nothing else Just k
  go k (PairB a ZeroB) = go (k + 1) a
  go _ _               = Nothing

-- basic-only trees (abort payloads)
ceBasic :: BasicExpr -> ShowS
ceBasic e = case basicNatDepth e of
  Just n  -> showString "TV/N(" . shows n . showString ")"
  Nothing -> case e of
    Fix ZeroSF       -> showString "TV/Z"
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
          -- fid slot -> church count k, for defers whose body is L.R.R.R(SetEnv^k Env)
          churchOf :: Map Int Int
          churchOf = Map.fromList
            [ (slot, k)
            | ((_, body), slot) <- zip defers [0 ..]
            , Just k <- [matchChurchCode body] ]
          -- A repeatFunctionS inner-lambda body (RFBody) is emitted as a native
          -- counted loop: force the incoming church code rc, look up its count k
          -- (O(1), churchK), and iterate tvCall k times. If rc is not a church
          -- defer (sentinel), or not a closure, fall back to the exact original
          -- frame emission (fb) / tvApp semantics.
          emitDefer ((_, body), slot) (frags, st)
            | isRepeatBody body =
                let (fb, st') = ce slots body st
                    def = showString "def d" . shows (slot :: Int)
                        . showString "(env: TV) -> TV:\n"
                        . showString "  match rc = tvL(tvL(tvR(tvR(env)))):\n"
                        . showString "    case TV/F:\n"
                        . showString "      k = churchK(rc.fid)\n"
                        . showString "      if k == 16777215:\n"
                        . showString "        return " . fb . showString "\n"
                        . showString "      else:\n"
                        -- route {t,r,b} (rWrap function) to the O(n) fix driver;
                        -- $k / other functions keep the church-count tvRepeat
                        . showString "        match fc = tvL(tvL(tvR(env))):\n"
                        . showString "          case TV/F:\n"
                        . showString "            rw = isRWrap(fc.fid)\n"
                        . showString "            switch rw:\n"
                        . showString "              case 0:\n"
                        . showString "                return tvRepeat(k, tvL(tvR(env)), tvL(env))\n"
                        . showString "              case _:\n"
                        . showString "                return TV/P(TV/F(" . shows (length defers)
                        . showString "), tvL(tvR(env)))\n"
                        . showString "          case TV/Z:\n            return tvRepeat(k, tvL(tvR(env)), tvL(env))\n"
                        . showString "          case TV/P:\n            return tvRepeat(k, tvL(tvR(env)), tvL(env))\n"
                        . showString "          case TV/N:\n            return tvRepeat(k, tvL(tvR(env)), tvL(env))\n"
                        . showString "          case TV/A:\n            return tvRepeat(k, tvL(tvR(env)), tvL(env))\n"
                        . showString "    case TV/A:\n      return TV/A(rc.p)\n"
                        . showString "    case TV/Z:\n      return TV/A(TV/Z)\n"
                        . showString "    case TV/P:\n      return TV/A(TV/Z)\n"
                        . showString "    case TV/N:\n      return TV/A(TV/Z)\n\n"
                in (def . frags, st')
            | otherwise =
                let (fb, st') = ce slots body st
                    def = showString "def d" . shows (slot :: Int)
                        . showString "(env: TV) -> TV:\n  return " . fb . showString "\n\n"
                in (def . frags, st')
          (deferFrags, st1) = foldr emitDefer (id, st0) (zip defers [0 ..])
          (mainFrags, st2) = ce slots sized st1
          nDefers = length defers
          -- reserved dispatch slot for tvFixApply (the {t,r,b} self-recursion)
          fixSlot = nDefers
          dispatchArm slot = showString "    case " . shows (slot :: Int)
                           . showString ":\n      return d" . shows slot . showString "(env)\n"
          dispatch = showString "def tvDispatch(slot: u24, env: TV) -> TV:\n  switch slot:\n"
                   . foldr (\s acc -> dispatchArm s . acc) id [0 .. nDefers - 1]
                   . showString "    case " . shows fixSlot
                   . showString ":\n      return tvFixApply(env)\n"
                   . showString "    case _:\n      return tvId(env)\n\n"
          -- churchK: slot -> k for church-code defers, sentinel 16777215 else.
          -- Contiguous arms (mirrors tvDispatch) so HVM's numeric switch is happy.
          churchKArm slot = showString "    case " . shows (slot :: Int)
                          . showString ":\n      return "
                          . shows (Map.findWithDefault 16777215 slot churchOf)
                          . showString "\n"
          churchK = showString "def churchK(fid: u24) -> u24:\n  switch fid:\n"
                  . foldr (\s acc -> churchKArm s . acc) id [0 .. nDefers - 1]
                  . showString "    case _:\n      return 16777215\n\n"
          -- isRWrap: 1 if the defer's body is a GateSwitch (the shape of a
          -- {t,r,b} recursion step rWrap = `if t i then step recur i else b i`),
          -- else 0. Only rWrap flows as the repeated function of a sized
          -- recursion, so this distinguishes {t,r,b} from an i2CB `$k` tower.
          rwrapSet :: Set.Set Int
          rwrapSet = Set.fromList
            [ slot | ((_, b), slot) <- zip defers [0 ..], isRWrapDefer b ]
          isRWrapArm slot = showString "    case " . shows (slot :: Int)
                          . showString ":\n      return "
                          . shows (if Set.member slot rwrapSet then 1 else 0 :: Int)
                          . showString "\n"
          isRWrap = showString "def isRWrap(fid: u24) -> u24:\n  switch fid:\n"
                  . foldr (\s acc -> isRWrapArm s . acc) id [0 .. nDefers - 1]
                  . showString "    case _:\n      return 0\n\n"
          -- tvFixApply: the O(n) self-referential driver for {t,r,b}. A sized
          -- recursion result is emitted as the closure P(F(fixSlot), rwrap);
          -- applying it to an input reconstructs the SAME fixed-size closure as
          -- `recur` and runs one rWrap step (`if t i then step recur i else
          -- b i`), so the recursion unwinds via its own base case in O(n) with
          -- O(1) per step -- instead of the church count building an O(k)-size
          -- tower at O(k^2) cost. Safe because sizing proved the base fires.
          tvFixApply = showString "def tvFixApply(env: TV) -> TV:\n"
                     . showString "  rwrap = tvR(env)\n"
                     . showString "  return tvCall(tvCall(rwrap, TV/P(TV/F("
                     . shows fixSlot . showString "), rwrap)), tvL(env))\n\n"
          telMain = showString "def tel_main() -> TV:\n  env = TV/Z\n  return "
                   . mainFrags . showString "\n\n"
      in ( showString emittedPrelude
         . deferFrags
         . emitGateDefs st2
         . dispatch
         . churchK
         . isRWrap
         . tvFixApply
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
  , "  N { v: u24 }"
  , ""
  , "# N v is the unary nat chain P(P(..Z..),Z) of depth v (INVARIANT v >= 1;"
  , "# zero is always Z, never N 0). Telomare numbers/short lists are deep pair"
  , "# chains that HVM2 copies node-by-node on every non-affine read; folding a"
  , "# clean chain into a u24 makes that copy free (u24 duplicates for free)."
  , "# Every match/switch over a TV below carries an N arm behaving EXACTLY as"
  , "# the equivalent pair chain would."
  , ""
  , "# smart pair constructor: collapse a clean unary-nat chain to N."
  , "def mkP(a: TV, b: TV) -> TV:"
  , "  match b:"
  , "    case TV/Z:"
  , "      match a:"
  , "        case TV/Z:"
  , "          return TV/N(1)"
  , "        case TV/N:"
  , "          return TV/N(a.v + 1)"
  , "        case TV/P:"
  , "          return TV/P(a, TV/Z)"
  , "        case TV/A:"
  , "          return TV/P(a, TV/Z)"
  , "        case TV/F:"
  , "          return TV/P(a, TV/Z)"
  , "    case TV/P:"
  , "      return TV/P(a, b)"
  , "    case TV/N:"
  , "      return TV/P(a, b)"
  , "    case TV/A:"
  , "      return TV/P(a, b)"
  , "    case TV/F:"
  , "      return TV/P(a, b)"
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
  , "    case TV/N:"
  , "      k = v.v - 1"      -- v >= 1 by invariant; Left of P(nat(v-1),Z) = nat(v-1)
  , "      switch k:"
  , "        case 0:"
  , "          return TV/Z"
  , "        case _:"
  , "          return TV/N(k)"
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
  , "    case TV/N:"
  , "      return TV/Z"       -- Right of P(nat(v-1),Z) is always Z
  , ""
  , "def tvId(v: TV) -> TV:"
  , "  return v"
  , ""
  , "# deep force to normal form (depth-first, results matched so they actually"
  , "# reduce). A computed value bound by a let and read by several consumers is"
  , "# forced ONCE here so the reads duplicate realized data instead of re-running"
  , "# the computation per read (HVM2 recomputes unreduced redexes on duplication)."
  , "def tvNF(v: TV) -> TV:"
  , "  match v:"
  , "    case TV/Z:"
  , "      return TV/Z"
  , "    case TV/N:"
  , "      return TV/N(v.v)"
  , "    case TV/F:"
  , "      return TV/F(v.fid)"
  , "    case TV/A:"
  , "      match fp = tvNF(v.p):"
  , "        case TV/Z:"
  , "          return TV/A(fp)"
  , "        case TV/P:"
  , "          return TV/A(fp)"
  , "        case TV/N:"
  , "          return TV/A(fp)"
  , "        case TV/A:"
  , "          return TV/A(fp)"
  , "        case TV/F:"
  , "          return TV/A(fp)"
  , "    case TV/P:"
  , "      match ff = tvNF(v.f):"
  , "        case TV/Z:"
  , "          return tvNFp(ff, v.s)"
  , "        case TV/P:"
  , "          return tvNFp(ff, v.s)"
  , "        case TV/N:"
  , "          return tvNFp(ff, v.s)"
  , "        case TV/A:"
  , "          return tvNFp(ff, v.s)"
  , "        case TV/F:"
  , "          return tvNFp(ff, v.s)"
  , ""
  , "def tvNFp(ff: TV, s: TV) -> TV:"
  , "  match fs = tvNF(s):"
  , "    case TV/Z:"
  , "      return mkP(ff, fs)"
  , "    case TV/P:"
  , "      return mkP(ff, fs)"
  , "    case TV/N:"
  , "      return mkP(ff, fs)"
  , "    case TV/A:"
  , "      return mkP(ff, fs)"
  , "    case TV/F:"
  , "      return mkP(ff, fs)"
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
  , "    case TV/N:"
  , "      return TV/N(v.v)"   -- a pure nat chain has no A/F inside: identity
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
  , "    case TV/N:"
  , "      return TV/A(TV/N(v.v))"   -- N v is a non-empty pair: A(tvTrunc(N v)) = A(N v)
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
  , "        case TV/N:"
  , "          return TV/A(TV/Z)"    -- a number in function position is an error
  , "    case TV/A:"
  , "      return TV/A(v.p)"
  , "    case TV/Z:"
  , "      return TV/A(TV/Z)"
  , "    case TV/F:"
  , "      return TV/A(TV/Z)"
  , "    case TV/N:"
  , "      return TV/A(TV/Z)"        -- N v = P(nat,Z): its f is a nat, never F"
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
  , "        case TV/N:"
  , "          return TV/A(TV/Z)"
  , "    case TV/A:"
  , "      return TV/A(c.p)"
  , "    case TV/Z:"
  , "      return TV/A(TV/Z)"
  , "    case TV/F:"
  , "      return TV/A(TV/Z)"
  , "    case TV/N:"
  , "      return TV/A(TV/Z)"
  , ""
  , "# native iteration driver: iter_setenv(n, e) == tvApp^n(e). Replaces a"
  , "# textually-nested tvApp spine (a church-numeral / sized-recursion core)"
  , "# so the iteration count is a free-to-copy u24 and the loop body is shared"
  , "# code rather than n duplicated unreduced application layers."
  , "def iter_setenv(n: u24, e: TV) -> TV:"
  , "  switch n:"
  , "    case 0:"
  , "      return e"
  , "    case _:"
  , "      return iter_setenv(n-1, tvApp(e))"
  , ""
  , "# native repeat: tvRepeat(n, f, x) == apply f to x, n times. This is the"
  , "# whole of telomare's ONE recursion primitive (repeatFunctionS): the church"
  , "# spine that drives k frame-rebuilds, each re-projecting the entire frame,"
  , "# is replaced by a counted loop threading only (f, x). One frame step is"
  , "# exactly tvCall(f, x). f is defunctionalized DATA (P(F fid, fenv)) so it"
  , "# duplicates cheaply. Cuts ~0.5M interactions/element to ~10-100/step."
  , "def tvRepeat(n: u24, f: TV, x: TV) -> TV:"
  , "  switch n:"
  , "    case 0:"
  , "      return x"
  , "    case _:"
  , "      return tvRepeat(n - 1, f, tvCall(f, x))"
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
  , "        case TV/N:"
  , "          return (0, 0)"
  , "        case TV/A:"
  , "          return (0, 0)"
  , "        case TV/F:"
  , "          return (0, 0)"
  , "    case TV/N:"
  , "      return (1, acc + v.v)"    -- N v is the nat chain of depth v
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
  , "    case TV/N:"
  , "      return String/Cons(v.v - 1, \"\")"   -- N v = single-char list [nat(v-1)]
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
  , "# `fun` is tel_main()'s value, computed ONCE in main and threaded through"
  , "# the loop: HVM2 re-unfolds nullary global refs at every reference, so"
  , "# calling tel_main() per iteration would recompute the whole tower each"
  , "# turn. Sharing the value is sound because TV is pure data (closures are"
  , "# defunctionalized slot numbers). Mirrors GHC evalLoop's sharing of the"
  , "# evaluated `fun` across funWrap iterations."
  , "def one_iter(fun: TV, inp: TV) -> (String, TV, u24):"
  , "  r = tvCall(fun, inp)"
  , "  match r:"
  , "    case TV/P:"
  , "      disp = tv_b2s(r.f)"
  , "      match nsv0 = r.s:"
  , "        case TV/Z:"
  , "          return (disp, TV/Z, 2)"
  , "        case TV/P:"
  , "          return (disp, TV/P(nsv0.f, nsv0.s), 1)"
  , "        case TV/N:"
  , "          return (disp, TV/N(nsv0.v), 1)"     -- non-Z state: continue"
  , "        case TV/A:"
  , "          return (disp, TV/Z, 0)"
  , "        case TV/F:"
  , "          return (disp, TV/F(nsv0.fid), 1)"
  , "    case TV/N:"
  , "      return (tv_b2s(tvL(TV/N(r.v))), TV/Z, 2)"  -- r = P(nat(v-1),Z): state Z -> halt"
  , "    case TV/A:"
  , "      return (\"aborted\", TV/Z, 0)"
  , "    case TV/Z:"
  , "      return (\"aborted\", TV/Z, 0)"
  , "    case TV/F:"
  , "      return (\"runtime error\", TV/Z, 0)"
  , ""
  , "def loop_go(fun: TV, state: TV, first: u24, ins: List(TV), acc: String) -> String:"
  , "  if first:"
  , "    (disp, ns, ok) = one_iter(fun, TV/Z)"
  , "    return loop_cont(fun, disp, ns, ok, ins, acc)"
  , "  else:"
  , "    match ins:"
  , "      case List/Nil:"
  , "        return acc"
  , "      case List/Cons:"
  , "        (disp, ns, ok) = one_iter(fun, TV/P(ins.head, state))"
  , "        return loop_cont(fun, disp, ns, ok, ins.tail, acc)"
  , ""
  , "def loop_cont(fun: TV, disp: String, ns: TV, ok: u24, rest: List(TV), acc: String) -> String:"
  , "  new_acc = sc(acc, sc(disp, \"\\n\"))"
  , "  switch ok:"
  , "    case 0:"
  , "      return new_acc"
  , "    case 1:"
  , "      match rest:"
  , "        case List/Nil:"
  , "          return new_acc"
  , "        case List/Cons:"
  , "          return loop_go(fun, ns, 0, rest, new_acc)"
  , "    case _:"
  , "      return new_acc"
  , ""
  , "# tel_main() is forced to WHNF and its top constructor REBUILT before"
  , "# entering the loop: loop_go duplicates `fun`, and HVM's lazy runtime"
  , "# refuses to clone a bare unexpanded global reference (@tel_main is the"
  , "# only nullary global that gets duplicated). Rebuilding makes the dup"
  , "# land on a data node on every runtime."
  , "def main() -> String:"
  , "  match f = tel_main():"
  , "    case TV/P:"
  , "      return sc(loop_go(TV/P(f.f, f.s), TV/Z, 1, inputs(), \"\"), \"\")"
  , "    case TV/Z:"
  , "      return sc(loop_go(TV/Z, TV/Z, 1, inputs(), \"\"), \"\")"
  , "    case TV/A:"
  , "      return sc(loop_go(TV/A(f.p), TV/Z, 1, inputs(), \"\"), \"\")"
  , "    case TV/F:"
  , "      return sc(loop_go(TV/F(f.fid), TV/Z, 1, inputs(), \"\"), \"\")"
  , "    case TV/N:"
  , "      return sc(loop_go(TV/N(f.v), TV/Z, 1, inputs(), \"\"), \"\")"
  ]
