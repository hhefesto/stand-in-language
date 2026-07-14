{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Telomare 2 backend: emit a sized 'CompiledExpr' as a Bend/HVM2 program
-- under the Telomare 2 affine discipline (design/TELOMARE2-DESIGN.md §12,
-- the migration table made executable).
--
-- This is a fork of 'Telomare.HvmBackend' (same value encoding, same
-- defunctionalization, same generated-program contract — the shell driver
-- @bend/run_telomare_hvm.sh@ runs both via @TELOMARE_EMIT_FLAG@) that adds
-- the design's two duplication-discipline rules. The correspondence:
--
--   [@dupS@ — contraction only on boxed values] a let-bound COMPUTED value
--   that its body reads more than once (the appB shape, bound value
--   'worthForcing', 'closureArgReads' >= 2) is normalized ONCE at the
--   binding ('tvNF') so the contraction copies realized data. Reads == 1 is
--   affine — no box, no force. This is the @main.newBoard : !@ site of the
--   levels pass (`telomare --emit-levels`), priced by the design's dup
--   grade instead of recomputed per read (the measured 10^9-interaction
--   blowup of the legacy pipeline, bend/HYBRID_PROGRESS.md).
--
--   [@boxS@/@iterS@ — promotion at the iteration boundary] the repeated
--   step closure of a sized recursion (the @f@ threaded by
--   'Telomare.HvmBackend.isRepeatBody' machinery) crosses INTO the
--   iteration, where it is re-read every unwinding — the design types its
--   captured environment one box level deeper. Operationally: 'tvNF' on the
--   closure once at loop entry, before 'tvRepeat'/@tvFixApply@ start
--   copying it per step. This is the @whoWon.board : !!@ site of the levels
--   pass: a static read-count gate cannot see contraction-via-recursion,
--   the level structure can.
--
-- Everything affine is untouched: no forcing anywhere else, HVM2's lazy dup
-- handles single-use and data-projection sharing as before. 'T2Lazy'
-- disables both rules (pure defunctionalized baseline) for A/B measurement.
--
-- The emitted header carries the static cost certificate: dup (let-force)
-- site count, iteration (box) sites, and the inferred iteration budgets
-- (churchK) — the same numbers design/VALIDATION.md reads as EAL levels.
module Telomare.T2Backend where

import Data.Fix (Fix (..))
import Data.Functor.Foldable (project)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Telomare
import Telomare.HvmBackend (EmitState (..), ceBasic, collectDefers,
                            compiledNatDepth, emittedDriver, emittedPrelude,
                            isRWrapDefer, isRepeatBody, isTwiddleBody,
                            matchChurchCode, setEnvSpineDepth, slotMap,
                            validateExpr, worthForcing)

data T2Mode = T2Eager | T2LetOnly | T2Lazy deriving (Eq, Show)

-- | T2 additions to the shared prelude. tvDF = force to DATA normal form:
-- like tvNF but a pair whose head is code (@P(F fid, cap)@ — the closure
-- shape) is left untouched, captured env unwalked. A box's contents are
-- realized at the box's own binding site; forcing through a closure from
-- the outside would cross a box boundary (and measurably diverges on
-- closure-heavy values: see module header / design/T2-BEND-BACKEND.md).
t2Prelude :: String
t2Prelude = unlines
  [ "# ---- T2 discipline prelude (src/Telomare/T2Backend.hs) ----"
  , ""
  , "# force to data normal form, stopping at closure boundaries"
  , "def tvDF(v: TV) -> TV:"
  , "  match v:"
  , "    case TV/Z:"
  , "      return TV/Z"
  , "    case TV/N:"
  , "      return TV/N(v.v)"
  , "    case TV/F:"
  , "      return TV/F(v.fid)"
  , "    case TV/A:"
  , "      match fp = tvDF(v.p):"
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
  , "      match ff = tvDF(v.f):"
  , "        case TV/F:"
  , "          return TV/P(ff, v.s)"   -- closure: captured env stays boxed
  , "        case TV/Z:"
  , "          return tvDFp(ff, v.s)"
  , "        case TV/P:"
  , "          return tvDFp(ff, v.s)"
  , "        case TV/N:"
  , "          return tvDFp(ff, v.s)"
  , "        case TV/A:"
  , "          return tvDFp(ff, v.s)"
  , ""
  , "def tvDFp(ff: TV, s: TV) -> TV:"
  , "  match fs = tvDF(s):"
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
  ]

letForceOn, iterBoxOn :: T2Mode -> Bool
letForceOn m = m == T2Eager || m == T2LetOnly
iterBoxOn m = m == T2Eager

-- | Scope-aware read count of a let binding. In the appB closure body the
-- binding is @Left env@; every nested let (appB) and every wholesale-capture
-- closure @Pair (Defer b) Env@ rebinds env to @(new, old)@, so the SAME
-- binding is reachable there as @Left (Right^k env)@ one k deeper. The
-- legacy 'closureArgReads' stopped at nested Defer scopes and therefore saw
-- <= 1 read for any binding consumed inside a let CHAIN (e.g. tictactoe's
-- @newBoard@, whose consumers all live in the nested @winner = ...@ scope) —
-- the exact miss bend/HYBRID_PROGRESS.md predicted. Closures with a
-- non-wholesale capture are not followed (reads inside them are missed:
-- undercount, i.e. we may fail to force — never a soundness issue).
deepArgReads :: CompiledExpr -> Int
deepArgReads = go 0 where
  go :: Int -> CompiledExpr -> Int
  go k e | isPath k e = 1
  go k (SetEnvB (SetEnvB (PairB (StuckEE (DeferSF _ twbody)) (PairB i c))))
    | isTwiddleBody twbody
    , StuckEE (DeferSF _ cbody) <- c = go k i + go (k + 1) cbody
  go k (PairB (StuckEE (DeferSF _ b)) EnvB) = go (k + 1) b
  go k (StuckEE (DeferSF _ _)) = 0        -- non-wholesale scope: skip
  go k e = foldl' (\acc x -> acc + go k x) 0 (project e)
  -- Left (Right^k env)
  isPath :: Int -> CompiledExpr -> Bool
  isPath k (LeftB x) = spineR k x where
    spineR :: Int -> CompiledExpr -> Bool
    spineR 0 EnvB       = True
    spineR n (RightB y) = n > 0 && spineR (n - 1) y
    spineR _ _          = False
  isPath _ _ = False

-- | The let-body code of an appB continuation, when statically extractable
-- (bare code or a closure pair; anything else — e.g. a continuation fetched
-- from the environment — is opaque).
letBody :: CompiledExpr -> Maybe CompiledExpr
letBody = \case
  StuckEE (DeferSF _ b)           -> Just b
  PairB (StuckEE (DeferSF _ b)) _ -> Just b
  _                               -> Nothing

-- | Does this appB binding meet the T2 contraction rule? Box (force) a
-- computed binding unless it is PROVABLY affine (statically extractable
-- body reading it <= 1 time). Opaque continuations are boxed conservatively
-- — in EAL terms, contraction must be licensed, so unknown use counts as
-- use-many. The dupS sites of the certificate.
isLetDup :: CompiledExpr -> Bool
isLetDup (SetEnvB (SetEnvB (PairB (StuckEE (DeferSF _ twbody)) (PairB i c)))) =
  isTwiddleBody twbody
  && worthForcing i
  && maybe True (\b -> deepArgReads b >= 2) (letBody c)
isLetDup _ = False

-- | Count T2 contraction sites in one def body, NOT descending into nested
-- Defer bodies (each unique fid is counted from its own 'collectDefers'
-- entry; bodies are identical per fid).
countLetDups :: CompiledExpr -> Int
countLetDups = go where
  go :: CompiledExpr -> Int
  go e@(StuckEE (DeferSF _ _)) = hereCount e -- leaf: body counted elsewhere
  go e = hereCount e + foldl' (\acc x -> acc + go x) 0 (project e)
  hereCount e = if isLetDup e then 1 else 0

-- ---------------------------------------------------------------------------
-- expression compilation: 'Telomare.HvmBackend.ce' with the T2 contraction
-- rule at the appB shape
-- ---------------------------------------------------------------------------

ceT2 :: T2Mode -> Map FunctionIndex Int -> CompiledExpr -> EmitState
     -> (ShowS, EmitState)
ceT2 mode slots = go where
  slotOf fid = case Map.lookup fid slots of
    Just s -> s
    _      -> error $ "T2Backend.ceT2: uncollected FunctionIndex " <> show fid
  go :: CompiledExpr -> EmitState -> (ShowS, EmitState)
  go expr st = case expr of
    ZeroB -> (showString "TV/Z", st)
    EnvB -> (showString "env", st)
    PairB a b
      | Just n <- compiledNatDepth (PairB a b) ->
          (showString "TV/N(" . shows n . showString ")", st)
    PairB a b ->
      let (fa, st1) = go a st
          (fb, st2) = go b st1
      in (showString "mkP(" . fa . showString ", " . fb . showString ")", st2)
    LeftB x -> wrap "tvL(" x st
    RightB x -> wrap "tvR(" x st
    StuckEE (DeferSF fid _) ->
      (showString "TV/F(" . shows (slotOf fid) . showString ")", st)
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
    -- T2 dupS: a let of a computed value contracted by its body is
    -- normalized once at the binding, so the copies are of realized data.
    -- tvDF (NOT tvNF): the force stops at closure boundaries — a closure is
    -- a box, and its captured env is boxed at ITS binding, not transitively
    -- here. Forcing through it would be reduction across a box boundary,
    -- which stratification forbids (and which measurably diverges: the
    -- tvNF variant ground tttSP past a 600 s budget). Affine bindings
    -- (single read) fall through untouched.
    SetEnvB (SetEnvB (PairB tw (PairB i c)))
      | letForceOn mode, isLetDup expr ->
          let (ftw, st1) = go tw st
              (fi, st2)  = go i st1
              (fc, st3)  = go c st2
          in ( showString "tvApp(tvApp(mkP(" . ftw . showString ", mkP(tvDF("
             . fi . showString "), " . fc . showString "))))"
             , st3 )
    SetEnvB (PairB (StuckEE (DeferSF fid _)) e) ->
      let (fe, st1) = go e st
      in (showString "d" . shows (slotOf fid) . showString "(" . fe . showString ")", st1)
    SetEnvB (PairB AbortB e) -> wrap "tvAbort(" e st
    SetEnvB x -> case setEnvSpineDepth expr of
      Just k | k >= 2 ->
        (showString "iter_setenv(" . shows k . showString ", env)", st)
      _ -> wrap "tvApp(" x st
    AbortB -> (showString "TV/A(TV/Z)", st)
    GateB _ _ -> (showString "TV/A(TV/Z)", st)
    AbortEE (AbortedF v) -> (showString "TV/A(" . ceBasic v . showString ")", st)
    _ -> error "T2Backend.ceT2: unexpected CompiledExpr constructor"
  wrap prefix x st =
    let (fx, st1) = go x st
    in (showString prefix . fx . showString ")", st1)

-- ---------------------------------------------------------------------------
-- top level: 'Telomare.HvmBackend.emitProgram' with the T2 promotion rule
-- at iteration entry and a static cost-certificate header
-- ---------------------------------------------------------------------------

emitProgramT2 :: T2Mode -> CompiledExpr -> String
emitProgramT2 mode sized =
  case validateExpr sized of
    Left err -> error $ "T2Backend.emitProgramT2: " <> err
    Right () ->
      let defers = collectDefers sized
          slots = slotMap defers
          st0 = EmitState id 0
          churchOf :: Map Int Int
          churchOf = Map.fromList
            [ (slot, k)
            | ((_, body), slot) <- zip defers [0 ..]
            , Just k <- [matchChurchCode body] ]
          -- T2 boxS: the step closure crosses into the iteration; force it
          -- to NF once at loop entry so per-unwinding reads copy data.
          fstep = if iterBoxOn mode
            then showString "tvDF(tvL(tvR(env)))"
            else showString "tvL(tvR(env))"
          repeatArm = showString "            return tvRepeat(k, " . fstep
                    . showString ", tvL(env))\n"
          emitDefer ((_, body), slot) (frags, st)
            | isRepeatBody body =
                let (fb, st') = ceT2 mode slots body st
                    def = showString "def d" . shows (slot :: Int)
                        . showString "(env: TV) -> TV:\n"
                        . showString "  match rc = tvL(tvL(tvR(tvR(env)))):\n"
                        . showString "    case TV/F:\n"
                        . showString "      k = churchK(rc.fid)\n"
                        . showString "      if k == 16777215:\n"
                        . showString "        return " . fb . showString "\n"
                        . showString "      else:\n"
                        . showString "        match fc = tvL(tvL(tvR(env))):\n"
                        . showString "          case TV/F:\n"
                        . showString "            rw = isRWrap(fc.fid)\n"
                        . showString "            switch rw:\n"
                        . showString "              case 0:\n"
                        . showString "                return tvRepeat(k, " . fstep
                        . showString ", tvL(env))\n"
                        . showString "              case _:\n"
                        . showString "                return TV/P(TV/F(" . shows (length defers)
                        . showString "), " . fstep . showString ")\n"
                        . showString "          case TV/Z:\n" . repeatArm
                        . showString "          case TV/P:\n" . repeatArm
                        . showString "          case TV/N:\n" . repeatArm
                        . showString "          case TV/A:\n" . repeatArm
                        . showString "    case TV/A:\n      return TV/A(rc.p)\n"
                        . showString "    case TV/Z:\n      return TV/A(TV/Z)\n"
                        . showString "    case TV/P:\n      return TV/A(TV/Z)\n"
                        . showString "    case TV/N:\n      return TV/A(TV/Z)\n\n"
                in (def . frags, st')
            | otherwise =
                let (fb, st') = ceT2 mode slots body st
                    def = showString "def d" . shows (slot :: Int)
                        . showString "(env: TV) -> TV:\n  return " . fb . showString "\n\n"
                in (def . frags, st')
          (deferFrags, st1) = foldr emitDefer (id, st0) (zip defers [0 ..])
          (mainFrags, st2) = ceT2 mode slots sized st1
          nDefers = length defers
          fixSlot = nDefers
          dispatchArm slot = showString "    case " . shows (slot :: Int)
                           . showString ":\n      return d" . shows slot . showString "(env)\n"
          dispatch = showString "def tvDispatch(slot: u24, env: TV) -> TV:\n  switch slot:\n"
                   . foldr (\s acc -> dispatchArm s . acc) id [0 .. nDefers - 1]
                   . showString "    case " . shows fixSlot
                   . showString ":\n      return tvFixApply(env)\n"
                   . showString "    case _:\n      return tvId(env)\n\n"
          churchKArm slot = showString "    case " . shows (slot :: Int)
                          . showString ":\n      return "
                          . shows (Map.findWithDefault 16777215 slot churchOf)
                          . showString "\n"
          churchK = showString "def churchK(fid: u24) -> u24:\n  switch fid:\n"
                  . foldr (\s acc -> churchKArm s . acc) id [0 .. nDefers - 1]
                  . showString "    case _:\n      return 16777215\n\n"
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
          tvFixApply = showString "def tvFixApply(env: TV) -> TV:\n"
                     . showString "  rwrap = tvR(env)\n"
                     . showString "  return tvCall(tvCall(rwrap, TV/P(TV/F("
                     . shows fixSlot . showString "), rwrap)), tvL(env))\n\n"
          telMain = showString "def tel_main() -> TV:\n  env = TV/Z\n  return "
                   . mainFrags . showString "\n\n"
          -- ---- static cost certificate ----
          letDups = countLetDups sized
                  + sum (countLetDups . snd <$> defers)
          iterSlots = [ slot | ((_, b), slot) <- zip defers [0 ..], isRepeatBody b ]
          budgets = Map.elems churchOf
          certificate = unlines
            [ "# T2 certificate (static; see design/TELOMARE2-DESIGN.md par.9,12):"
            , "#   mode: " <> (case mode of
                 T2Eager   -> "eager (T2 discipline ON: dupS let-force + iterS box)"
                 T2LetOnly -> "let-only (dupS let-force; iterS box OFF)"
                 T2Lazy    -> "lazy (baseline, discipline OFF)")
            , "#   defs: " <> show nDefers
            , "#   dupS sites (contracted computed lets, forced at binding): "
              <> show letDups
            , "#   iterS sites (step closure boxed at loop entry): "
              <> show (length iterSlots)
            , "#   iteration budgets (churchK, = inferred recursion sizes): "
              <> show budgets
            , "#   rwrap ({t,r,b} step) defs routed to O(n) tvFixApply: "
              <> show (Set.size rwrapSet)
            , "#   forbidden-by-construction: no unpriced contraction of computation"
            , "#     (every remaining implicit dup copies realized data or a u24)."
            ]
      in ( showString certificate
         . showString emittedPrelude
         . showString t2Prelude
         . deferFrags
         . emitGateDefs st2
         . dispatch
         . churchK
         . isRWrap
         . tvFixApply
         . telMain
         . showString emittedDriver
         ) ""
