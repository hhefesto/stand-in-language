{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}

-- | The Telomare Tier-2 runtime: a metered environment machine for the
-- .tel core (the charter's "deoptimize, never reject" made real).
--
-- Compatibility semantics for the historical .tel core, with two deliberate
-- deviations:
--
--   1. __Native recursion, no sizing.__ the old runtime baked a church tower
--      @SetEnv^(n+1) Env@ into every @{t,s,b}@ site;
--      the tower builds the recursion ladder @rWrap^n(abort)@ eagerly.
--      Telomare puts 'TUnbounded' in the same position and represents the
--      ladder's limit as a 'VRec' value that unrolls ONE @rWrap@ layer per
--      demanded recursive call (metered per token).  Since sizing only
--      proves a bound suffices — at runtime the base fires early through
--      the test's Gate — while-semantics agrees with sized semantics on
--      every finitely terminating program accepted by the compatibility
--      frontend, and additionally runs programs the old static sizer rejected.
--
--   2. __Lazy gate selection.__ For the syntactic if\/then\/else shape
--      @SetEnv (Pair (Gate else then) scrutinee)@,
--      the shape every recursion step uses), only the selected branch is
--      evaluated.  Required for (1) — the recur branch of an unbounded
--      ladder must not be forced past the base case.  Values on the
--      selected path are identical; dead-branch effects simply never happen.
--
-- Aborts are VALUES ('VAborted'): they propagate
-- through projections, application heads and gate scrutinees
-- (@abortStep@'s rules), may be embedded in pairs, and are DISCARDED if
-- the program never uses them — only an abort surviving into the
-- iteration result is an error ('findAbort'). Payload truncation is Zero\/Pair structural,
-- everything else Zero).
module Telomare.Tel.Eval
  ( TelExpr (..)
  , Value (..)
  , Meter (..)
  , emptyMeter
  , TelError (..)
  , EvalM
  , runEval
  , evalTel
  , applyClosure
  , forceValue
  , findAbort
  ) where

import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.State (State, get, gets, modify', put, runState)
import Data.Map (Map)
import qualified Data.Map as Map
import Telomare.Compat.Syntax (BasicExpr, UnsizedRecursionToken, pattern PairB,
                               pattern ZeroB)

-- | The .tel core, plus the native recursion node (which replaces the
-- church tower the old sizing pass would install).
data TelExpr
  = TZero
  | TPair TelExpr TelExpr
  | TEnv
  | TSetEnv TelExpr
  | TDefer TelExpr
  | TGate TelExpr TelExpr        -- ^ (zero-branch, pair-branch)
  | TLeft TelExpr
  | TRight TelExpr
  | TAbort
  | TUnbounded UnsizedRecursionToken
  deriving (Eq, Show)

-- | Machine values.  Closures are @VPair (VDefer code) env@ by the .tel
-- calling convention; 'VRec' is the on-demand recursion ladder.
data Value
  = VZero
  | VPair Value Value
  | VDefer TelExpr
  | VGate Value Value
  | VAbort
  | VAborted BasicExpr
    -- ^ an abort VALUE: propagates and may be discarded; fatal only if it
    -- survives into the iteration result
  | VRec UnsizedRecursionToken Value Value
    -- ^ @VRec tok step fenv@: the limit of @rWrap^n(abort)@; 'forceValue'
    -- unrolls one layer by applying @step@ to the ladder itself.
  deriving (Eq, Show)

-- | The work meter — Tier 2's running cost report (M4 budgets will be
-- checked against it).
data Meter = Meter
  { mApplies :: !Int                              -- ^ function applications
  , mGates   :: !Int                              -- ^ gate selections
  , mUnrolls :: !(Map UnsizedRecursionToken Int)  -- ^ per-site recursion depth
  }
  deriving (Eq, Show)

emptyMeter :: Meter
emptyMeter = Meter 0 0 Map.empty

data TelError
  = TelStuck String        -- ^ ill-formed application/projection
  | TelOutOfFuel           -- ^ @--max-steps@ exhausted
  deriving (Eq, Show)

type EvalM = ExceptT TelError (State (Meter, Maybe Int))

runEval :: Maybe Int -> EvalM a -> (Either TelError a, Meter)
runEval fuel m =
  let (r, (meter, _)) = runState (runExceptT m) (emptyMeter, fuel)
  in (r, meter)

spend :: EvalM ()
spend = gets snd >>= \case
  Nothing -> pure ()
  Just n
    | n <= 0    -> throwError TelOutOfFuel
    | otherwise -> get >>= \(m, _) -> put (m, Just (n - 1))

tickApply :: EvalM ()
tickApply = modify' (\(m, f) -> (m { mApplies = mApplies m + 1 }, f)) >> spend

tickGate :: EvalM ()
tickGate = modify' (\(m, f) -> (m { mGates = mGates m + 1 }, f))

tickUnroll :: UnsizedRecursionToken -> EvalM ()
tickUnroll tok =
  modify' (\(m, f) ->
    (m { mUnrolls = Map.insertWith (+) tok 1 (mUnrolls m) }, f)) >> spend

-- | Unroll a recursion ladder one layer; identity on everything else.
forceValue :: Value -> EvalM Value
forceValue = \case
  VRec tok step fenv -> do
    tickUnroll tok
    case step of
      VDefer d -> evalTel d (VPair (VRec tok step fenv) fenv) >>= forceValue
      _        -> throwError (TelStuck "VRec: step is not deferred code")
  v -> pure v

-- | Abort payload truncation (Zero/Pair structural,
-- everything else to Zero).
truncateV :: Value -> BasicExpr
truncateV = \case
  VPair a b -> PairB (truncateV a) (truncateV b)
  _         -> ZeroB

-- | Leftmost abort embedded anywhere in a result value. 'VDefer' bodies are
-- code, not values — nothing to scan.
findAbort :: Value -> Maybe BasicExpr
findAbort = \case
  VAborted e -> Just e
  VPair a b  -> firstJust (findAbort a) (findAbort b)
  VGate l r  -> firstJust (findAbort l) (findAbort r)
  _          -> Nothing
  where
    firstJust (Just x) _ = Just x
    firstJust Nothing  y = y

-- | One evaluation step: expression in an environment.
evalTel :: TelExpr -> Value -> EvalM Value
evalTel expr env = case expr of
  TZero      -> pure VZero
  TEnv       -> pure env
  TAbort     -> pure VAbort
  TDefer d   -> pure (VDefer d)
  TPair a b  -> VPair <$> evalTel a env <*> evalTel b env
  TGate l r  -> VGate <$> evalTel l env <*> evalTel r env
  TLeft x    -> evalTel x env >>= forceValue >>= \case
    VZero          -> pure VZero
    VPair a _      -> pure a
    a@(VAborted _) -> pure a
    _              -> throwError (TelStuck "left of non-pair")
  TRight x   -> evalTel x env >>= forceValue >>= \case
    VZero          -> pure VZero
    VPair _ b      -> pure b
    a@(VAborted _) -> pure a
    _              -> throwError (TelStuck "right of non-pair")
  -- the lazy if/then/else shape; see module header
  TSetEnv (TPair (TGate l r) s) -> do
    sv <- evalTel s env >>= forceValue
    tickGate
    case sv of
      VZero          -> evalTel l env
      VPair _ _      -> evalTel r env
      a@(VAborted _) -> pure a
      _              -> throwError (TelStuck "gate on non-data scrutinee")
  TSetEnv x  -> evalTel x env >>= forceValue >>= \case
    VPair f e      -> applyRaw f e
    a@(VAborted _) -> pure a
    _              -> throwError (TelStuck "setenv of non-pair")
  TUnbounded tok -> case env of
    VPair rf (VPair rf2 (VPair step (VPair _seed fenv))) ->
      pure (VPair rf (VPair rf2 (VPair step (VPair (VRec tok step fenv) fenv))))
    _ -> throwError (TelStuck
           "TUnbounded: unexpected iteration frame (telomare encoding drift?)")

-- | Application dispatch.
applyRaw :: Value -> Value -> EvalM Value
applyRaw fun arg = forceValue fun >>= \case
  VDefer d       -> tickApply >> evalTel d arg
  a@(VAborted _) -> pure a
  VGate l r      -> tickGate >> forceValue arg >>= \case
    VZero          -> pure l
    VPair _ _      -> pure r
    a@(VAborted _) -> pure a
    _              -> throwError (TelStuck "gate applied to non-data")
  VAbort         -> forceValue arg >>= \case
    VZero          -> pure (VDefer TEnv)   -- Abort . 0 = identity defer
    p@(VPair _ _)  -> pure (VAborted (truncateV p))
    a@(VAborted _) -> pure a
    _              -> throwError (TelStuck "abort applied to non-data")
  _              -> throwError (TelStuck "application of non-function")

-- | Apply a closure value @(Defer code, cloEnv)@ to an argument — the
-- .tel calling convention.
applyClosure :: Value -> Value -> EvalM Value
applyClosure fun arg = case fun of
  VPair (VDefer d) cloEnv -> tickApply >> evalTel d (VPair arg cloEnv)
  _                       -> throwError (TelStuck "main is not a closure")
