{-# LANGUAGE LambdaCase #-}

-- | The Telomare transcript IO loop — the protocol of
-- the .tel transcript protocol:
--
--   * @main@ runs FIRST, on Zero, before any input is read;
--   * each iteration: decode the display half, print it (one trailing
--     newline), then — if the new state is not Zero — read one line and
--     run @main (Pair (encode line) state)@;
--   * bare Zero result = "aborted"; state Zero ends the loop (the historical
--     interactive mode ends silently — the "done" string is discarded);
--   * prompts are part of program output, never printed by the loop.
--
-- Deliberate improvement over the old loop: EOF
-- on stdin ends the loop cleanly instead of crashing with an hGetLine
-- exception.
module Telomare.Tel.Loop
  ( iterateMain
  , runTelLoop
  , runTelWithInput
  , s2v
  , v2s
  ) where

import Data.Char (chr, ord)
import System.IO (hFlush, isEOF, stdout)

import Telomare.Compat.Syntax (RunTimeError (AbortRunTime))
import Telomare.Tel.Eval

-- ── encodings over machine values ───────────────────────────────────────────

i2v :: Int -> Value
i2v 0 = VZero
i2v n = VPair (i2v (n - 1)) VZero

v2i :: Value -> Maybe Int
v2i VZero           = Just 0
v2i (VPair n VZero) = succ <$> v2i n
v2i _               = Nothing

s2v :: String -> Value
s2v = foldr (VPair . i2v . ord) VZero

v2s :: Value -> Maybe String
v2s VZero        = Just ""
v2s (VPair c cs) = ((:) . chr <$> v2i c) <*> v2s cs
v2s _            = Nothing

-- ── one loop iteration (funWrap) ────────────────────────────────────────────

-- | Run one iteration: apply the main closure to this iteration's input
-- value.  Returns the display string and @Just newState@ to continue.
iterateMain :: Value -> Maybe (String, Value) -> EvalM (String, Maybe Value)
iterateMain mainClosure inp =
  let inputValue = case inp of
        Nothing               -> VZero
        Just (line, oldState) -> VPair (s2v line) oldState
  in applyClosure mainClosure inputValue >>= \result ->
        -- A surviving abort embedded anywhere in the result
       -- ends the run (discarded aborts never got here)
       case findAbort result of
         Just e -> pure ("runtime error:\n" <> show (AbortRunTime e), Nothing)
         Nothing -> case result of
           VZero -> pure ("aborted", Nothing)
           VPair disp newState -> case v2s disp of
             Just d -> pure (d, case newState of
                              VZero -> Nothing
                              ns    -> Just ns)
             Nothing -> pure ("error converting display value", Nothing)
           _ -> pure ("error converting iteration value", Nothing)

-- Evaluate the compiled program to the main closure value.
mainClosureOf :: TelExpr -> EvalM Value
mainClosureOf t = evalTel t VZero

-- ── interactive loop ────────────────────────────────────────────────────────

-- | Interactive transcript loop.  Returns the final meter.
runTelLoop :: Maybe Int -> TelExpr -> IO Meter
runTelLoop fuel prog = go Nothing (Left ())
  where
    -- We re-enter runEval per iteration carrying no evaluator state, so
    -- meter totals accumulate here.
    go inp acc =
      let (r, meter) = runEval fuel (mainClosureOf prog >>= \m -> iterateMain m inp)
          total = accumulate acc meter
      in case r of
           Left e -> do
             putStrLn (renderTelError e)
             pure total
           Right (out, next) -> do
             putStrLn out
             hFlush stdout
             case next of
                Nothing -> pure total
                Just ns -> isEOF >>= (\case
                  True  -> pure total   -- clean EOF
                  False -> do
                    line <- getLine
                    go (Just (line, ns)) (Right total))
    accumulate acc m = case acc of
      Left ()  -> m
      Right m0 -> Meter (mApplies m0 + mApplies m) (mGates m0 + mGates m)
                        (mUnrolls m0 <> mUnrolls m)

-- | Pure transcript for tests: outputs joined by newlines, one line per
-- iteration, ending like the interactive loop (no "done").  Runs at most
-- as many iterations as there are input lines (plus the initial one).
runTelWithInput :: Maybe Int -> TelExpr -> [String] -> (Either TelError [String], Meter)
runTelWithInput fuel prog inputs = runEval fuel $ do
  m <- mainClosureOf prog
  let go inp remaining = do
        (out, next) <- iterateMain m inp
        case (next, remaining) of
          (Nothing, _)      -> pure [out]
          (Just _, [])      -> pure [out]
          (Just ns, l : ls) -> (out :) <$> go (Just (l, ns)) ls
  go Nothing inputs

renderTelError :: TelError -> String
renderTelError = \case
  TelStuck msg -> "runtime error (stuck): " <> msg
  TelOutOfFuel -> "runtime error: step budget exhausted (Tier-2 meter)"
