-- Scratch oracle (not part of the repo): time master's EAL phases on module
-- NAME in FILE (Prelude.tel in the working directory): the main pass
-- (inferEALLifted's verdict, ealLiftedMain of inferEALWithLifting) and the
-- pre-sizing gate certifyMain, each printed with its CPU seconds.
module Main where

import Control.Exception (evaluate)
import Data.Bifunctor (first)
import Data.List (intercalate)
import qualified Data.Map as Map
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.IO (hFlush, stdout)
import qualified System.IO.Strict as Strict
import Telomare.EAL
import Telomare.Error (renderEALError)
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (DeferMap (..), deferLift, main2Term3)
import Control.Monad.Except (runExceptT)
import qualified Control.Monad.State.Strict as State

timed :: String -> String -> IO ()
timed label s = do
  t0 <- getCPUTime
  n <- evaluate (length s)
  t1 <- getCPUTime
  putStrLn (label <> " (" <> show (fromIntegral (t1 - t0) / 1e12 :: Double) <> "s, " <> show n <> " chars): " <> take 300 s)
  hFlush stdout

main :: IO ()
main = do
  (name : file : phases) <- getArgs
  preludeFile <- Strict.readFile "Prelude.tel"
  src <- Strict.readFile file
  let expandNamed n content =
        case runParseModule n content >>= first renderExpansionError . expandModule of
          Right m -> m
          Left e  -> error e
  case main2Term3 [(name, expandNamed name src), ("Prelude", expandNamed "Prelude" preludeFile)] name of
    Left e -> putStrLn ("error " <> show e)
    Right t3 -> do
      let ph = if null phases then ["pre", "certify"] else phases
          lr = inferEALWithLifting t3
      mapM_ (\p -> case p of
        "pre" -> timed "pre" (intercalate " | " (lines (renderEALVerdict lr)))
        "certify" -> timed "certifyMain" (either (intercalate " | " . lines . renderEALError) (const "ok") (certifyMain t3))
        "main" -> let (DeferMap dm, m) = deferLift t3 in
          timed "main" (case State.evalState (runExceptT (analyzeTopWith True "program input" m)) (initEALState { esBodies = dm }) of
            Left e -> "fail " <> intercalate " | " (lines (renderEALError e))
            Right _ -> "ok")
        w | w `elem` ["walk", "shwalk", "dpwalk"] -> let
            (DeferMap dm0, m0) = deferLift t3
            (dm, m) = case w of
              "walk" -> (dm0, m0)
              _ -> let (dmS, _, mainS, _) = specializeLets Nothing (w == "dpwalk") dm0 m0 in (dmS, mainS)
            stats = State.execState (runExceptT (walkTop True "program input" m)) (initEALState { esBodies = dm })
          in timed w ("bodies " <> show (Map.size dm) <> " vars " <> show (esNextVar stats) <> " eqs " <> show (esSumEqCount stats)
               <> " applies " <> show (esNextApply stats) <> " leaves " <> show (esLeafCount stats))
        "faithful" -> timed "faithful" (either (const "refused") (const "ok") (ealLiftedMain (inferEALFaithful t3)))
        _ -> putStrLn ("unknown phase " <> p)) ph
