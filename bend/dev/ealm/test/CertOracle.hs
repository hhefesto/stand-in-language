{-# LANGUAGE LambdaCase #-}
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
import Telomare.Driver (SizingOption (..), compileReporting, certifiedProgramFrom, CompiledProgram (..))
import Telomare.Machine (chainLinks)
import Telomare.Size (SizingReport (..))
import Telomare.Eval.IC (renderRefusal)
import Data.List (sortOn)
import Telomare.IR.Core (Term3, compiled2Term3)
import Data.List (isInfixOf)
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
        w | w `elem` ["fwalk", "fshwalk", "fdpwalk"] -> let
            (DeferMap dm0, m0) = uncurry faithfulProgram (deferLift t3)
            (dm, m) = case w of
              "fwalk" -> (dm0, m0)
              _ -> let (dmS, _, mainS, _) = specializeLets Nothing (w == "fdpwalk") dm0 m0 in (dmS, mainS)
            stats = State.execState (runExceptT (walkTop True "program input" m)) (initEALState { esBodies = dm, esUniformChains = True })
          in timed w ("bodies " <> show (Map.size dm) <> " vars " <> show (esNextVar stats) <> " eqs " <> show (esSumEqCount stats)
               <> " applies " <> show (esNextApply stats) <> " leaves " <> show (esLeafCount stats))
        "fmain" -> let (DeferMap dm, m) = uncurry faithfulProgram (deferLift t3) in
          timed "fmain" (case State.evalState (runExceptT (analyzeTopWith True "program input" m)) (initEALState { esBodies = dm, esUniformChains = True }) of
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
        "post" -> postPhase t3
        "showpost" -> case compileReporting MainSizing pure t3 of
          Left e -> putStrLn ("sizing error " <> take 300 (show e))
          Right (_, sized) -> let (DeferMap dm, _) = deferLift (compiled2Term3 sized) in
            mapM_ (\(h, (fi, b)) -> let t = show (forgetL b) in if "Abort" `isInfixOf` t then putStrLn (show (fromEnum fi) <> " " <> take 16 (show h) <> " " <> t) else pure ()) (Map.toList dm)
        "fguide" -> mapM_ putStrLn (guideLines (inferEALFaithful t3))
        "faithful" -> timed "faithful" (either (const "refused") (const "ok") (ealLiftedMain (inferEALFaithful t3)))
        _ -> putStrLn ("unknown phase " <> p)) ph

showStepsO :: [Step] -> String
showStepsO = concatMap (\case SL -> "L"; SR -> "R")

guideLine :: String -> CodeGuidance -> String
guideLine h g = "g " <> show (fromEnum (cgIndex g)) <> " bang " <> show (cgEnvBang g)
  <> " max " <> show (cgMaxLevel g) <> " spec " <> show (cgSpeculatable g)
  <> " layout " <> maybe "-" show (cgCaptureLayout g)
  <> " usage " <> intercalate "," [ (if null p then "." else showStepsO p) <> "=" <> show n | (p, n) <- Map.toList (cgUsage g) ]
  <> " h " <> take 16 h

guideLines :: EALLiftedResult -> [String]
guideLines lr = ("verdict: " <> intercalate " | " (lines (renderEALVerdict lr))) :
  [ either (\e -> "f " <> take 16 (show h) <> " " <> intercalate " | " (lines (renderEALError e))) (guideLine (show h)) eg
  | (h, eg) <- sortOn (\(h, eg) -> (either (const (-1000000)) (fromEnum . cgIndex) eg, show h)) (Map.toList (ealGuidance lr)) ]

postPhase :: Term3 -> IO ()
postPhase t3 = case compileReporting MainSizing pure t3 of
  Left e -> putStrLn ("sizing error " <> take 300 (show e))
  Right (report, sized) -> do
    let cert = inferEALFaithful t3
        links = chainLinks (sizingReportCounts report)
    putStrLn ("faithful: " <> intercalate " | " (lines (renderEALVerdict cert)))
    putStrLn ("derive: " <> either ("Left " <>) (const "Right") (deriveSizedGuidance links t3 cert sized))
    let cp = certifiedProgramFrom t3 report sized
    putStrLn ("verdict: " <> either (\r -> "Left " <> intercalate " | " (lines r)) (\r -> "Right top " <> show (ealTopLevelBang r) <> " max " <> show (ealMaxLevel r) <> " shape " <> show (ealMainShape r)) (cpVerdict cp))
    mapM_ (\(h, g) -> putStrLn (guideLine (show h) g)) (sortOn (\(h, g) -> (fromEnum (cgIndex g), show h)) (Map.toList (cpGuidance cp)))
