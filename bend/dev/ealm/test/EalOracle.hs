{-# LANGUAGE LambdaCase #-}
-- Scratch oracle for the Bend port of master's EAL (not part of the repo):
-- for each line of the input file (an expression, run as `main = EXPR`
-- beside the Prelude), print master's EAL verdicts and guidance.
module Main where

import Data.Bifunctor (first)
import Data.List (intercalate)
import qualified Data.Map as Map
import System.Environment (getArgs)
import qualified System.IO.Strict as Strict
import Telomare.Driver (compileUnitTest)
import Telomare.EAL
import Telomare.Error (renderEALError)
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (main2Term3)

main :: IO ()
main = do
  [file] <- getArgs
  preludeFile <- Strict.readFile "Prelude.tel"
  progs <- fmap unescape . lines <$> Strict.readFile file
  let expandNamed name content =
        case runParseModule name content >>= first renderExpansionError . expandModule of
          Right m -> m
          Left e  -> error e
      prelude = [("Prelude", expandNamed "Prelude" preludeFile)]
      parse str = first show $ main2Term3
        (("AuxModule", expandNamed "AuxModule" ("import Prelude\nmain = " <> str)) : prelude) "AuxModule"
  mapM_ (\s -> do
    putStrLn ("== " <> s)
    case parse s of
      Left e -> putStrLn ("parse: " <> e)
      Right t3 -> do
        let lr = inferEALWithLifting t3
        report "pre" lr
        putStrLn . ("certifyMain: " <>) $ either renderEALError (const "ok") (certifyMain t3)
        let fa = inferEALFaithful t3
        report "faithful" fa
        case compileUnitTest t3 of
          Left e -> putStrLn ("compile: " <> show e)
          Right c -> report "post" (inferEALCompiled c)) progs
  where
    unescape = \case
      '\\' : 'n' : rest -> '\n' : unescape rest
      c : rest -> c : unescape rest
      [] -> []
    report what lr = do
      putStrLn (what <> ": " <> renderEALVerdict lr)
      case ealLiftedMain lr of
        Right r -> putStrLn (what <> ".main: top " <> show (ealTopLevelBang r) <> " max " <> show (ealMaxLevel r)
          <> " shape " <> show (ealMainShape r) <> " defers "
          <> intercalate "," [ show fi <> "=" <> show b | (fi, b) <- Map.toList (ealDeferBangs r) ])
        Left _ -> pure ()
      mapM_ (\(h, g) -> putStrLn ("  " <> take 8 (show h) <> " " <> case g of
        Left e -> "fail " <> head (lines (renderEALError e) <> [""])
        Right cg -> show (cgIndex cg) <> " env " <> show (cgEnvBang cg) <> " lvl " <> show (cgMaxLevel cg)
          <> " spec " <> show (cgSpeculatable cg) <> " layout " <> show (cgCaptureLayout cg)
          <> " usage " <> show (Map.toList (cgUsage cg)))) (Map.toList (ealGuidance lr))
