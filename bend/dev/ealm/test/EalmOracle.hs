{-# LANGUAGE LambdaCase #-}
-- Scratch oracle for bend/EALm.bend (not part of the repo): for each line
-- of the input file (an expression, run as `main = EXPR` beside the
-- Prelude), print the main pass of master's EAL alone (inferEALLifted's
-- runMain, uniform chains off, no let-specialization fallback).
module Main where

import Control.Monad.Except (runExceptT)
import qualified Control.Monad.State.Strict as State
import Data.Bifunctor (first)
import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import System.Environment (getArgs)
import qualified System.IO.Strict as Strict
import Telomare.EAL
import Telomare.Error (renderEALError)
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (DeferMap (..), deferLift, main2Term3)

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
        let (DeferMap dm, m) = deferLift t3
        case State.evalState (runExceptT (go m)) (initEALState { esBodies = dm }) of
          Left e -> putStrLn ("main: fail " <> intercalate " | " (lines (renderEALError e)))
          Right (r, shapes, levels) -> do
            putStrLn ("main: top " <> show (ealTopLevelBang r) <> " max " <> show (ealMaxLevel r)
              <> " shape " <> show (ealMainShape r) <> " defers "
              <> intercalate "," [ show fi <> "=" <> show b | (fi, b) <- Map.toList (ealDeferBangs r) ])
            mapM_ (\(h, (fi, _)) -> putStrLn ("  " <> take 8 (show h) <> " " <> show fi
              <> " env " <> show (Map.findWithDefault 0 fi (ealDeferBangs r))
              <> " lvl " <> show (Map.findWithDefault 0 fi levels)
              <> " layout " <> show (Map.lookup h shapes))) (Map.toList dm)
        let lr = inferEALWithLifting t3
        putStrLn ("pre: " <> intercalate " | " (lines (renderEALVerdict lr)))
        case ealLiftedMain lr of
          Right r -> putStrLn ("pre.main: top " <> show (ealTopLevelBang r) <> " max " <> show (ealMaxLevel r)
            <> " shape " <> show (ealMainShape r) <> " defers "
            <> intercalate "," [ show fi <> "=" <> show b | (fi, b) <- Map.toList (ealDeferBangs r) ])
          Left _ -> pure ()
        putStrLn ("certifyMain: " <> either (intercalate " | " . lines . renderEALError) (const "ok") (certifyMain t3))) progs
  where
    unescape = \case
      '\\' : 'n' : rest -> '\n' : unescape rest
      c : rest -> c : unescape rest
      [] -> []
    go term = do
      (bMain, _, sRes, vals) <- analyzeTopWith True "program input" term
      let value r = fromMaybe 0 $ Map.lookup r vals
      topBang <- value <$> findB bMain
      defers <- State.gets esDefers >>= fmap (Map.fromListWith max) .
        traverse (\(fi, b) -> (,) fi . value <$> findB b)
      depths <- leafDepths vals
      levels <- bodyLeafDepths vals
      shapes <- groundCaptureShapes
      mainShape <- shapeOfSigma sRes
      pure ( EALResult { ealTopLevelBang = topBang, ealDeferBangs = defers
                       , ealMaxLevel = maximum (0 : depths), ealMainShape = mainShape }
           , shapes, levels )
