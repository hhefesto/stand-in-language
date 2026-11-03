-- Scratch oracle (not part of the repo): the lifted hash of main
-- (liftedBodyHash of deferLift's main) for module NAME in file FILE,
-- beside the Prelude in the working directory.
module Main where

import Data.Bifunctor (first)
import System.Environment (getArgs)
import qualified System.IO.Strict as Strict
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (deferLift, liftedBodyHash, main2Term3)

main :: IO ()
main = do
  [name, file] <- getArgs
  preludeFile <- Strict.readFile "Prelude.tel"
  src <- Strict.readFile file
  let expandNamed n content =
        case runParseModule n content >>= first renderExpansionError . expandModule of
          Right m -> m
          Left e  -> error e
  case main2Term3 [(name, expandNamed name src), ("Prelude", expandNamed "Prelude" preludeFile)] name of
    Left e -> putStrLn ("error " <> show e)
    Right t3 -> print (liftedBodyHash (snd (deferLift t3)))
