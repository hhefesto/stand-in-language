module Main where
-- show-oracle FILE: each lifted body of master's deferLift, by first index:
-- "fi hash" then the show text liftedBodyHash digests.
import Data.Bifunctor (first)
import qualified Data.Map as Map
import Data.List (sortOn)
import System.Environment (getArgs)
import qualified System.IO.Strict as Strict
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (DeferMap (..), deferLift, main2Term3)
import Telomare.EAL (forgetL)

main :: IO ()
main = do
  [file] <- getArgs
  preludeFile <- Strict.readFile "Prelude.tel"
  s <- Strict.readFile file
  let expandNamed name content =
        case runParseModule name content >>= first renderExpansionError . expandModule of
          Right m -> m
          Left e  -> error e
      prelude = [("Prelude", expandNamed "Prelude" preludeFile)]
      Right t3 = main2Term3 (("AuxModule", expandNamed "AuxModule" ("import Prelude\nmain = " <> s)) : prelude) "AuxModule"
      (DeferMap dm, m) = deferLift t3
  mapM_ (\(h, (fi, b)) -> do
          putStrLn ("== " <> show fi <> " " <> show h)
          putStrLn (show (forgetL b))) (sortOn (fst . snd) (Map.toList dm))
