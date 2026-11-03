module Main where
import Data.Bifunctor (first)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Environment (getArgs)
import qualified System.IO.Strict as Strict
import Telomare.EAL
import Telomare.Expand (expandModule, renderExpansionError)
import Telomare.Parse (runParseModule)
import Telomare.Resolve (DeferMap (..), deferLift, main2Term3, liftedBodyHash)

main :: IO ()
main = do
  [file, deepS] <- getArgs
  preludeFile <- Strict.readFile "Prelude.tel"
  s <- Strict.readFile file
  let expandNamed name content =
        case runParseModule name content >>= first renderExpansionError . expandModule of
          Right m -> m
          Left e  -> error e
      prelude = [("Prelude", expandNamed "Prelude" preludeFile)]
      Right t3 = main2Term3 (("AuxModule", expandNamed "AuxModule" ("import Prelude\nmain = " <> s)) : prelude) "AuxModule"
      (DeferMap dm, m) = deferLift t3
      (dmS, originS, mainS, SpecInfo defs reads) = specializeLets Nothing (deepS == "1") dm m
  putStrLn ("spec bodies " <> show (Map.size dmS) <> " origins " <> show (Map.size originS) <> " defs " <> show (Set.size defs))
  mapM_ (\(h, o) -> putStrLn ("  " <> show h <> " <- " <> show o)) (Map.toList originS)
  putStrLn ("main " <> show (liftedBodyHash mainS))
  mapM_ (\d -> putStrLn ("def " <> show d)) (Set.toList defs)
  mapM_ (\(fi, ks) -> putStrLn ("reads " <> show fi <> " " <> show (Set.toList ks))) (Map.toList reads)
