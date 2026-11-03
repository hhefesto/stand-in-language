-- Scratch oracle (not part of the repo): master's solveLinear on systems
-- read one per line: nv|lbs|weights|lhs>rhs;...
module Main where

import qualified Data.Map as Map
import System.Environment (getArgs)
import Telomare.EAL
import Telomare.Error (Blame (..))
import Telomare.IR.Loc (LocTag (..))

splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
  (a, _ : rest) -> a : splitOn c rest
  (a, [])       -> [a]

main :: IO ()
main = do
  [file] <- getArgs
  ls <- lines <$> readFile file
  mapM_ (\l -> do
    let [nvS, lbS, wS, eqS] = splitOn '|' l
        nv = read nvS :: Int
        lbs = fmap read (words lbS) :: [Int]
        ws = fmap read (words wS) :: [Integer]
        eqs = [ EqR (fmap read (words lhs)) (read rhs) (BlameIn UnknownLoc (show i) Nothing)
              | (i, e) <- zip [0 :: Int ..] (splitOn ';' eqS), let [lhs, rhs] = splitOn '>' e ]
    putStrLn $ case solveLinear (lbs !!) (ws !!) eqs of
      Left bad -> "fail" <> concatMap (\(EqR _ _ (BlameIn _ s _)) -> " " <> s) bad
      Right m -> "ok" <> concatMap (\v -> " " <> maybe "-" show (Map.lookup v m)) [0 .. nv - 1]) ls
