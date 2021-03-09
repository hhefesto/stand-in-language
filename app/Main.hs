module Main where

import           Data.Char
import qualified System.IO.Strict     as Strict
import           Telomare
import           Telomare.Eval
import           Telomare.Optimizer
import           Telomare.Parser
import           Telomare.RunTime
import           Telomare.TypeChecker (inferType, typeCheck)
--import Telomare.Llvm

main = do
  preludeFile <- Strict.readFile "Prelude.tel"

  let
    prelude = case parsePrelude preludeFile of
      Right p -> p
      Left pe -> error $ getErrorString pe
    runMain s = case compile <$> parseMain prelude s of
      Left e -> putStrLn $ concat ["failed to parse ", s, " ", e]
      Right (Right g) -> evalLoop g
      Right z -> putStrLn $ "compilation failed somehow, with result " <> show z
    -- testData = Twiddle $ Pair (Pair (Pair Zero Zero) Zero) (Pair Zero Zero)
    -- testData = PRight $ Pair (Pair (Pair Zero Zero) Zero) (Pair Zero Zero)
    -- testData = SetEnv $ Pair (Defer $ Pair Zero Env) Zero
    -- testData = ite (Pair Zero Zero) (Pair (Pair Zero Zero) Zero) (Pair Zero (Pair Zero Zero))

  -- print $ makeModule testData
  {-
  runJIT (makeModule testData) >>= \result -> case result of
    Left err -> putStrLn $ concat ["JIT error: ", err]
    Right mod -> putStrLn "JIT seemed to finish ok"
  -}
  -- printBindingTypes prelude
  -- Strict.readFile "tictactoe.tel" >>= runMain
  Strict.readFile "examples.tel" >>= runMain
  --runMain "main = \\x -> 0"
  --runMain "main = \\x -> if x then 0 else (\"Test message\", 0)"
  --runMain "main = \\x -> if listEqual (left x) \"quit\" then 0 else (\"type quit to exit\", 1)"
