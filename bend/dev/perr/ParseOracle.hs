-- parse-oracle MODE FILE: master's parse errors, for the port's checker.
-- FILE holds cases separated by '\RS'. MODE: module | defs | repl | expr.
-- Prints "== i" then errorBundlePretty, or "OK", for each case.
module Main where

import Control.Monad (void)
import Data.Void (Void)
import System.Environment (getArgs)
import System.IO
import Telomare.Parse
import Text.Megaparsec

splitRS :: String -> [String]
splitRS s = case break (== '\RS') s of
  (a, [])     -> [a]
  (a, _ : bs) -> a : splitRS bs

replStep :: TelomareParser ()
replStep = try (void (parseSingleDefinition <* eof)) <|> void (parseLongExpr <* eof)

run :: String -> String -> String
run mode input = case mode of
  "module" -> shown (runParser (void parseModuleItems) "t" input)
  "defs"   -> shown (runParser (void parseDefinitions) "" input)
  "repl"   -> shown (runParser replStep "" input)
  "expr"   -> shown (runParser (void parseExpression) "" input)
  _        -> error "mode: module | defs | repl | expr"
  where
    shown :: Either (ParseErrorBundle String Void) () -> String
    shown = either errorBundlePretty (const "OK\n")

main :: IO ()
main = do
  [mode, file] <- getArgs
  hSetEncoding stdout utf8
  h <- openFile file ReadMode
  hSetEncoding h utf8
  content <- hGetContents h
  mapM_ (\(i, c) -> putStr ("== " <> show i <> "\n" <> run mode c))
        (zip [0 :: Int ..] (splitRS content))
