module Main (main) where

import System.Environment (getArgs)
import System.Exit (die)

import Telomare.Backend.Bend
import Telomare.Transport

-- Standalone, non-interactive transport-to-Bend command. It deliberately does
-- not parse or typecheck Tel2.
main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    [artifactPath] -> do
      source <- readFile artifactPath
      artifact <- either die pure (parseArtifact source)
      validated <- either (die . validationMessage) pure (validateArtifact artifact)
      either (die . bendErrorMessage) putStr (emitBend validated)
    _ -> die "usage: telomare-bend ARTIFACT"
