module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)
import Telomare3.Core (telomare3Version)

-- M0 placeholder test; real spec-vector and law tests arrive at M2.
main :: IO ()
main = unless (take 9 telomare3Version == "telomare3") exitFailure
