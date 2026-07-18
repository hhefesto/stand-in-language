-- | Test driver: spec vectors (Examples.agda 1:1) + law properties
-- (Agda-proved theorems, QuickChecked on the mirror; ≥1000 cases each).
module Main (main) where

import Control.Monad (forM, forM_, unless)
import System.Exit (exitFailure)
import Test.QuickCheck (quickCheckWithResult, stdArgs)
import Test.QuickCheck.Test (Args (..), isSuccess)

import BoundVectors (boundVectors)
import BudgetOracle (budgetVectors)
import CertificateVectors (certificateVectors)
import CompileFailVectors (compileFailVectors)
import CopyVectors (copyVectors)
import InferOracle (inferProps, oracleVectors)
import Laws (lawProps)
import LinearVectors (linearVectors)
import MeterVectors (meterVectors)
import ParityTel (parityVectors)
import SpecVectors (specVectors)
import SurfaceVectors (surfaceVectors)
import Tel2Vectors (tel2Vectors)
import TransportVectors (transportVectors)

main :: IO ()
main = do
  telParity <- parityVectors
  tel2 <- tel2Vectors
  compileFails <- compileFailVectors
  let vectors = specVectors <> surfaceVectors <> linearVectors <> compileFails <> copyVectors <> oracleVectors <> budgetVectors <> boundVectors <> certificateVectors <> meterVectors <> telParity <> tel2 <> transportVectors
      props   = lawProps <> inferProps
      failedVectors = [n | (n, ok) <- vectors, not ok]
  forM_ vectors $ \(n, ok) ->
    putStrLn ((if ok then "PASS " else "FAIL ") <> n)
  lawResults <- forM props $ \(n, p) -> do
    putStrLn ("LAW  " <> n)
    r <- quickCheckWithResult (stdArgs { maxSuccess = 1000 }) p
    pure (n, isSuccess r)
  let failedLaws = [n | (n, ok) <- lawResults, not ok]
  unless (null failedVectors && null failedLaws) $ do
    forM_ (failedVectors <> failedLaws) (putStrLn . ("FAILED: " <>))
    exitFailure
  putStrLn ("all " <> show (length vectors) <> " vectors + "
            <> show (length props) <> " laws OK")
