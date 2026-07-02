{-# LANGUAGE BangPatterns #-}

-- | Native-GHC baseline for the run comparison: the SAME algorithm (telomare's
-- drainS = whileS nonZeroS predS) as a strict guarded loop.  The test/body are
-- the same definitions the ConCat emission consumes (duplicated from HvmMain.hs
-- — keep in sync); this executable is compiled WITHOUT the ConCat plugin.
--
--   telomare-bench-hs N   →  prints the loop result (0)
module Main where

import System.Environment (getArgs)

drainTest :: Int -> Bool
drainTest x = 0 < x
{-# INLINE drainTest #-}

drainBody :: Int -> Int
drainBody x = x - 1
{-# INLINE drainBody #-}

-- the whileS unfolding: fuel-bounded guarded loop, strict accumulator
go :: Int -> Int -> Int
go 0 x = x
go n !x = if drainTest x then go (n - 1) (drainBody x) else x

main :: IO ()
main = do
  args <- getArgs
  case args of
    [s] -> let n = read s :: Int
           in putStrLn ("result = " ++ show (go n n))
    _   -> putStrLn "usage: telomare-bench-hs N"
