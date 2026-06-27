{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators   #-}

-- | Compile telomare morphism ports through ConCat into the HVM category,
-- emitting runnable Bend (HVM2) programs to out/<name>.bend.
module Main where

import Prelude

import System.Directory (createDirectoryIfMissing)

import ConCat.AltCat (toCcc)
import ConCat.Misc   ((:*), sqr)
import ConCat.Rebox  ()

import HVM (HVM, render, toBendProgram, toBendIterate, toBendFold)

-- ── telomare morphism ports (over Int / u24) ──
fibAccStep :: Int :* Int -> Int :* Int        -- (a,b) ↦ (b, a+b)
fibAccStep (a, b) = (b, a + b)
{-# INLINE fibAccStep #-}

type V4 = ((Int :* Int) :* Int) :* Int

s4a, s4b, s4c :: V4 -> V4
s4a (((a,b),c),d) = (((min a b, max a b), min c d), max c d)
s4b (((a,b),c),d) = (((min a c, min b d), max a c), max b d)
s4c (((a,b),c),d) = (((a, min b c), max b c), d)
{-# INLINE s4a #-}
{-# INLINE s4b #-}
{-# INLINE s4c #-}

mergeSort4 :: V4 -> V4
mergeSort4 v = s4c (s4b (s4a v))
{-# INLINE mergeSort4 #-}

type V8 = (((((((Int :* Int) :* Int) :* Int) :* Int) :* Int) :* Int) :* Int)

sortL1, sortL2, sortL3, sortL4, sortL5, sortL6 :: V8 -> V8
sortL1 (((((((a,b),c),d),e),f),g),h) =
  (((((((min a b, max a b), min c d), max c d), min e f), max e f), min g h), max g h)
sortL2 (((((((a,b),c),d),e),f),g),h) =
  (((((((min a c, min b d), max a c), max b d), min e g), min f h), max e g), max f h)
sortL3 (((((((a,b),c),d),e),f),g),h) =
  (((((((a, min b c), max b c), d), e), min f g), max f g), h)
sortL4 (((((((a,b),c),d),e),f),g),h) =
  (((((((min a e, min b f), min c g), min d h), max a e), max b f), max c g), max d h)
sortL5 (((((((a,b),c),d),e),f),g),h) =
  (((((((a, b), min c e), min d f), max c e), max d f), g), h)
sortL6 (((((((a,b),c),d),e),f),g),h) =
  (((((((a, min b c), max b c), min d e), max d e), min f g), max f g), h)
{-# INLINE sortL1 #-}
{-# INLINE sortL2 #-}
{-# INLINE sortL3 #-}
{-# INLINE sortL4 #-}
{-# INLINE sortL5 #-}
{-# INLINE sortL6 #-}

mergeSort8 :: V8 -> V8
mergeSort8 v = sortL6 (sortL5 (sortL4 (sortL3 (sortL2 (sortL1 v)))))
{-# INLINE mergeSort8 #-}

-- ── bounded recursion (run on HVM2 with a RUNTIME size) ──
-- telomare fibS = exlS ∘S iterS fibAccStepS ∘S fibInitS, with the iteration
-- count a runtime CLI arg.  step + init go through toCcc; iterS is the primitive.
fibInit :: Int -> Int :* (Int :* Int)        -- n ↦ (n, (0,1))  (count, seed)
fibInit n = (n, (0, 1))
{-# INLINE fibInit #-}

-- tree reduction (sum): leaf = id, combine = (+).  Parallel divide-and-conquer.
addPair :: Int :* Int -> Int
addPair (a, b) = a + b
{-# INLINE addPair #-}

idInt :: Int -> Int
idInt x = x
{-# INLINE idInt #-}

emit :: String -> HVM a b -> String -> IO ()
emit name m input = do
  let bend = toBendProgram m input
  writeFile ("out/" ++ name ++ ".bend") bend
  putStrLn (name ++ "  term: " ++ render m)
  putStrLn ("  wrote out/" ++ name ++ ".bend  (run on it: bend run-c)")

main :: IO ()
main = do
  createDirectoryIfMissing True "out"
  putStrLn "ConCat -> HVM2: compiling telomare morphism ports to Bend programs"
  putStrLn ""
  emit "hvm-sqr"        (toCcc (sqr @Int)  :: HVM Int Int)                  "5"
  emit "hvm-fib-step"   (toCcc fibAccStep  :: HVM (Int :* Int) (Int :* Int)) "(3, 4)"
  emit "hvm-merge-sort4"(toCcc mergeSort4  :: HVM V4 V4)                     "(((3, 1), 4), 2)"
  emit "hvm-merge-sort8"(toCcc mergeSort8  :: HVM V8 V8)
       "(((((((7, 6), 5), 4), 3), 2), 1), 0)"
  -- bounded recursion: step/init via toCcc, recursion as a primitive loop; size = runtime CLI arg
  writeFile "out/hvm-fib-iter.bend"
    (toBendIterate (toCcc fibAccStep :: HVM (Int :* Int) (Int :* Int))
                   (toCcc fibInit    :: HVM Int (Int :* (Int :* Int))))
  putStrLn "hvm-fib-iter   wrote out/hvm-fib-iter.bend  (run: bend run-c <it> N  -> fib(N), runtime-sized)"
  writeFile "out/hvm-tree-sum.bend"
    (toBendFold (toCcc idInt   :: HVM Int Int)
                (toCcc addPair :: HVM (Int :* Int) Int))
  putStrLn "hvm-tree-sum   wrote out/hvm-tree-sum.bend  (run: bend run-c <it> D  -> 2^D, parallel fold)"
  putStrLn ""
  putStrLn "Done. Expected when run on HVM2:"
  putStrLn "  hvm-sqr        5                 -> 25"
  putStrLn "  hvm-fib-step   (3,4)             -> (4, 7)"
  putStrLn "  hvm-merge-sort4 (3,1,4,2)        -> (1, 2, 3, 4)"
  putStrLn "  hvm-merge-sort8 [7,6,5,4,3,2,1,0] -> [0,1,2,3,4,5,6,7]"
