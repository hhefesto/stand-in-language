-- Run-comparison driver: ONE telomare _⇨S_ algorithm — drainS = whileS nonZeroS
-- predS (cost 2N+1, proved by refl in telomare.agda) — executed by the verified
-- reference runtime ⟦_⟧K via runFromSyntax.
--
--   benchDrain N            run mode: execute drainS (N , N), print the result
--                           (auto-budget pipeline: computes ⟦_⟧C then runs ⟦_⟧K)
--   benchDrain N predict    predict mode: print cost / span / space (no ⟦_⟧K run)
--
-- The external runner (nix run .#bench-drain) times the process; the same
-- algorithm also runs as a native GHC loop and on HVM2 via ConCat emission.
{-# OPTIONS --guardedness #-}
module benchDrain where

open import telomare hiding (main)

open import Data.Nat            using (ℕ)
open import Data.Nat.Show       using (show; readMaybe)
open import Data.List           using (List; []; _∷_)
open import Data.Maybe          using (Maybe; just; nothing)
open import Data.Product        using (_,_; proj₁; proj₂)
open import Data.String         using (String; _++_)
open import Data.Unit.Polymorphic using (⊤)
open import Level               using (0ℓ)
open import IO                  using (IO; putStrLn; Main; _>>_; _>>=_)
open import System.Environment  using (getArgs)

private
  showResult : Result ℕ → String
  showResult halted         = "halted"
  showResult (finished v g) = show v

  -- run mode: the canonical telomare pipeline (budget from ⟦_⟧C, then ⟦_⟧K)
  runMode : ℕ → IO {0ℓ} ⊤
  runMode n = putStrLn ("result = " ++ showResult (runFromSyntax drainS (n , n)))

  -- predict mode: the three static resource functors (no execution)
  predictMode : ℕ → IO {0ℓ} ⊤
  predictMode n =
    putStrLn ("cost  = " ++ show (proj₁ (⟦ drainS ⟧C (n , n))) ++ "   (= 2N: test+tick per step; fuel = start ⇒ no final test)") >>
    putStrLn ("span  = " ++ show (span drainS (n , n))) >>
    putStrLn ("space = " ++ show (space drainS (n , n)))

  go : List String → IO {0ℓ} ⊤
  go (s ∷ []) with readMaybe 10 s
  ... | just n  = runMode n
  ... | nothing = putStrLn "usage: benchDrain N [predict]"
  go (s ∷ _ ∷ _) with readMaybe 10 s
  ... | just n  = predictMode n
  ... | nothing = putStrLn "usage: benchDrain N [predict]"
  go [] = putStrLn "usage: benchDrain N [predict]"

main : Main
main = IO.run (getArgs >>= go)
