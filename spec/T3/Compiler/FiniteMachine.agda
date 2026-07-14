------------------------------------------------------------------------
-- The generic natural-key partition used by the finite-machine compiler.
-- Both branches reconstruct the consumed input, so dispatch is affine.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Compiler.FiniteMachine where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value

partitionNat : ℕ → nat ⇨ (nat ⊕ nat)
partitionNat zero =
  caseS (inlS ∘S constS zero) (inrS ∘S sucS) ∘S natOutS
partitionNat (suc k) =
  caseS (inrS ∘S constS zero)
        ((caseS (inlS ∘S sucS) (inrS ∘S sucS) ∘S partitionNat k))
  ∘S natOutS

forgetChoice : {A : Ty} → (A ⊕ A) ⇨ A
forgetChoice = caseS idS idS

partitionNat-preserves : (k n : ℕ)
                       → ⟦ forgetChoice ∘S partitionNat k ⟧V n ≡ n
partitionNat-preserves zero    zero    = refl
partitionNat-preserves zero    (suc n) = refl
partitionNat-preserves (suc k) zero    = refl
partitionNat-preserves (suc k) (suc n)
  with ⟦ partitionNat k ⟧V n | partitionNat-preserves k n
... | inj₁ x | p = cong suc p
... | inj₂ x | p = cong suc p
