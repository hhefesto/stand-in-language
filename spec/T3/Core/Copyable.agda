------------------------------------------------------------------------
-- Explicitly witnessed copying. There is no catch-all Copyable constructor:
-- ordinary sums and lists remain affine, while bang uses core contraction.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Core.Copyable where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value

data Copyable : Ty → Set where
  copy-unit : Copyable unit
  copy-nat  : Copyable nat
  copy-prod : {A B : Ty} → Copyable A → Copyable B → Copyable (A ⊗ B)
  copy-bang : {A : Ty} → Copyable (! A)

-- Rearrange component copies without introducing contraction.
shuffle : {A B : Ty} → ((A ⊗ A) ⊗ (B ⊗ B)) ⇨ ((A ⊗ B) ⊗ (A ⊗ B))
shuffle = assocS
        ∘S (unassocS ⊗S idS)
        ∘S ((idS ⊗S swapS) ⊗S idS)
        ∘S unassocS
        ∘S (idS ⊗S unassocS)
        ∘S assocS

copyS : {A : Ty} → Copyable A → A ⇨ (A ⊗ A)
copyS copy-unit       = lunitS
copyS copy-nat        = dupNatS
copyS (copy-prod p q) = shuffle ∘S (copyS p ⊗S copyS q)
copyS copy-bang       = dupS

copyS-correct : {A : Ty} → (p : Copyable A) → (a : ⟦ A ⟧T)
              → ⟦ copyS p ⟧V a ≡ (a , a)
copyS-correct copy-unit       a       = refl
copyS-correct copy-nat        a       = refl
copyS-correct (copy-prod p q) (a , b)
  rewrite copyS-correct p a | copyS-correct q b = refl
copyS-correct copy-bang       a       = refl
