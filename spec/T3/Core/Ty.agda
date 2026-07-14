------------------------------------------------------------------------
-- T3.Core.Ty — objects of the Telomare core category.
--
-- Core object language.
--
-- Decision: box depth lives on
-- Ty — `!` is a type constructor — not on the judgment (A ⇨ⁿ B).
-- Judgment-indexing would make stratification local but infects every rule
-- for a locality gain whole-program inference does not need.
--
-- The load-bearing line is ⟦ ! A ⟧T = ⟦ A ⟧T: values do not see boxes.
-- The modality is cost/discipline-relevant, value-irrelevant.  In Telomare
-- this clause is upgraded to a functor identity by T3.Place (factorization
-- through erasure); the candidate *intrinsic* denotation for ! (length
-- spaces) is handled by T3.Sem.Length.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Core.Ty where

open import Data.Nat     using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)

data Ty : Set where
  unit  : Ty
  nat   : Ty
  _⊗_   : Ty → Ty → Ty
  _⊕_   : Ty → Ty → Ty
  listT : Ty → Ty
  !_    : Ty → Ty            -- the EAL exponential

infixl 5 _⊗_
infixl 4 _⊕_
infixr 6 !_

-- Values do not see boxes: ⟦!A⟧ = ⟦A⟧.
⟦_⟧T : Ty → Set
⟦ unit    ⟧T = ⊤
⟦ nat     ⟧T = ℕ
⟦ A ⊗ B   ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A ⊕ B   ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ listT A ⟧T = List ⟦ A ⟧T
⟦ ! A     ⟧T = ⟦ A ⟧T

-- Word model of value size (space and the dup grade charge in these units).
-- NB ⟦_⟧T is non-injective (⟦!A⟧T = ⟦A⟧T), so helpers over ⟦_⟧T need their
-- Ty argument EXPLICIT throughout the spec.
sizeT : (A : Ty) → ⟦ A ⟧T → ℕ
sizeT unit      _        = 1
sizeT nat       _        = 1
sizeT (A ⊗ B)   (a , b)  = sizeT A a + sizeT B b
sizeT (A ⊕ B)   (inj₁ a) = suc (sizeT A a)
sizeT (A ⊕ B)   (inj₂ b) = suc (sizeT B b)
sizeT (listT A) []       = 1
sizeT (listT A) (x ∷ xs) = suc (sizeT A x + sizeT (listT A) xs)
sizeT (! A)     a        = sizeT A a
