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
  _⊸_   : Ty → Ty → Ty       -- affine closures: applied at most once

infixl 5 _⊗_
infixl 4 _⊕_
infixr 6 !_
infixr 3 _⊸_

-- Values do not see boxes: ⟦!A⟧ = ⟦A⟧.  Closures denote the semantic
-- function space — totality of closure evaluation is definitional.  The
-- Haskell mirror defunctionalizes (code + typed environment); agreement
-- is re-checked pointwise by its tests.
⟦_⟧T : Ty → Set
⟦ unit    ⟧T = ⊤
⟦ nat     ⟧T = ℕ
⟦ A ⊗ B   ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A ⊕ B   ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ listT A ⟧T = List ⟦ A ⟧T
⟦ ! A     ⟧T = ⟦ A ⟧T
⟦ A ⊸ B   ⟧T = ⟦ A ⟧T → ⟦ B ⟧T

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
sizeT (A ⊸ B)   _        = 1
  -- Pointer model.  Exact where duplication is actually possible: only
  -- CLOSED closures are promotable/duplicable, and a closed-closure
  -- duplicate is one code pointer.  Documented undercount for probes on
  -- linear closures with environments (design/CLOSURES.md; revisit at R3).

-- Structural copy evidence: which types admit a costed data copy (the
-- copyS primitive in T3.Core.Syntax, charged sizeT by the dup grade).
-- Every first-order data type is copyable — deliberately: duplication of
-- DATA is legal wherever it is priced.  There is NO arrow case: a
-- closure is suspended computation, and duplicating computation goes
-- through the ! modality (dupS on ! (A ⊸ B)), never through copyS.
-- That absence is the modal rule.
-- Bang-free, arrow-free first-order data: the license for R2 data
-- promotion (promoteS in T3.Core.Syntax).  Deliberately NOT Copyable:
-- Copyable (! A) exists, and promotion at ! A would be dig — the
-- operator whose absence fixes box depth.  Ground rules ! out
-- structurally, so no dig arises by composition.
data Ground : Ty → Set where
  ground-unit : Ground unit
  ground-nat  : Ground nat
  ground-prod : {A B : Ty} → Ground A → Ground B → Ground (A ⊗ B)
  ground-sum  : {A B : Ty} → Ground A → Ground B → Ground (A ⊕ B)
  ground-list : {A : Ty} → Ground A → Ground (listT A)

data Copyable : Ty → Set where
  copy-unit : Copyable unit
  copy-nat  : Copyable nat
  copy-prod : {A B : Ty} → Copyable A → Copyable B → Copyable (A ⊗ B)
  copy-sum  : {A B : Ty} → Copyable A → Copyable B → Copyable (A ⊕ B)
  copy-list : {A : Ty} → Copyable A → Copyable (listT A)
  copy-bang : {A : Ty} → Copyable (! A)
