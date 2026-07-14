------------------------------------------------------------------------
-- T3.Surface.Syntax — the cartesian surface category S.
--
-- What users write elaborates here (charter §2.2/§2.9): the core's
-- constructor set MINUS the entire EAL interface (no dupS/boxS/boxValS/
-- mergeS — no boxes exist at the surface), PLUS free contraction `dupU`
-- on every object (that is the cartesian-ness: the surface has fork).
-- Recursion is still fuel-carrying and first-order — totality is
-- manifest — but its type mentions no box: stratification is the CORE's
-- discipline, recovered by placement (T3.Place), never written by users.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Surface.Syntax where

open import Data.Nat using (ℕ)

open import T3.Surface.Ty

infixr 2 _⇨U_
infixr 9 _∘U_
infixr 3 _⊗U_

data _⇨U_ : UTy → UTy → Set where
  -- category
  idU      : {A : UTy} → A ⇨U A
  _∘U_     : {A B C : UTy} → B ⇨U C → A ⇨U B → A ⇨U C
  -- cartesian structure (dupU is what the core does NOT have)
  _⊗U_     : {A B C D : UTy} → A ⇨U B → C ⇨U D → (A ⊗ᵤ C) ⇨U (B ⊗ᵤ D)
  dupU     : {A : UTy} → A ⇨U (A ⊗ᵤ A)
  swapU    : {A B : UTy} → (A ⊗ᵤ B) ⇨U (B ⊗ᵤ A)
  assocU   : {A B C : UTy} → ((A ⊗ᵤ B) ⊗ᵤ C) ⇨U (A ⊗ᵤ (B ⊗ᵤ C))
  unassocU : {A B C : UTy} → (A ⊗ᵤ (B ⊗ᵤ C)) ⇨U ((A ⊗ᵤ B) ⊗ᵤ C)
  exlU     : {A B : UTy} → (A ⊗ᵤ B) ⇨U A
  exrU     : {A B : UTy} → (A ⊗ᵤ B) ⇨U B
  weakU    : {A : UTy} → A ⇨U unitᵤ
  runitU   : {A : UTy} → A ⇨U (A ⊗ᵤ unitᵤ)
  lunitU   : {A : UTy} → A ⇨U (unitᵤ ⊗ᵤ A)
  -- coproducts + distributivity
  inlU     : {A B : UTy} → A ⇨U (A ⊕ᵤ B)
  inrU     : {A B : UTy} → B ⇨U (A ⊕ᵤ B)
  caseU    : {A B C : UTy} → A ⇨U C → B ⇨U C → (A ⊕ᵤ B) ⇨U C
  distlU   : {A B C : UTy} → (A ⊗ᵤ (B ⊕ᵤ C)) ⇨U ((A ⊗ᵤ B) ⊕ᵤ (A ⊗ᵤ C))
  -- data
  nilU     : {A : UTy} → unitᵤ ⇨U listᵤ A
  consU    : {A : UTy} → (A ⊗ᵤ listᵤ A) ⇨U listᵤ A
  unconsU  : {A : UTy} → listᵤ A ⇨U (unitᵤ ⊕ᵤ (A ⊗ᵤ listᵤ A))
  natOutU  : natᵤ ⇨U (unitᵤ ⊕ᵤ natᵤ)
  sucU     : natᵤ ⇨U natᵤ
  addU     : (natᵤ ⊗ᵤ natᵤ) ⇨U natᵤ
  constU   : {A : UTy} → ℕ → A ⇨U natᵤ
  -- refinement guard
  guardU   : {A : UTy} → A ⇨U (unitᵤ ⊕ᵤ unitᵤ) → A ⇨U (A ⊕ᵤ unitᵤ)
  -- fuel-carrying recursion, box-free typing
  iterU    : {A : UTy} → A ⇨U A → (natᵤ ⊗ᵤ A) ⇨U A
  foldU    : {A B : UTy} → (B ⊗ᵤ A) ⇨U B → (listᵤ A ⊗ᵤ B) ⇨U B
  whileU   : {A : UTy} → A ⇨U (unitᵤ ⊕ᵤ unitᵤ) → A ⇨U A → (natᵤ ⊗ᵤ A) ⇨U A
