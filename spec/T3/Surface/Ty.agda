------------------------------------------------------------------------
-- T3.Surface.Ty — box-free surface objects and the type-level erasure.
--
-- The surface category S (charter §2.2) is CARTESIAN: users never write a
-- box, and surface types have no `!`.  `strip` erases core types down to
-- surface types; `stripV` is its action on values.  Because ⟦!A⟧T = ⟦A⟧T,
-- stripV forgets no information — it re-indexes the same data, and the
-- factorization theorem (T3.Place) says the value semantics commutes with
-- it: decorations are semantically invisible AS A FUNCTOR IDENTITY.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Surface.Ty where

open import Data.Nat     using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import T3.Core.Ty

data UTy : Set where
  unitᵤ : UTy
  natᵤ  : UTy
  _⊗ᵤ_  : UTy → UTy → UTy
  _⊕ᵤ_  : UTy → UTy → UTy
  listᵤ : UTy → UTy
  _⊸ᵤ_  : UTy → UTy → UTy

infixl 5 _⊗ᵤ_
infixl 4 _⊕ᵤ_
infixr 3 _⊸ᵤ_

⟦_⟧U : UTy → Set
⟦ unitᵤ   ⟧U = ⊤
⟦ natᵤ    ⟧U = ℕ
⟦ A ⊗ᵤ B  ⟧U = ⟦ A ⟧U × ⟦ B ⟧U
⟦ A ⊕ᵤ B  ⟧U = ⟦ A ⟧U ⊎ ⟦ B ⟧U
⟦ listᵤ A ⟧U = List ⟦ A ⟧U
⟦ A ⊸ᵤ B  ⟧U = ⟦ A ⟧U → ⟦ B ⟧U

-- Type-level erasure: forget the boxes.
strip : Ty → UTy
strip unit      = unitᵤ
strip nat       = natᵤ
strip (A ⊗ B)   = strip A ⊗ᵤ strip B
strip (A ⊕ B)   = strip A ⊕ᵤ strip B
strip (listT A) = listᵤ (strip A)
strip (! A)     = strip A
strip (A ⊸ B)   = strip A ⊸ᵤ strip B

-- Value-level erasure: the identity in disguise (Agda cannot see
-- ⟦ A ⟧T ≡ ⟦ strip A ⟧U definitionally, so we transport structurally).
-- At arrows the transport needs the mutual inverse unstripV; the pair is
-- an identity re-indexing at every first-order layer.
stripV   : (A : Ty) → ⟦ A ⟧T → ⟦ strip A ⟧U
unstripV : (A : Ty) → ⟦ strip A ⟧U → ⟦ A ⟧T

stripV unit      tt       = tt
stripV nat       n        = n
stripV (A ⊗ B)   (a , b)  = (stripV A a , stripV B b)
stripV (A ⊕ B)   (inj₁ a) = inj₁ (stripV A a)
stripV (A ⊕ B)   (inj₂ b) = inj₂ (stripV B b)
stripV (listT A) []       = []
stripV (listT A) (x ∷ xs) = stripV A x ∷ stripV (listT A) xs
stripV (! A)     a        = stripV A a
stripV (A ⊸ B)   f        = λ u → stripV B (f (unstripV A u))

unstripV unit      tt       = tt
unstripV nat       n        = n
unstripV (A ⊗ B)   (a , b)  = (unstripV A a , unstripV B b)
unstripV (A ⊕ B)   (inj₁ a) = inj₁ (unstripV A a)
unstripV (A ⊕ B)   (inj₂ b) = inj₂ (unstripV B b)
unstripV (listT A) []       = []
unstripV (listT A) (x ∷ xs) = unstripV A x ∷ unstripV (listT A) xs
unstripV (! A)     a        = unstripV A a
unstripV (A ⊸ B)   g        = λ a → unstripV B (g (stripV A a))

-- On the verdict type of tests, erasure is literally the identity.
strip2 : (r : ⊤ ⊎ ⊤) → stripV (unit ⊕ unit) r ≡ r
strip2 (inj₁ tt) = refl
strip2 (inj₂ tt) = refl
