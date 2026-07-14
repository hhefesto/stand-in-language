------------------------------------------------------------------------
-- T3.Compiler.Direct — the first surface-to-core compiler slice.
--
-- Direct relates the box-free affine surface fragment to the matching core
-- term.  It deliberately has no rule for general dupU or any recursion:
-- those constructs require modal placement.  dupU at nat is admitted by
-- the measured atom exemption dupNatS.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Compiler.Direct where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value
open import T3.Surface.Ty
open import T3.Surface.Syntax
open import T3.Surface.Sem
open import T3.Place using (ε; ε-factor)

-- Canonical bang-free embedding used by the Haskell compiler endpoints.
liftU : UTy → Ty
liftU unitᵤ      = unit
liftU natᵤ       = nat
liftU (A ⊗ᵤ B)   = liftU A ⊗ liftU B
liftU (A ⊕ᵤ B)   = liftU A ⊕ liftU B
liftU (listᵤ A)  = listT (liftU A)

-- Successful direct elaboration evidence.  Indexing the source by the
-- erasure of the core endpoints makes the erasure law intrinsic.
data Direct : {A B : Ty} → strip A ⇨U strip B → A ⇨ B → Set where
  d-id      : {A : Ty} → Direct idU (idS {A})
  d-comp    : {A B C : Ty} {f : strip A ⇨U strip B} {g : strip B ⇨U strip C}
              {f′ : A ⇨ B} {g′ : B ⇨ C}
            → Direct g g′ → Direct f f′ → Direct (g ∘U f) (g′ ∘S f′)
  d-tensor  : {A B C D : Ty} {f : strip A ⇨U strip B} {g : strip C ⇨U strip D}
              {f′ : A ⇨ B} {g′ : C ⇨ D}
            → Direct f f′ → Direct g g′ → Direct (f ⊗U g) (f′ ⊗S g′)
  d-dupNat  : Direct dupU dupNatS
  d-swap    : {A B : Ty} → Direct swapU (swapS {A} {B})
  d-assoc   : {A B C : Ty} → Direct assocU (assocS {A} {B} {C})
  d-unassoc : {A B C : Ty} → Direct unassocU (unassocS {A} {B} {C})
  d-exl     : {A B : Ty} → Direct exlU (exlS {A} {B})
  d-exr     : {A B : Ty} → Direct exrU (exrS {A} {B})
  d-weak    : {A : Ty} → Direct weakU (weakS {A})
  d-runit   : {A : Ty} → Direct runitU (runitS {A})
  d-lunit   : {A : Ty} → Direct lunitU (lunitS {A})
  d-inl     : {A B : Ty} → Direct inlU (inlS {A} {B})
  d-inr     : {A B : Ty} → Direct inrU (inrS {A} {B})
  d-case    : {A B C : Ty} {l : strip A ⇨U strip C} {r : strip B ⇨U strip C}
              {l′ : A ⇨ C} {r′ : B ⇨ C}
            → Direct l l′ → Direct r r′ → Direct (caseU l r) (caseS l′ r′)
  d-distl   : {A B C : Ty} → Direct distlU (distlS {A} {B} {C})
  d-nil     : {A : Ty} → Direct nilU (nilS {A})
  d-cons    : {A : Ty} → Direct consU (consS {A})
  d-uncons  : {A : Ty} → Direct unconsU (unconsS {A})
  d-natOut  : Direct natOutU natOutS
  d-suc     : Direct sucU sucS
  d-add     : Direct addU addS
  d-const   : {A : Ty} (k : ℕ) → Direct (constU k) (constS {A} k)
  d-guard   : {A : Ty} {t : strip A ⇨U (unitᵤ ⊕ᵤ unitᵤ)}
              {t′ : A ⇨ (unit ⊕ unit)}
            → Direct t t′ → Direct (guardU t) (guardS t′)

-- Every successful direct elaboration erases to exactly its source term.
direct-erases : {A B : Ty} {f : strip A ⇨U strip B} {g : A ⇨ B}
              → Direct f g → ε g ≡ f
direct-erases d-id             = refl
direct-erases (d-comp dg df)   = cong₂ _∘U_ (direct-erases dg) (direct-erases df)
direct-erases (d-tensor df dg) = cong₂ _⊗U_ (direct-erases df) (direct-erases dg)
direct-erases d-dupNat         = refl
direct-erases d-swap           = refl
direct-erases d-assoc          = refl
direct-erases d-unassoc        = refl
direct-erases d-exl            = refl
direct-erases d-exr            = refl
direct-erases d-weak           = refl
direct-erases d-runit          = refl
direct-erases d-lunit          = refl
direct-erases d-inl            = refl
direct-erases d-inr            = refl
direct-erases (d-case dl dr)   = cong₂ caseU (direct-erases dl) (direct-erases dr)
direct-erases d-distl          = refl
direct-erases d-nil            = refl
direct-erases d-cons           = refl
direct-erases d-uncons         = refl
direct-erases d-natOut         = refl
direct-erases d-suc            = refl
direct-erases d-add            = refl
direct-erases (d-const _)      = refl
direct-erases (d-guard dt)     = cong guardU (direct-erases dt)

-- The direct compiler inherits semantic preservation from core erasure.
direct-factor : {A B : Ty} {f : strip A ⇨U strip B} {g : A ⇨ B}
              → Direct f g → (a : ⟦ A ⟧T)
              → stripV B (⟦ g ⟧V a) ≡ ⟦ f ⟧VS (stripV A a)
direct-factor {A} {f = f} {g = g} d a =
  trans (ε-factor g a)
        (cong (λ h → ⟦ h ⟧VS (stripV A a)) (direct-erases d))

direct-addTwice : Direct (addU ∘U dupU) (addS ∘S dupNatS)
direct-addTwice = d-comp d-add d-dupNat
