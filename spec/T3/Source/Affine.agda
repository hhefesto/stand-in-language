------------------------------------------------------------------------
-- Central resource rules for the pointful source elaborator.
-- This models typed elaboration after parsing; it is not a parser proof.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Source.Affine where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)

infixr 5 _×T_ _+T_

data Ty : Set where
  unit nat : Ty
  _×T_ _+T_ : Ty → Ty → Ty

Ctx = List Ty

data Expr : Set where
  var   : ℕ → Expr
  unitE : Expr
  natE  : ℕ → Expr
  pair  : Expr → Expr → Expr
  letE  : Expr → Expr → Expr
  copy  : Expr → Expr
  caseE : Expr → Expr → Expr → Expr

data Lookup : Ctx → ℕ → Ty → Set where
  here  : {Γ : Ctx} {A : Ty} → Lookup (A ∷ Γ) zero A
  there : {Γ : Ctx} {A B : Ty} {n : ℕ}
        → Lookup Γ n A → Lookup (B ∷ Γ) (suc n) A

-- Split assigns every affine input to at most one subexpression.
data Split : Ctx → Ctx → Ctx → Set where
  empty : Split [] [] []
  left  : {Γ Δ Θ : Ctx} {A : Ty}
        → Split Γ Δ Θ → Split (A ∷ Γ) (A ∷ Δ) Θ
  right : {Γ Δ Θ : Ctx} {A : Ty}
        → Split Γ Δ Θ → Split (A ∷ Γ) Δ (A ∷ Θ)
  drop  : {Γ Δ Θ : Ctx} {A : Ty}
        → Split Γ Δ Θ → Split (A ∷ Γ) Δ Θ

data Copyable : Ty → Set where
  copyUnit : Copyable unit
  copyNat  : Copyable nat
  copyProd : {A B : Ty} → Copyable A → Copyable B → Copyable (A ×T B)

infix 4 _⊢_∶_

data _⊢_∶_ : Ctx → Expr → Ty → Set where
  varRule  : {Γ : Ctx} {A : Ty} {n : ℕ}
           → Lookup Γ n A → Γ ⊢ var n ∶ A
  unitLit  : {Γ : Ctx} → Γ ⊢ unitE ∶ unit
  natLit   : {Γ : Ctx} (n : ℕ) → Γ ⊢ natE n ∶ nat
  product  : {Γ Δ Θ : Ctx} {A B : Ty} {e f : Expr}
           → Split Γ Δ Θ → Δ ⊢ e ∶ A → Θ ⊢ f ∶ B
           → Γ ⊢ pair e f ∶ (A ×T B)
  letBind  : {Γ Δ Θ : Ctx} {A B : Ty} {e body : Expr}
           → Split Γ Δ Θ → Δ ⊢ e ∶ A → (A ∷ Θ) ⊢ body ∶ B
           → Γ ⊢ letE e body ∶ B
  explicitCopy : {Γ : Ctx} {A : Ty} {e : Expr}
               → Copyable A → Γ ⊢ e ∶ A
               → Γ ⊢ copy e ∶ (A ×T A)
  sumCase : {Γ : Ctx} {A B C : Ty} {e l r : Expr}
          → Γ ⊢ e ∶ (A +T B) → (A ∷ []) ⊢ l ∶ C → (B ∷ []) ⊢ r ∶ C
          → Γ ⊢ caseE e l r ∶ C
