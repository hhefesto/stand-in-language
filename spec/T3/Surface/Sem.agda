------------------------------------------------------------------------
-- T3.Surface.Sem — the surface value semantics ⟦_⟧VS : S → Set.
--
-- The extensional layer (charter §2.2): everything writable at the
-- surface denotes a plain total function; nothing here is ever rejected.
-- Tier 2 realizes exactly this semantics (fuel-metered, M7).  The loop
-- and guard helpers are shared with the core semantics (T3.Sem.Value) —
-- one meaning, two syntaxes, related by erasure (T3.Place).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Surface.Sem where

open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)

open import T3.Surface.Ty
open import T3.Surface.Syntax
open import T3.Sem.Value using (mapV; iterV; foldV; whileV; guardV)

⟦_⟧VS : {A B : UTy} → A ⇨U B → ⟦ A ⟧U → ⟦ B ⟧U
⟦ idU        ⟧VS a = a
⟦ g ∘U f     ⟧VS a = ⟦ g ⟧VS (⟦ f ⟧VS a)
⟦ f ⊗U g     ⟧VS (a , c) = (⟦ f ⟧VS a , ⟦ g ⟧VS c)
⟦ dupU       ⟧VS a = (a , a)
⟦ swapU      ⟧VS (a , b) = (b , a)
⟦ assocU     ⟧VS ((a , b) , c) = (a , (b , c))
⟦ unassocU   ⟧VS (a , (b , c)) = ((a , b) , c)
⟦ exlU       ⟧VS (a , _) = a
⟦ exrU       ⟧VS (_ , b) = b
⟦ weakU      ⟧VS _ = tt
⟦ runitU     ⟧VS a = (a , tt)
⟦ lunitU     ⟧VS a = (tt , a)
⟦ inlU       ⟧VS a = inj₁ a
⟦ inrU       ⟧VS b = inj₂ b
⟦ caseU l r  ⟧VS (inj₁ a) = ⟦ l ⟧VS a
⟦ caseU l r  ⟧VS (inj₂ b) = ⟦ r ⟧VS b
⟦ distlU     ⟧VS (a , inj₁ b) = inj₁ (a , b)
⟦ distlU     ⟧VS (a , inj₂ c) = inj₂ (a , c)
⟦ nilU       ⟧VS _ = []
⟦ consU      ⟧VS (x , xs) = x ∷ xs
⟦ unconsU    ⟧VS [] = inj₁ tt
⟦ unconsU    ⟧VS (x ∷ xs) = inj₂ (x , xs)
⟦ natOutU    ⟧VS zero = inj₁ tt
⟦ natOutU    ⟧VS (suc n) = inj₂ n
⟦ sucU       ⟧VS n = suc n
⟦ addU       ⟧VS (a , b) = a + b
⟦ constU k   ⟧VS _ = k
⟦ guardU t   ⟧VS a = guardV a (⟦ t ⟧VS a)
⟦ mapU f     ⟧VS xs = mapV ⟦ f ⟧VS xs
⟦ iterU f    ⟧VS (n , a) = iterV n ⟦ f ⟧VS a
⟦ foldU f    ⟧VS (xs , b) = foldV xs ⟦ f ⟧VS b
⟦ whileU t s ⟧VS (n , a) = whileV n ⟦ t ⟧VS ⟦ s ⟧VS a
