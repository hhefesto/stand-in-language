------------------------------------------------------------------------
-- T3.Sem.Value — the value denotation ⟦_⟧V (the specification).
--
-- A plain total function; totality
-- is Agda's termination checker.  Boxes are invisible (⟦!A⟧T = ⟦A⟧T), so
-- dupS is honest duplication and boxS/boxValS are identities on values.
--
-- The iteration/guard helpers are written -go style (no `with`) so they
-- stay definitionally transparent to the graded and execution semantics'
-- proofs (T3.Adequacy case-splits on the same scrutinees).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Sem.Value where

open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)

open import T3.Core.Ty
open import T3.Core.Syntax

-- Exported helpers (T3.Sem.Graded's value-coherence lemma relates its own
-- loops to these).
iterV : {A : Set} → ℕ → (A → A) → A → A
iterV zero    f a = a
iterV (suc n) f a = iterV n f (f a)

foldV : {A B : Set} → List A → (B × A → B) → B → B
foldV []       f b = b
foldV (x ∷ xs) f b = foldV xs f (f (b , x))

mapV : {A B : Set} → (A → B) → List A → List B
mapV f []       = []
mapV f (x ∷ xs) = f x ∷ mapV f xs

-- guard output: pass the input through on inj₁, error on inj₂.
guardOut : {A E : Set} → A → ⊤ ⊎ ⊤ → A ⊎ E → A ⊎ E
guardOut a (inj₁ _) _ = inj₁ a
guardOut a (inj₂ _) e = e

guardV : {A : Set} → A → ⊤ ⊎ ⊤ → A ⊎ ⊤
guardV a r = guardOut a r (inj₂ tt)

whileV-go : {A : Set} → ℕ → (A → ⊤ ⊎ ⊤) → (A → A) → A → ⊤ ⊎ ⊤ → A
whileV : {A : Set} → ℕ → (A → ⊤ ⊎ ⊤) → (A → A) → A → A

whileV-go n t s a (inj₁ _) = a
whileV-go n t s a (inj₂ _) = whileV n t s (s a)

whileV zero    t s a = a
whileV (suc n) t s a = whileV-go n t s a (t a)

-- bounded higher-order recursion.  recur is the semantic function `recV n`
-- (this recursion one fuel lower); termination is the structural decrease
-- of the fuel, even though recur is handed to the arbitrary body `r`.
recV-go : {A B : Set} → ℕ → (A → ⊤ ⊎ ⊤) → ((A → B) × A → B) → (A → B)
        → A → ⊤ ⊎ ⊤ → B
recV : {A B : Set} → ℕ → (A → ⊤ ⊎ ⊤) → ((A → B) × A → B) → (A → B) → A → B

recV-go n t r l a (inj₁ _) = l a
recV-go n t r l a (inj₂ _) = r ((λ y → recV n t r l y) , a)

recV zero    t r l a = l a
recV (suc n) t r l a = recV-go n t r l a (t a)

⟦_⟧V : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ⟦ B ⟧T
⟦ idS        ⟧V a = a
⟦ g ∘S f     ⟧V a = ⟦ g ⟧V (⟦ f ⟧V a)
⟦ f ⊗S g     ⟧V (a , c) = (⟦ f ⟧V a , ⟦ g ⟧V c)
⟦ swapS      ⟧V (a , b) = (b , a)
⟦ assocS     ⟧V ((a , b) , c) = (a , (b , c))
⟦ unassocS   ⟧V (a , (b , c)) = ((a , b) , c)
⟦ exlS       ⟧V (a , _) = a
⟦ exrS       ⟧V (_ , b) = b
⟦ weakS      ⟧V _ = tt
⟦ runitS     ⟧V a = (a , tt)
⟦ lunitS     ⟧V a = (tt , a)
⟦ inlS       ⟧V a = inj₁ a
⟦ inrS       ⟧V b = inj₂ b
⟦ caseS l r  ⟧V (inj₁ a) = ⟦ l ⟧V a
⟦ caseS l r  ⟧V (inj₂ b) = ⟦ r ⟧V b
⟦ distlS     ⟧V (a , inj₁ b) = inj₁ (a , b)
⟦ distlS     ⟧V (a , inj₂ c) = inj₂ (a , c)
⟦ nilS       ⟧V _ = []
⟦ consS      ⟧V (x , xs) = x ∷ xs
⟦ unconsS    ⟧V [] = inj₁ tt
⟦ unconsS    ⟧V (x ∷ xs) = inj₂ (x , xs)
⟦ natOutS    ⟧V zero = inj₁ tt
⟦ natOutS    ⟧V (suc n) = inj₂ n
⟦ sucS       ⟧V n = suc n
⟦ addS       ⟧V (a , b) = a + b
⟦ constS k   ⟧V _ = k
⟦ dupNatS    ⟧V n = (n , n)
⟦ copyS _    ⟧V a = (a , a)
⟦ guardS t   ⟧V a = guardV a (⟦ t ⟧V a)
⟦ curryS f   ⟧V c = λ a → ⟦ f ⟧V (c , a)
⟦ applyS     ⟧V (f , a) = f a
⟦ mapCS      ⟧V (f , xs) = mapV f xs
⟦ iterCS     ⟧V (f , (n , a)) = iterV n f a
⟦ foldCS     ⟧V (f , (xs , b)) = foldV xs f b
⟦ whileCS    ⟧V (t , (s , (n , a))) = whileV n t s a
⟦ promoteS _ ⟧V a = a               -- values don't see boxes
⟦ dupS       ⟧V a = (a , a)
⟦ boxS f     ⟧V a = ⟦ f ⟧V a
⟦ boxValS f  ⟧V a = ⟦ f ⟧V a
⟦ mergeS     ⟧V p = p
⟦ mapS f     ⟧V xs = mapV ⟦ f ⟧V xs
⟦ iterS f    ⟧V (n , a) = iterV n ⟦ f ⟧V a
⟦ foldS f    ⟧V (xs , b) = foldV xs ⟦ f ⟧V b
⟦ whileS t s ⟧V (n , a) = whileV n ⟦ t ⟧V ⟦ s ⟧V a
⟦ recS t r l ⟧V (n , a) = recV n ⟦ t ⟧V ⟦ r ⟧V ⟦ l ⟧V a
