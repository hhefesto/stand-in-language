------------------------------------------------------------------------
-- T3.Sem.Exec — the fuel-metered execution semantics ⟦_⟧K.
--
-- TelM may halt when fuel runs
-- out (never diverges); T3.Adequacy proves it PRECISE against the work
-- instance of the graded semantics: run with the computed budget and you
-- finish with exactly 0 fuel left.
--
-- CLOSURES: the machine value of A ⊸ B is a fuel-monadic function —
-- KVal (A ⊸ B) = KVal A → TelM (KVal B) — so a closure body's fuel is
-- consumed at each apply.  applyS consumes ONE step-tel of its own,
-- mirroring workAlg's applyT = 1, then runs the body.
--
-- Consistency discipline: ⟦_⟧K consumes a step-tel exactly where workAlg
-- charges (natOut looks, applies, taken loop steps) and nowhere else —
-- guardS and whileS probes charge 0 work, so they consume no fuel of
-- their own (the probe's dup-grade cost is a different algebra's
-- business).
--
-- The loop helpers are public: T3.Adequacy's proofs name them.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Sem.Exec where

open import Data.Nat     using (ℕ; zero; suc; _+_)
open import Data.Maybe   using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value using (guardV)

Tel : Set
Tel = ℕ

-- Execution: may halt when fuel runs out (never diverges).
TelM : Set → Set
TelM A = Tel → Maybe (A × Tel)

return-tel : {A : Set} → A → TelM A
return-tel a g = just (a , g)

bind-tel : {A B : Set} → TelM A → (A → TelM B) → TelM B
bind-tel m f g = m g >>= λ { (a , g') → f a g' }

step-tel : {A : Set} → TelM A → TelM A
step-tel m zero    = nothing
step-tel m (suc g) = m g

infixr 0 _→K_
_→K_ : Set → Set → Set
A →K B = A → TelM B

iterT : {A : Set} → ℕ → (A →K A) → A →K A
iterT zero    _ a = return-tel a
iterT (suc n) f a = step-tel (bind-tel (f a) (iterT n f))

foldT : {A B : Set} → List A → ((B × A) →K B) → B →K B
foldT []       _ b = return-tel b
foldT (x ∷ xs) f b = step-tel (bind-tel (f (b , x)) (foldT xs f))

mapT : {A B : Set} → List A → (A →K B) → TelM (List B)
mapT []       _ = return-tel []
mapT (x ∷ xs) f = step-tel
  (bind-tel (f x) λ y →
   bind-tel (mapT xs f) λ ys →
   return-tel (y ∷ ys))

whileGoT : {A : Set} → ℕ → (A →K (⊤ ⊎ ⊤)) → (A →K A) → A → ⊤ ⊎ ⊤ → TelM A
whileT   : {A : Set} → ℕ → (A →K (⊤ ⊎ ⊤)) → (A →K A) → A →K A

whileGoT n t s a (inj₁ _) = return-tel a
whileGoT n t s a (inj₂ _) = step-tel (bind-tel (s a) (whileT n t s))

whileT zero    t s a = return-tel a
whileT (suc n) t s a = bind-tel (t a) (whileGoT n t s a)

-- Machine values: fuel-monadic at arrows, structural elsewhere.
KVal : Ty → Set
KVal unit      = ⊤
KVal nat       = ℕ
KVal (A ⊗ B)   = KVal A × KVal B
KVal (A ⊕ B)   = KVal A ⊎ KVal B
KVal (listT A) = List (KVal A)
KVal (! A)     = KVal A
KVal (A ⊸ B)   = KVal A → TelM (KVal B)

⟦_⟧K : {A B : Ty} → A ⇨ B → KVal A →K KVal B
⟦ idS        ⟧K a = return-tel a
⟦ g ∘S f     ⟧K a = bind-tel (⟦ f ⟧K a) ⟦ g ⟧K
⟦ f ⊗S g     ⟧K (a , c) = bind-tel (⟦ f ⟧K a) λ b →
                           bind-tel (⟦ g ⟧K c) λ d →
                           return-tel (b , d)
⟦ swapS      ⟧K (a , b) = return-tel (b , a)
⟦ assocS     ⟧K ((a , b) , c) = return-tel (a , (b , c))
⟦ unassocS   ⟧K (a , (b , c)) = return-tel ((a , b) , c)
⟦ exlS       ⟧K (a , _) = return-tel a
⟦ exrS       ⟧K (_ , b) = return-tel b
⟦ weakS      ⟧K _ = return-tel tt
⟦ runitS     ⟧K a = return-tel (a , tt)
⟦ lunitS     ⟧K a = return-tel (tt , a)
⟦ inlS       ⟧K a = return-tel (inj₁ a)
⟦ inrS       ⟧K b = return-tel (inj₂ b)
⟦ caseS l r  ⟧K (inj₁ a) = ⟦ l ⟧K a
⟦ caseS l r  ⟧K (inj₂ b) = ⟦ r ⟧K b
⟦ distlS     ⟧K (a , inj₁ b) = return-tel (inj₁ (a , b))
⟦ distlS     ⟧K (a , inj₂ c) = return-tel (inj₂ (a , c))
⟦ nilS       ⟧K _ = return-tel []
⟦ consS      ⟧K (x , xs) = return-tel (x ∷ xs)
⟦ unconsS    ⟧K [] = return-tel (inj₁ tt)
⟦ unconsS    ⟧K (x ∷ xs) = return-tel (inj₂ (x , xs))
⟦ natOutS    ⟧K zero = step-tel (return-tel (inj₁ tt))
⟦ natOutS    ⟧K (suc n) = step-tel (return-tel (inj₂ n))
⟦ sucS       ⟧K n = return-tel (suc n)
⟦ addS       ⟧K (a , b) = return-tel (a + b)
⟦ constS k   ⟧K _ = return-tel k
⟦ dupNatS    ⟧K n = return-tel (n , n)
⟦ copyS _    ⟧K a = return-tel (a , a)
⟦ guardS t   ⟧K a = bind-tel (⟦ t ⟧K a) λ r → return-tel (guardV a r)
⟦ curryS f   ⟧K c = return-tel (λ a → ⟦ f ⟧K (c , a))
⟦ applyS     ⟧K (f , a) = step-tel (f a)
⟦ mapCS      ⟧K (f , xs) = mapT xs f
⟦ promoteS _ ⟧K a = return-tel a
⟦ dupS       ⟧K a = return-tel (a , a)
⟦ boxS f     ⟧K a = ⟦ f ⟧K a
⟦ boxValS f  ⟧K a = ⟦ f ⟧K a
⟦ mergeS     ⟧K p = return-tel p
⟦ mapS f     ⟧K xs = mapT xs ⟦ f ⟧K
⟦ iterS f    ⟧K (n , a) = iterT n ⟦ f ⟧K a
⟦ foldS f    ⟧K (xs , b) = foldT xs ⟦ f ⟧K b
⟦ whileS t s ⟧K (n , a) = whileT n ⟦ t ⟧K ⟦ s ⟧K a
