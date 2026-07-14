------------------------------------------------------------------------
-- T3.Sem.Length — the M5 attempt: an intrinsic denotation for `!`
-- (telomare2 §16 debt 1), timeboxed.  OUTCOME: the arbiter FIRED.
--
-- Candidate model (Dal Lago–Hofmann, "Quantitative models and implicit
-- complexity" [cited]): length spaces over a resource monoid — every
-- morphism comes with a majorizing realizer cost; `!A` has the same
-- points as A but a genuinely different majorization structure, and
-- dupS exists BECAUSE of the bang structure.
--
-- The simplest candidate monoid over telomare3's word-size model
-- (T3.Core.Ty.sizeT) is ADDITIVE majorization: a morphism is c-realized
-- when output size ≤ c + input size.  This module machine-checks that
-- the candidate FAILS the arbiter test the charter reserved for it
-- (§14.1): the fuel-carrying iteration `iterS` — with the pragmatic
-- typing — admits NO additive realizer: a list-building step grows the
-- output linearly in the fuel, while the input (fuel is one machine
-- word) stays constant ('iterS-not-additive').
--
-- Consequence, recorded as the M5 DESIGN AXIOM (documented, not
-- postulated): an intrinsic length-space denotation for telomare3's `!`
-- requires a resource monoid with genuine elementary growth (Dal Lago–
-- Hofmann's polynomial/elementary monoids), whose Agda formalization is
-- deferred; until then `!` has no intrinsic denotation in this spec and
-- the graded semantics (T3.Sem.Graded) remains the sole cost layer —
-- telomare2's position, now held consciously WITH a machine-checked
-- reason.  Nothing downstream depends on this module (charter §2.7).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Sem.Length where

open import Data.Nat             using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; +-suc; +-monoˡ-≤;
                                        +-monoʳ-≤; n≤1+n)
open import Data.Product         using (_×_; _,_; Σ)
open import Data.List            using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary     using (¬_)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value

-- Additive majorization over the word-size model: output size bounded by
-- a constant plus input size.
AdditivelyRealized : (A B : Ty) → (⟦ A ⟧T → ⟦ B ⟧T) → Set
AdditivelyRealized A B f =
  Σ ℕ (λ c → ∀ a → sizeT B (f a) ≤ c + sizeT A a)

-- The witness iteration: each step conses one element.
stepL : listT nat ⇨ listT nat
stepL = consS ∘S (constS 0 ⊗S idS) ∘S lunitS

grow : (nat ⊗ ! (listT nat)) ⇨ ! (listT nat)
grow = iterS stepL

private
  L : Ty
  L = listT nat

  -- iterating stepL n times adds 2n words.
  sizeLB : ∀ n (a : ⟦ L ⟧T)
         → n + n + sizeT L a ≤ sizeT L (iterV n ⟦ stepL ⟧V a)
  sizeLB zero    a = ≤-refl
  sizeLB (suc n) a =
    subst (_≤ sizeT L (iterV n ⟦ stepL ⟧V (0 ∷ a)))
          (sym eq)
          (sizeLB n (0 ∷ a))
    where
      s = sizeT L a
      eq : suc n + suc n + s ≡ n + n + suc (suc s)
      eq = trans (cong (_+ s) (cong suc (+-suc n n)))
                 (sym (trans (+-suc (n + n) (suc s))
                             (cong suc (+-suc (n + n) s))))

  -- suc c + suc c + 1 ≰ c + 2
  absurd-arith : ∀ c → ¬ (suc c + suc c + 1 ≤ c + 2)
  absurd-arith zero (s≤s (s≤s ()))
  absurd-arith (suc c) (s≤s p) =
    absurd-arith c (≤-trans (weaken c) p)
    where
      weaken : ∀ c → suc c + suc c + 1 ≤ suc c + suc (suc c) + 1
      weaken c = +-monoˡ-≤ 1 (+-monoʳ-≤ (suc c) (n≤1+n (suc c)))

-- THE ARBITER RESULT: iterS with the pragmatic typing admits no additive
-- realizer.  (Instantiate any claimed constant c at fuel = suc c over
-- the empty list: the output holds 2c+3 words, the bound allows c+2.)
iterS-not-additive :
  ¬ AdditivelyRealized (nat ⊗ ! L) (! L) ⟦ grow ⟧V
iterS-not-additive (c , h) =
  absurd-arith c (≤-trans lower (h (suc c , [])))
  where
    lower : suc c + suc c + 1 ≤ sizeT (! L) (⟦ grow ⟧V (suc c , []))
    lower = sizeLB (suc c) []
