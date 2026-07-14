------------------------------------------------------------------------
-- T3.Examples.Budgets — M4's gate: budgets compute by refl, and the
-- VALIDATION.md behaviors S1/S2/S3 are definitional consequences.
--
-- Oracle mapping (VALIDATION.md, telomare1 churchK): telomare1's size
-- k = semantic bound + 2 (S1 — the church-tower elaboration constant of
-- telomare1, measured there; our budget IS the semantic bound).
--   * dPow shape: bounds 3,4,6  ↦  churchK 5,6,8   (VALIDATION §4)
--   * whoWon strata: bounds 8,3 ↦  churchK 10,5    (§3 k-groups
--     {10,10}{5,5,5}; the {3} group is a 1-bound site: 1+2)
--   * pow on church literals: no fuel-carrying sites — no budgets
--     (the documented sizing-invisibility divergence, §6)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Examples.Budgets where

open import Data.Nat     using (ℕ)
open import Data.Maybe   using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Abstract

-- ── S1: a single site's budget is its fuel bound ────────────────────────────

-- double (Examples.Basics): fuel = the input nat.
double : nat ⇨ ! nat
double = iterS (sucS ∘S sucS) ∘S (idS ⊗S boxValS (constS 0)) ∘S runitS

double-budget :
  proj₁ (transfer double (natLE 5))
  ≡ binB (recB (just 5) (binB tipB tipB))
         (binB (binB tipB tipB) tipB)
double-budget = refl

double-shape : proj₂ (transfer double (natLE 5)) ≡ bangS (natLE 10)
double-shape = refl

-- ── S2: an inner site is budgeted at the max over ALL outer iterations ──────

-- A depth-2 tower where the inner fuel GROWS each outer round (the dPow
-- mechanism): state (fuel , !acc); each outer step bumps the fuel and
-- re-runs the inner iteration with it.
towerStep : (nat ⊗ ! nat) ⇨ (nat ⊗ ! nat)
towerStep = (sucS ⊗S iterS sucS) ∘S assocS ∘S (dupNatS ⊗S idS)

tower : (nat ⊗ ! (nat ⊗ ! nat)) ⇨ ! (nat ⊗ ! nat)
tower = iterS towerStep

tower-depth : depth tower ≡ 2
tower-depth = refl

-- Outer fuel 3, inner fuel starting at 4: the inner site sees fuels
-- 4, 5, 6 across the three outer unrollings — its budget is their max, 6
-- (Girard's level-by-level bound as the DEFINITION: aiter joins budgets
-- over every unrolling).  Bounds (3, 6) ↦ churchK (5, 8): the outer and
-- innermost dPow numbers.
tower-in : Shape (nat ⊗ ! (nat ⊗ ! nat))
tower-in = pairS (natLE 3) (bangS (pairS (natLE 4) (bangS (natLE 0))))

tower-budget :
  proj₁ (transfer tower tower-in)
  ≡ recB (just 3)
      (binB (binB tipB (recB (just 6) tipB))
            (binB tipB (binB tipB tipB)))
tower-budget = refl

-- ── S3: a compound producer is evaluated before its consumer is sized ───────

-- The consumer's fuel is the PRODUCER's output bound: doubling 3 gives 6.
prod : nat ⇨ nat
prod = addS ∘S dupNatS

consumerAfterProducer : (nat ⊗ ! nat) ⇨ ! nat
consumerAfterProducer = iterS sucS ∘S (prod ⊗S idS)

s3-budget :
  proj₁ (transfer consumerAfterProducer
          (pairS (natLE 3) (bangS (natLE 0))))
  ≡ binB (recB (just 6) tipB) (binB (binB tipB tipB) tipB)
s3-budget = refl

-- ── whoWon strata: fold over 8 rows, each row folding 3 cells ───────────────

rowStep : (! nat ⊗ listT nat) ⇨ ! nat
rowStep = foldS addS ∘S swapS

whoWonish : (listT (listT nat) ⊗ ! (! nat)) ⇨ ! (! nat)
whoWonish = foldS rowStep

whoWonish-depth : depth whoWonish ≡ 2
whoWonish-depth = refl

whoWonish-in : Shape (listT (listT nat) ⊗ ! (! nat))
whoWonish-in = pairS (listS 8 (listS 3 (natLE 2))) (bangS (bangS (natLE 0)))

-- Bounds (8, 3) ↦ churchK (10, 5): whoWon's row and position strata.
whoWonish-budget :
  proj₁ (transfer whoWonish whoWonish-in)
  ≡ recB (just 8) (binB (recB (just 3) tipB) tipB)
whoWonish-budget = refl

-- ── pow on church literals: no fuel-carrying sites, no budgets ──────────────

churchArith : nat ⇨ nat
churchArith = addS ∘S dupNatS ∘S sucS

churchArith-budget :
  proj₁ (transfer churchArith (natLE 7)) ≡ binB tipB (binB tipB tipB)
churchArith-budget = refl

-- ── unbounded fuel is a NOTICE (⊤ budget), never a rejection ────────────────

unsizable-budget :
  proj₁ (transfer (iterS sucS) topS) ≡ recB nothing tipB
unsizable-budget = refl
