------------------------------------------------------------------------
-- T3.Examples.Basics — worked examples; every grade computes by refl.
--
-- Each named fact here computes through the consolidated graded semantics and
-- becomes a Haskell test vector 1:1 by name (test/SpecVectors.hs).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Examples.Basics where

open import Data.Nat     using (ℕ)
open import Data.Maybe   using (just)
open import Data.Product using (_,_; proj₁)
open import Data.Sum     using (inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value
open import T3.Sem.Graded
open import T3.Sem.Exec
open import T3.Adequacy

-- ── core examples through ⟦_⟧G ──────────────────────────────────────────────

-- double n = iterate (+2) n times from a boxed 0.  n is consumed ONCE (as
-- fuel); the seed is a closed value, boxed by empty-context promotion.
-- Fully affine: dup grade 0.
double : nat ⇨ ! nat
double = iterS (sucS ∘S sucS) ∘S (idS ⊗S boxValS (constS 0)) ∘S runitS

double-val : ⟦ double ⟧V 5 ≡ 10
double-val = refl

double-cost : work double 5 ≡ 5                  -- 1 tel per iteration
double-cost = refl

double-dup : dupGrade double 5 ≡ 0               -- affine by construction
double-dup = refl

double-depth : depth double ≡ 1                  -- result one level down
double-depth = refl

double-adequate : ⟦ double ⟧K 5 5 ≡ just (10 , 0)
double-adequate = adequateV double 5

-- The atom exemption: n + n duplicates a machine scalar (free on HVM2,
-- charged 1 word by the grade).
addTwice : nat ⇨ nat
addTwice = addS ∘S dupNatS

addTwice-val : ⟦ addTwice ⟧V 5 ≡ 10
addTwice-val = refl

addTwice-dup : dupGrade addTwice 5 ≡ 1
addTwice-dup = refl

-- sumList: fold addition over a list, seed a boxed closed 0.  The list is
-- consumed affinely — dup grade 0 by construction.
sumList : listT nat ⇨ ! nat
sumList = foldS addS ∘S (idS ⊗S boxValS (constS 0)) ∘S runitS

egList : ⟦ listT nat ⟧T
egList = 1 ∷ 2 ∷ 3 ∷ []

incrementAll : listT nat ⇨ ! (listT nat)
incrementAll = mapS sucS

map-val : ⟦ incrementAll ⟧V egList ≡ 2 ∷ 3 ∷ 4 ∷ []
map-val = refl

map-cost : work incrementAll egList ≡ 3
map-cost = refl

map-dup : dupGrade incrementAll egList ≡ 0
map-dup = refl

map-depth : depth incrementAll ≡ 1
map-depth = refl

map-adequate : ⟦ incrementAll ⟧K egList 3 ≡ just (2 ∷ 3 ∷ 4 ∷ [] , 0)
map-adequate = adequateV incrementAll egList

sumList-val : ⟦ sumList ⟧V egList ≡ 6
sumList-val = refl

sumList-cost : work sumList egList ≡ 3           -- 1 tel per element
sumList-cost = refl

sumList-dup : dupGrade sumList egList ≡ 0        -- affine ⇒ free on nets
sumList-dup = refl

-- Sharing a computed value is priced. The sum comes
-- back boxed; dupS copies the box; with no dereliction the copies are
-- consumed one level down, via mergeS + boxS addS.  The dup charge (size
-- of the copied value: 1 word) is visible statically — not discovered at
-- 10⁹ interactions.
sumTwice : listT nat ⇨ ! nat
sumTwice = boxS addS ∘S mergeS ∘S dupS ∘S sumList

sumTwice-val : ⟦ sumTwice ⟧V egList ≡ 12
sumTwice-val = refl

sumTwice-dup : dupGrade sumTwice egList ≡ 1      -- one boxed word, copied once
sumTwice-dup = refl

-- Nesting boxes stacks strata: towerHeight is the coarse cost report.
twoLevels : unit ⇨ ! ! nat
twoLevels = boxValS (boxValS (constS 7))

twoLevels-depth : towerHeight twoLevels ≡ 2
twoLevels-depth = refl

-- ── M1 additions exercised ──────────────────────────────────────────────────

-- isZero: probe a nat (stop on zero — the whileS convention inj₁ = stop).
isZero : nat ⇨ (unit ⊕ unit)
isZero = caseS inlS (inrS ∘S weakS) ∘S natOutS

-- pred: 0 ↦ 0, suc n ↦ n.
predS : nat ⇨ nat
predS = caseS (constS 0) idS ∘S natOutS

-- countDown: while (not zero) pred, seed a boxed 3, fuel = the input.
-- Work: per taken step = probe test (1 natOut) + step charge (1) + pred
-- (1 natOut) = 3; three taken steps + the final stopping probe (1) = 10.
-- Dup: the probe reads the loop state without consuming it — 1 word per
-- probe, 4 probes.  The implicit copy is priced, never free.
countDown : nat ⇨ ! nat
countDown = whileS isZero predS ∘S (idS ⊗S boxValS (constS 3)) ∘S runitS

countDown-val : ⟦ countDown ⟧V 5 ≡ 0
countDown-val = refl

countDown-cost : work countDown 5 ≡ 10
countDown-cost = refl

countDown-dup : dupGrade countDown 5 ≡ 4
countDown-dup = refl

countDown-depth : depth countDown ≡ 1
countDown-depth = refl

countDown-adequate : ⟦ countDown ⟧K 5 10 ≡ just (0 , 0)
countDown-adequate = adequateV countDown 5

-- Fuel exhaustion is well-defined (returns the state reached), and cheaper:
-- with fuel 2, two taken steps, no stopping probe.
countDown-fuel : ⟦ countDown ⟧V 2 ≡ 1
countDown-fuel = refl

-- guardS: the refinement primitive.  positive = {n : nat | n > 0}, as a
-- pass-through-or-error morphism.  Runtime refinement failure is an error
-- VALUE (inj₂), priced like everything else; the probe's implicit copy
-- charges the dup grade.
isPositive : nat ⇨ (unit ⊕ unit)
isPositive = caseS inrS (inlS ∘S weakS) ∘S natOutS

positive : nat ⇨ (nat ⊕ unit)
positive = guardS isPositive

positive-pass : ⟦ positive ⟧V 5 ≡ inj₁ 5
positive-pass = refl

positive-fail : ⟦ positive ⟧V 0 ≡ inj₂ tt
positive-fail = refl

positive-cost : work positive 5 ≡ 1              -- the natOut look
positive-cost = refl

positive-dup : dupGrade positive 5 ≡ 1           -- the probe's copy
positive-dup = refl

positive-adequate : ⟦ positive ⟧K 5 1 ≡ just (inj₁ 5 , 0)
positive-adequate = adequateV positive 5
