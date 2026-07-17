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
open import T3.Adequacy using ()

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
double-adequate = refl

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
map-adequate = refl

sumList-val : ⟦ sumList ⟧V egList ≡ 6
sumList-val = refl

sumList-cost : work sumList egList ≡ 3           -- 1 tel per element
sumList-cost = refl

sumList-dup : dupGrade sumList egList ≡ 0        -- affine ⇒ free on nets
sumList-dup = refl

-- Costed data copy: reuse of first-order data is legal and priced by
-- size.  Copying is free time (work 0) but never free duplication — the
-- dup grade charges the full word size of the copied value.
copyList : listT nat ⇨ (listT nat ⊗ listT nat)
copyList = copyS (copy-list copy-nat)

copyList-val : ⟦ copyList ⟧V egList ≡ (egList , egList)
copyList-val = refl

copyList-cost : work copyList egList ≡ 0
copyList-cost = refl

copyList-dup : dupGrade copyList egList ≡ 7      -- sizeT of the 3-element list
copyList-dup = refl

copyList-depth : depth copyList ≡ 0
copyList-depth = refl

-- One input list feeding two folds through one priced copy.
sumBoth : listT nat ⇨ (! nat ⊗ ! nat)
sumBoth = (sumList ⊗S sumList) ∘S copyS (copy-list copy-nat)

sumBoth-val : ⟦ sumBoth ⟧V egList ≡ (6 , 6)
sumBoth-val = refl

sumBoth-cost : work sumBoth egList ≡ 6           -- both folds pay their steps
sumBoth-cost = refl

sumBoth-dup : dupGrade sumBoth egList ≡ 7        -- exactly the one copy
sumBoth-dup = refl

sumBoth-adequate : ⟦ sumBoth ⟧K egList 6 ≡ just ((6 , 6) , 0)
sumBoth-adequate = refl

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
countDown-adequate = refl

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
positive-adequate = refl

-- ── closures ────────────────────────────────────────────────────────────────

-- A closed closure: no captured environment beyond unit.
inc⊸ : unit ⇨ (nat ⊸ nat)
inc⊸ = curryS (sucS ∘S exrS)

-- Linear application: form the closure, apply it once.  Work 1 = the
-- apply tag (the body is free); no duplication; depth 0 — curry/apply
-- are level-preserving.
applyInc : nat ⇨ nat
applyInc = applyS ∘S (inc⊸ ⊗S idS) ∘S lunitS

applyInc-val : ⟦ applyInc ⟧V 5 ≡ 6
applyInc-val = refl

applyInc-cost : work applyInc 5 ≡ 1
applyInc-cost = refl

applyInc-dup : dupGrade applyInc 5 ≡ 0
applyInc-dup = refl

applyInc-depth : depth applyInc ≡ 0
applyInc-depth = refl

applyInc-adequate : ⟦ applyInc ⟧K 5 1 ≡ just (6 , 0)
applyInc-adequate = refl

-- Runtime selection between two REUSABLE closed closures: each branch
-- promotes a closed closure via boxValS (the only way to make code
-- reusable), and the chosen one is applied one level down.
chooseOp : (unit ⊕ unit) ⇨ ! (nat ⊸ nat)
chooseOp = caseS (boxValS inc⊸) (boxValS (curryS (predS ∘S exrS)))

applyChosen : (unit ⊕ unit) ⇨ ! nat
applyChosen =
  boxS applyS ∘S mergeS ∘S (chooseOp ⊗S boxValS (constS 3)) ∘S runitS

applyChosen-left : ⟦ applyChosen ⟧V (inj₁ tt) ≡ 4
applyChosen-left = refl

applyChosen-right : ⟦ applyChosen ⟧V (inj₂ tt) ≡ 2
applyChosen-right = refl

applyChosen-depth : depth applyChosen ≡ 1
applyChosen-depth = refl

-- Higher-order map: a runtime-selected reusable mapper over a closed
-- list.  Work per element = 1 step + the selected body's own cost.
egListS : unit ⇨ listT nat
egListS =
  consS ∘S (constS 1 ⊗S (consS ∘S (constS 2 ⊗S nilS) ∘S lunitS)) ∘S lunitS

mapChosen : (unit ⊕ unit) ⇨ ! (listT nat)
mapChosen = mapCS ∘S (chooseOp ⊗S egListS) ∘S runitS

mapChosen-left : ⟦ mapChosen ⟧V (inj₁ tt) ≡ 2 ∷ 3 ∷ []
mapChosen-left = refl

mapChosen-right : ⟦ mapChosen ⟧V (inj₂ tt) ≡ 0 ∷ 1 ∷ []
mapChosen-right = refl

mapChosen-cost-left : work mapChosen (inj₁ tt) ≡ 2
mapChosen-cost-left = refl                        -- suc body is free

mapChosen-cost-right : work mapChosen (inj₂ tt) ≡ 4
mapChosen-cost-right = refl                       -- pred pays a natOut look

mapChosen-depth : depth mapChosen ≡ 1
mapChosen-depth = refl
