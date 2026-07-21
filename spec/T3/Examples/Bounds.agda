------------------------------------------------------------------------
-- T3.Examples.Bounds — static work/dup bounds on worked examples; every
-- fact computes by refl and becomes a Haskell test vector 1:1 by name
-- (test/BoundVectors.hs).
--
-- Examples pair static bounds with checks that concrete grades stay below
-- them.  Bounds are honest rather than necessarily tight: loops use full
-- fuel and branches use their maximum.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Examples.Bounds where

open import Data.Nat     using (ℕ; _≤_; s≤s; z≤n)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁)
open import Data.Sum     using (inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Graded
open import T3.Abstract using (Shape; topS; natLE; pairS; bangS; listS)
open import T3.Bound
open import T3.Examples.Basics using (double; countDown; applyInc;
                                       chooseOp; applyChosen; mapChosen;
                                       incrementAll; copyList; sumBoth;
                                       positive; egList)

-- double: iterate (+2) n times.  At fuel ≤ 5 the loop is charged five
-- rounds of one step each; the seed and plumbing are free.
double-bound : proj₁ (costW double (natLE 5)) ≡ just 5
double-bound = refl

double-bound-holds : work double 5 ≤ 5
double-bound-holds = proj₁ (costW-sound double (natLE 5) ≤-refl′)
  where ≤-refl′ : 5 ≤ 5
        ≤-refl′ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

-- At an unknown Nat input the fuel is unbounded: the analysis says so
-- honestly rather than guessing.
double-unbounded : proj₁ (costW double topS) ≡ nothing
double-unbounded = refl

-- countDown: while-loop with fuel ≤ 5; each round pays the probe's
-- natOut, the step charge, and pred's natOut — 3 per full round, with
-- the full-unroll sum dominating any early stop.
countDown-bound : proj₁ (costW countDown (natLE 5)) ≡ just 15
countDown-bound = refl

countDown-bound-holds : work countDown 5 ≤ 15
countDown-bound-holds =
  proj₁ (costW-sound countDown (natLE 5) (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

-- applyInc: form a closure, apply it once — 1 work (the apply tag; the
-- suc body is free), bounded even at an unknown argument.
applyInc-bound : proj₁ (costW applyInc topS) ≡ just 1
applyInc-bound = refl

applyInc-bound-holds : work applyInc 5 ≤ 1
applyInc-bound-holds = work-bounded applyInc 5

-- chooseOp: the closure bound survives runtime selection — each branch
-- promotes a closed closure and the analysis carries the max body cost
-- through the sum (suc: 0; pred: 1 natOut).
chooseOp-bound : proj₁ (costW chooseOp (shapeOfTy (unit ⊕ unit)))
               ≡ just 0
chooseOp-bound = refl

applyChosen-bound : proj₁ (costW applyChosen (shapeOfTy (unit ⊕ unit)))
                  ≡ just 2
applyChosen-bound = refl

applyChosen-bound-holds-left : work applyChosen (inj₁ tt) ≤ 2
applyChosen-bound-holds-left = work-bounded applyChosen (inj₁ tt)

applyChosen-bound-holds-right : work applyChosen (inj₂ tt) ≤ 2
applyChosen-bound-holds-right = work-bounded applyChosen (inj₂ tt)

-- mapChosen: a runtime-selected reusable mapper over a two-element
-- closed list: 2 elements × (1 step + body ≤ 1) = 4.
mapChosen-bound : proj₁ (costW mapChosen (shapeOfTy (unit ⊕ unit)))
                ≡ just 4
mapChosen-bound = refl

mapChosen-bound-holds-left : work mapChosen (inj₁ tt) ≤ 4
mapChosen-bound-holds-left = work-bounded mapChosen (inj₁ tt)

mapChosen-bound-holds-right : work mapChosen (inj₂ tt) ≤ 4
mapChosen-bound-holds-right = work-bounded mapChosen (inj₂ tt)

-- A matchNat-style literal cascade: natOut cost is fixed by the LITERAL
-- depth, not the scrutinee — probing against {0,1,2} pays at most 3
-- looks on ANY input.  This is why tic-tac-toe's step bound is
-- input-independent.
probe3 : nat ⇨ nat
probe3 =
  caseS (constS 0)
    (caseS (constS 1)
      (caseS (constS 2) (constS 3) ∘S natOutS)
      ∘S natOutS)
    ∘S natOutS

probe3-bound : proj₁ (costW probe3 topS) ≡ just 3
probe3-bound = refl

probe3-bound-holds : work probe3 100 ≤ 3
probe3-bound-holds = work-bounded probe3 100

-- ── Static duplication bounds ───────────────────────────────────────────────

list3S : Shape (listT nat)
list3S = listS 3 (natLE 5)

list3-size : sizeS list3S ≡ just 7
list3-size = refl

nat-top-size : sizeS (topS {A = nat}) ≡ just 1
nat-top-size = refl

-- A three-element Nat list occupies one nil word plus two words per cons.
-- copyS charges that complete input size.
copyList-dup-bound : proj₁ (costD copyList list3S) ≡ just 7
copyList-dup-bound = refl

copyList-dup-bound-holds : dupGrade copyList egList ≤ 7
copyList-dup-bound-holds = dup-bounded-at copyList list3S
  (s≤s (s≤s (s≤s z≤n)) ,
   s≤s z≤n ∷ s≤s (s≤s z≤n) ∷
   s≤s (s≤s (s≤s z≤n)) ∷ [])

-- The two folds are affine; the only duplication is the shared input copy.
sumBoth-dup-bound : proj₁ (costD sumBoth list3S) ≡ just 7
sumBoth-dup-bound = refl

sumBoth-dup-bound-holds : dupGrade sumBoth egList ≤ 7
sumBoth-dup-bound-holds = dup-bounded-at sumBoth list3S
  (s≤s (s≤s (s≤s z≤n)) ,
   s≤s z≤n ∷ s≤s (s≤s z≤n) ∷
   s≤s (s≤s (s≤s z≤n)) ∷ [])

-- A zero-duplication map remains statically zero even at unknown length.
map-dup-bound : proj₁ (costD incrementAll topS) ≡ just 0
map-dup-bound = refl

map-dup-bound-holds : dupGrade incrementAll egList ≤ 0
map-dup-bound-holds = dup-bounded incrementAll egList

-- guardS copies its probed Nat once.
positive-dup-bound : proj₁ (costD positive topS) ≡ just 1
positive-dup-bound = refl

positive-dup-bound-holds : dupGrade positive 5 ≤ 1
positive-dup-bound-holds = dup-bounded positive 5

-- Full-unroll while bound: five possible probes, while the concrete run
-- stops after four.  Test and step bodies themselves are affine.
countDown-dup-bound : proj₁ (costD countDown (natLE 5)) ≡ just 5
countDown-dup-bound = refl

countDown-dup-bound-holds : dupGrade countDown 5 ≤ 5
countDown-dup-bound-holds = dup-bounded-at countDown (natLE 5)
  (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

-- Closure formation/application introduces no duplication for this body.
applyInc-dup-bound : proj₁ (costD applyInc topS) ≡ just 0
applyInc-dup-bound = refl

applyInc-dup-bound-holds : dupGrade applyInc 5 ≤ 0
applyInc-dup-bound-holds = dup-bounded applyInc 5
