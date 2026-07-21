------------------------------------------------------------------------
-- T3.Sem.Space — the live-heap space semantics (design/SPACE.md).
--
-- A DEDICATED sized interpreter, deliberately not a CostAlgebra
-- instance: retention — a loop's un-consumed tail, a tensor's sibling,
-- a map's already-produced prefix — needs the sizes of values that are
-- not part of the current leaf transition, which chargePrim/_⋄_ are
-- never given (see T3.Sem.Graded's header).
--
-- ⟦_⟧S returns (peak , value): the peak number of live words during
-- left-to-right evaluation, and the value.  Value components coincide
-- with ⟦_⟧G's; closures carry their own peak function (GVal ℕ), so the
-- Kripke relation γW of T3.Bound reads off space bounds unchanged.
--
-- Size model is sizeG (mirror of sizeT): boxes are weightless and a
-- closure is one word (pointer model — the environment's words surface
-- when the body runs; the sit-in-heap undercount is the same one
-- documented for the dup grade in T3.Core.Ty).
--
-- Every case charges at least its input's live size; output liveness is
-- charged by the consumer (the machine wrapper reports peak ⊔ output
-- size at the boundary).  applyS charges the closure's own peak, which
-- by the curryS clause is the body's peak on (env , argument) — the
-- captured environment resurfaces there.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Sem.Space where

open import Data.Nat     using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value using (guardOut)
open import T3.Sem.Graded using (GVal; sizeG)

private
  sz : (A : Ty) → GVal ℕ A → ℕ
  sz = sizeG ℕ

-- map retains the un-consumed tail through the round and the produced
-- element through the rest of the traversal.
mapSp : (A B : Ty) → (GVal ℕ A → ℕ × GVal ℕ B)
      → List (GVal ℕ A) → ℕ × List (GVal ℕ B)
mapSp A B f []       = (1 , [])
mapSp A B f (x ∷ xs) =
  let (pb , y)  = f x
      (pr , ys) = mapSp A B f xs
  in ((sz (listT A) xs + pb) ⊔ (sz B y + pr) , y ∷ ys)

iterSp : (A : Ty) → (GVal ℕ A → ℕ × GVal ℕ A)
       → ℕ → GVal ℕ A → ℕ × GVal ℕ A
iterSp A f zero    a = (sz A a , a)
iterSp A f (suc n) a =
  let (pb , b) = f a
      (pr , c) = iterSp A f n b
  in (pb ⊔ pr , c)

-- fold retains the un-consumed tail alongside each round's body.
foldSp : (A B : Ty) → ((GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
       → List (GVal ℕ A) → GVal ℕ B → ℕ × GVal ℕ B
foldSp A B f []       b = (sz B b , b)
foldSp A B f (x ∷ xs) b =
  let (pb , b') = f (b , x)
      (pr , c)  = foldSp A B f xs b'
  in ((sz (listT A) xs + pb) ⊔ pr , c)

whileSpGo : (A : Ty) → ℕ
          → (GVal ℕ A → ℕ × (⊤ ⊎ ⊤)) → (GVal ℕ A → ℕ × GVal ℕ A)
          → GVal ℕ A → ℕ → ⊤ ⊎ ⊤ → ℕ × GVal ℕ A
whileSp   : (A : Ty) → ℕ
          → (GVal ℕ A → ℕ × (⊤ ⊎ ⊤)) → (GVal ℕ A → ℕ × GVal ℕ A)
          → GVal ℕ A → ℕ × GVal ℕ A

whileSpGo A n t s a pt (inj₁ _) = (pt ⊔ sz A a , a)
whileSpGo A n t s a pt (inj₂ _) =
  let (ps , b) = s a
      (pr , c) = whileSp A n t s b
  in (pt ⊔ (ps ⊔ pr) , c)

whileSp A zero    t s a = (sz A a , a)
whileSp A (suc n) t s a = let (pt , r) = t a in whileSpGo A n t s a pt r

⟦_⟧S : {A B : Ty} → A ⇨ B → GVal ℕ A → ℕ × GVal ℕ B
⟦_⟧S {A} idS a = (sz A a , a)
⟦ g ∘S f ⟧S a =
  let (pf , b) = ⟦ f ⟧S a
      (pg , c) = ⟦ g ⟧S b
  in (pf ⊔ pg , c)
⟦_⟧S (_⊗S_ {A} {B} {C} {D} f g) (a , c) =
  let (pf , b) = ⟦ f ⟧S a
      (pg , d) = ⟦ g ⟧S c
  in ((sz C c + pf) ⊔ (sz B b + pg) , (b , d))
⟦_⟧S {A ⊗ B} swapS (a , b) = (sz A a + sz B b , (b , a))
⟦_⟧S {(A ⊗ B) ⊗ C} assocS ((a , b) , c) =
  (sz A a + sz B b + sz C c , (a , (b , c)))
⟦_⟧S {A ⊗ (B ⊗ C)} unassocS (a , (b , c)) =
  (sz A a + (sz B b + sz C c) , ((a , b) , c))
⟦_⟧S {A ⊗ B} exlS (a , b) = (sz A a + sz B b , a)
⟦_⟧S {A ⊗ B} exrS (a , b) = (sz A a + sz B b , b)
⟦_⟧S {A} weakS a = (sz A a , tt)
⟦_⟧S {A} runitS a = (suc (sz A a) , (a , tt))
⟦_⟧S {A} lunitS a = (suc (sz A a) , (tt , a))
⟦_⟧S {A} inlS a = (suc (sz A a) , inj₁ a)
⟦_⟧S {B} inrS b = (suc (sz B b) , inj₂ b)
⟦_⟧S {A ⊕ B} (caseS l r) (inj₁ a) =
  let (p , c) = ⟦ l ⟧S a in (suc (sz A a) ⊔ p , c)
⟦_⟧S {A ⊕ B} (caseS l r) (inj₂ b) =
  let (p , c) = ⟦ r ⟧S b in (suc (sz B b) ⊔ p , c)
⟦_⟧S {A ⊗ (B ⊕ C)} distlS (a , inj₁ b) =
  (sz A a + suc (sz B b) , inj₁ (a , b))
⟦_⟧S {A ⊗ (B ⊕ C)} distlS (a , inj₂ c) =
  (sz A a + suc (sz C c) , inj₂ (a , c))
⟦ nilS ⟧S _ = (1 , [])
⟦_⟧S {A ⊗ listT _} consS (x , xs) = (suc (sz A x + sz (listT A) xs) , x ∷ xs)
⟦_⟧S {listT A} unconsS [] = (2 , inj₁ tt)
⟦_⟧S {listT A} unconsS (x ∷ xs) =
  (suc (sz A x + sz (listT A) xs) , inj₂ (x , xs))
⟦ natOutS ⟧S zero = (2 , inj₁ tt)
⟦ natOutS ⟧S (suc n) = (2 , inj₂ n)
⟦ sucS ⟧S n = (1 , suc n)
⟦ addS ⟧S (a , b) = (2 , a + b)
⟦_⟧S {A} (constS k) a = (sz A a , k)
⟦ dupNatS ⟧S n = (2 , (n , n))
⟦_⟧S {A} (copyS _) a = (sz A a + sz A a , (a , a))
⟦_⟧S {A} (guardS t) a =
  let (pt , r) = ⟦ t ⟧S a
  in (pt ⊔ suc (sz A a) , guardOut a r (inj₂ tt))
⟦_⟧S {C} (curryS f) c = (sz C c , λ a → ⟦ f ⟧S (c , a))
⟦_⟧S {(A ⊸ B) ⊗ A} applyS (gf , a) =
  let (pb , b) = gf a
  in (suc (sz A a) ⊔ pb , b)
⟦_⟧S {(! (A ⊸ B)) ⊗ listT _} mapCS (gf , xs) =
  let (p , ys) = mapSp A B gf xs in (suc p , ys)
⟦_⟧S {A} (promoteS _) a = (sz A a , a)
⟦_⟧S {(! A)} dupS a = (sz A a + sz A a , (a , a))
⟦ boxS f ⟧S a = ⟦ f ⟧S a
⟦ boxValS f ⟧S a = ⟦ f ⟧S a
⟦_⟧S {(! A) ⊗ (! B)} mergeS (a , b) = (sz A a + sz B b , (a , b))
⟦_⟧S (mapS {A} {B} f) xs = mapSp A B ⟦ f ⟧S xs
⟦_⟧S (iterS {A} f) (n , a) =
  let (p , c) = iterSp A ⟦ f ⟧S n a in (suc p , c)
⟦_⟧S (foldS {A} {B} f) (xs , b) =
  let (p , c) = foldSp A B ⟦ f ⟧S xs b
  in ((sz (listT A) xs + sz B b) ⊔ p , c)
⟦_⟧S (whileS {A} t s) (n , a) =
  let (p , c) = whileSp A n ⟦ t ⟧S ⟦ s ⟧S a in (suc p , c)

-- The space reading of a run.
spacePeak : {A B : Ty} → A ⇨ B → GVal ℕ A → ℕ
spacePeak f a = proj₁ (⟦ f ⟧S a)
