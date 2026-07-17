------------------------------------------------------------------------
-- T3.Sem.Graded — ONE graded interpretation, many cost algebras.
--
-- Work, duplication, and space resource readings collapse into one
-- interpretation ⟦_⟧G parameterized by a CostAlgebra.  The execution
-- semantics ⟦_⟧K (T3.Sem.Exec) deliberately stays separate: it is not a
-- grading but the machine, and T3.Adequacy proves it precise against the
-- work instance.
--
-- CLOSURES change the shape of graded values: a closure's body cost is
-- dynamic (paid at each apply), so the graded meaning of A ⊸ B must
-- carry its own grade function.  GVal M is the graded value universe —
-- identical to ⟦_⟧T except GVal M (A ⊸ B) = GVal M A → M × GVal M B.
-- Charges are therefore taken on SIZES (sizeG, the GVal mirror of
-- sizeT), which is also exactly how the Haskell mirror's CostAlgebra was
-- already specialized.
--
-- Value coherence is proved ONCE, generically, as the fundamental lemma
-- of a logical relation: ≈G relates graded values to specification
-- values (equality at first-order structure, pointwise at arrows), and
-- for every algebra R, G-val sends related inputs to related outputs.
-- At arrow-free types GVal M A and ⟦ A ⟧T are definitionally equal and
-- ≈G collapses to structural equality, so first-order consequences
-- (the Examples' refl facts) are unchanged.
--
-- towerHeight is NOT an instance (see T3.Core.Syntax): it is the sup
-- over all inputs, a quotient of the grade read directly off the syntax.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Sem.Graded where

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat     using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise
                         using (Pointwise; []; _∷_)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                         using (_≡_; refl)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value

-- Graded values over a cost carrier M: a closure carries its grade.
GVal : Set → Ty → Set
GVal M unit      = ⊤
GVal M nat       = ℕ
GVal M (A ⊗ B)   = GVal M A × GVal M B
GVal M (A ⊕ B)   = GVal M A ⊎ GVal M B
GVal M (listT A) = List (GVal M A)
GVal M (! A)     = GVal M A
GVal M (A ⊸ B)   = GVal M A → M × GVal M B

-- Word model of graded value size (mirror of sizeT; closures = 1 word).
sizeG : (M : Set) (A : Ty) → GVal M A → ℕ
sizeG M unit      _        = 1
sizeG M nat       _        = 1
sizeG M (A ⊗ B)   (a , b)  = sizeG M A a + sizeG M B b
sizeG M (A ⊕ B)   (inj₁ a) = suc (sizeG M A a)
sizeG M (A ⊕ B)   (inj₂ b) = suc (sizeG M B b)
sizeG M (listT A) []       = 1
sizeG M (listT A) (x ∷ xs) = suc (sizeG M A x + sizeG M (listT A) xs)
sizeG M (! A)     a        = sizeG M A a
sizeG M (A ⊸ B)   _        = 1

-- The logical relation between graded and specification values:
-- structural equality below arrows, pointwise at arrows.
≈G : (M : Set) (A : Ty) → GVal M A → ⟦ A ⟧T → Set
≈G M unit      _         _         = ⊤
≈G M nat       m         n         = m ≡ n
≈G M (A ⊗ B)   (ga , gb) (a , b)   = ≈G M A ga a × ≈G M B gb b
≈G M (A ⊕ B)   (inj₁ ga) (inj₁ a)  = ≈G M A ga a
≈G M (A ⊕ B)   (inj₂ gb) (inj₂ b)  = ≈G M B gb b
≈G M (A ⊕ B)   (inj₁ _)  (inj₂ _)  = ⊥
≈G M (A ⊕ B)   (inj₂ _)  (inj₁ _)  = ⊥
≈G M (listT A) gxs       xs        = Pointwise (≈G M A) gxs xs
≈G M (! A)     ga        a         = ≈G M A ga a
≈G M (A ⊸ B)   gf        f         =
  ∀ ga a → ≈G M A ga a → ≈G M B (proj₂ (gf ga)) (f a)

-- Test verdicts are first-order: related verdicts are equal.
≈G-verdict : (M : Set) (gv : GVal M (unit ⊕ unit)) (v : ⟦ unit ⊕ unit ⟧T)
           → ≈G M (unit ⊕ unit) gv v → gv ≡ v
≈G-verdict M (inj₁ tt) (inj₁ tt) _ = refl
≈G-verdict M (inj₂ tt) (inj₂ tt) _ = refl
≈G-verdict M (inj₁ tt) (inj₂ tt) ()
≈G-verdict M (inj₂ tt) (inj₁ tt) ()

-- Leaf-primitive tags: what chargePrim discriminates on.  Structural
-- constructors (∘S, ⊗S, caseS, boxS, boxValS, guardS, iterS, foldS,
-- whileS, mapCS) are interpreted recursively and charge through
-- chargeStep / chargeBase / chargeProbe instead — with applyT the one
-- exception: apply charges its tag AND the body's dynamic grade.
data PrimTag : Set where
  idT swapT assocT unassocT exlT exrT weakT runitT lunitT
    inlT inrT distlT nilT consT unconsT
    natOutT sucT addT constT dupNatT dupT copyT mergeT
    curryT applyT : PrimTag

record CostAlgebra : Set₁ where
  infixr 7 _⋄_
  infixr 6 _∥_
  field
    ℳ           : Set
    _⋄_         : ℳ → ℳ → ℳ      -- sequential composition of grades
    _∥_         : ℳ → ℳ → ℳ      -- parallel (tensor) composition
    chargePrim  : (A B : Ty) → PrimTag → ℕ → ℕ → ℳ
                                   -- charge on input/output SIZES
    chargeStep  : ℳ                -- per taken loop step
    chargeBase  : (A : Ty) → ℕ → ℳ
                                   -- at loop exhaustion/stop (space: live size)
    chargeProbe : (A : Ty) → ℕ → ℳ
                                   -- guardS / whileS test: the implicit
                                   -- copy of the probed value, never free

module Interp (R : CostAlgebra) where
  open CostAlgebra R

  private
    sz : (A : Ty) → GVal ℳ A → ℕ
    sz = sizeG ℳ

  mapG : {A B : Set} → (List B → ℳ) → List A → (A → ℳ × B) → ℳ × List B
  mapG base []       f = (base [] , [])
  mapG base (x ∷ xs) f =
    let (m , y)  = f x
        (r , ys) = mapG base xs f
    in (chargeStep ⋄ (m ⋄ r) , y ∷ ys)

  iterG : {A : Set} → (A → ℳ) → ℕ → (A → ℳ × A) → A → ℳ × A
  iterG base zero    f a = (base a , a)
  iterG base (suc n) f a =
    let (m , b) = f a
        (r , c) = iterG base n f b
    in (chargeStep ⋄ (m ⋄ r) , c)

  foldG : {A B : Set} → (B → ℳ) → List A → ((B × A) → ℳ × B) → B → ℳ × B
  foldG base []       f b = (base b , b)
  foldG base (x ∷ xs) f b =
    let (m , b') = f (b , x)
        (r , c)  = foldG base xs f b'
    in (chargeStep ⋄ (m ⋄ r) , c)

  whileGo : (A : Ty) → ℕ
          → (GVal ℳ A → ℳ × (⊤ ⊎ ⊤)) → (GVal ℳ A → ℳ × GVal ℳ A)
          → GVal ℳ A → ℳ → ⊤ ⊎ ⊤ → ℳ × GVal ℳ A
  whileG  : (A : Ty) → ℕ
          → (GVal ℳ A → ℳ × (⊤ ⊎ ⊤)) → (GVal ℳ A → ℳ × GVal ℳ A)
          → GVal ℳ A → ℳ × GVal ℳ A

  whileGo A n t s a mt (inj₁ _) = (chargeProbe A (sz A a) ⋄ mt , a)
  whileGo A n t s a mt (inj₂ _) =
    let (ms , b) = s a
        (r , c)  = whileG A n t s b
    in (chargeProbe A (sz A a) ⋄ (mt ⋄ (chargeStep ⋄ (ms ⋄ r))) , c)

  whileG A zero    t s a = (chargeBase (! A) (sz A a) , a)
  whileG A (suc n) t s a = let (mt , r) = t a in whileGo A n t s a mt r

  ⟦_⟧G : {A B : Ty} → A ⇨ B → GVal ℳ A → ℳ × GVal ℳ B
  ⟦_⟧G {A} idS a = (chargePrim A A idT (sz A a) (sz A a) , a)
  ⟦ g ∘S f ⟧G a =
    let (m , b) = ⟦ f ⟧G a
        (r , c) = ⟦ g ⟧G b
    in (m ⋄ r , c)
  ⟦ f ⊗S g ⟧G (a , c) =
    let (m , b) = ⟦ f ⟧G a
        (r , d) = ⟦ g ⟧G c
    in (m ∥ r , (b , d))
  ⟦ swapS {A} {B} ⟧G p@(a , b) =
    (chargePrim (A ⊗ B) (B ⊗ A) swapT (sz (A ⊗ B) p) (sz (B ⊗ A) (b , a))
    , (b , a))
  ⟦ assocS {A} {B} {C} ⟧G p@((a , b) , c) =
    (chargePrim ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) assocT
      (sz ((A ⊗ B) ⊗ C) p) (sz (A ⊗ (B ⊗ C)) (a , (b , c)))
    , (a , (b , c)))
  ⟦ unassocS {A} {B} {C} ⟧G p@(a , (b , c)) =
    (chargePrim (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C)
      unassocT (sz (A ⊗ (B ⊗ C)) p) (sz ((A ⊗ B) ⊗ C) ((a , b) , c))
    , ((a , b) , c))
  ⟦ exlS {A} {B} ⟧G p@(a , _) =
    (chargePrim (A ⊗ B) A exlT (sz (A ⊗ B) p) (sz A a) , a)
  ⟦ exrS {A} {B} ⟧G p@(_ , b) =
    (chargePrim (A ⊗ B) B exrT (sz (A ⊗ B) p) (sz B b) , b)
  ⟦ weakS {A} ⟧G a = (chargePrim A unit weakT (sz A a) 1 , tt)
  ⟦ runitS {A} ⟧G a =
    (chargePrim A (A ⊗ unit) runitT (sz A a) (sz (A ⊗ unit) (a , tt))
    , (a , tt))
  ⟦ lunitS {A} ⟧G a =
    (chargePrim A (unit ⊗ A) lunitT (sz A a) (sz (unit ⊗ A) (tt , a))
    , (tt , a))
  ⟦ inlS {A} {B} ⟧G a =
    (chargePrim A (A ⊕ B) inlT (sz A a) (suc (sz A a)) , inj₁ a)
  ⟦ inrS {A} {B} ⟧G b =
    (chargePrim B (A ⊕ B) inrT (sz B b) (suc (sz B b)) , inj₂ b)
  ⟦ caseS l r ⟧G (inj₁ a) = ⟦ l ⟧G a
  ⟦ caseS l r ⟧G (inj₂ b) = ⟦ r ⟧G b
  ⟦ distlS {A} {B} {C} ⟧G p@(a , inj₁ b) =
    (chargePrim (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C)) distlT
      (sz (A ⊗ (B ⊕ C)) p) (suc (sz (A ⊗ B) (a , b)))
    , inj₁ (a , b))
  ⟦ distlS {A} {B} {C} ⟧G p@(a , inj₂ c) =
    (chargePrim (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C)) distlT
      (sz (A ⊗ (B ⊕ C)) p) (suc (sz (A ⊗ C) (a , c)))
    , inj₂ (a , c))
  ⟦ nilS {A} ⟧G u = (chargePrim unit (listT A) nilT 1 1 , [])
  ⟦ consS {A} ⟧G p@(x , xs) =
    (chargePrim (A ⊗ listT A) (listT A) consT
      (sz (A ⊗ listT A) p) (sz (listT A) (x ∷ xs))
    , (x ∷ xs))
  ⟦ unconsS {A} ⟧G [] =
    (chargePrim (listT A) (unit ⊕ (A ⊗ listT A)) unconsT 1 2 , inj₁ tt)
  ⟦ unconsS {A} ⟧G l@(x ∷ xs) =
    (chargePrim (listT A) (unit ⊕ (A ⊗ listT A)) unconsT
      (sz (listT A) l) (suc (sz (A ⊗ listT A) (x , xs)))
    , inj₂ (x , xs))
  ⟦ natOutS ⟧G zero =
    (chargePrim nat (unit ⊕ nat) natOutT 1 2 , inj₁ tt)
  ⟦ natOutS ⟧G n@(suc k) =
    (chargePrim nat (unit ⊕ nat) natOutT 1 2 , inj₂ k)
  ⟦ sucS ⟧G n = (chargePrim nat nat sucT 1 1 , suc n)
  ⟦ addS ⟧G p@(a , b) = (chargePrim (nat ⊗ nat) nat addT 2 1 , a + b)
  ⟦ constS {A} k ⟧G a = (chargePrim A nat constT (sz A a) 1 , k)
  ⟦ dupNatS ⟧G n = (chargePrim nat (nat ⊗ nat) dupNatT 1 2 , (n , n))
  ⟦ copyS {A} _ ⟧G a =
    (chargePrim A (A ⊗ A) copyT (sz A a) (sz A a + sz A a) , (a , a))
  ⟦ guardS {A} t ⟧G a =
    let (mt , r) = ⟦ t ⟧G a
    in (chargeProbe A (sz A a) ⋄ mt , guardV a r)
  ⟦ curryS {C} {A} {B} f ⟧G c =
    (chargePrim C (A ⊸ B) curryT (sz C c) 1 , λ a → ⟦ f ⟧G (c , a))
  ⟦ applyS {A} {B} ⟧G (f , a) =
    let (m , b) = f a
    in (chargePrim ((A ⊸ B) ⊗ A) B applyT (suc (sz A a)) (sz B b) ⋄ m , b)
  ⟦ mapCS {A} {B} ⟧G (f , xs) =
    mapG (λ ys → chargeBase (! (listT B)) (sz (listT B) ys)) xs f
  ⟦ dupS {A} ⟧G a =
    (chargePrim (! A) (! A ⊗ ! A) dupT (sz A a) (sz A a + sz A a) , (a , a))
  ⟦ boxS f ⟧G a = ⟦ f ⟧G a
  ⟦ boxValS f ⟧G a = ⟦ f ⟧G a
  ⟦ mergeS {A} {B} ⟧G p =
    (chargePrim (! A ⊗ ! B) (! (A ⊗ B)) mergeT
      (sz (! A ⊗ ! B) p) (sz (! (A ⊗ B)) p)
    , p)
  ⟦ mapS {A} {B} f ⟧G xs =
    mapG (λ ys → chargeBase (! (listT B)) (sz (listT B) ys)) xs ⟦ f ⟧G
  ⟦ iterS {A} f ⟧G (n , a) =
    iterG (λ x → chargeBase (! A) (sz A x)) n ⟦ f ⟧G a
  ⟦ foldS {A} {B} f ⟧G (xs , b) =
    foldG (λ x → chargeBase (! B) (sz B x)) xs ⟦ f ⟧G b
  ⟦ whileS {A} t s ⟧G (n , a) = whileG A n ⟦ t ⟧G ⟦ s ⟧G a

  -- Value coherence: the fundamental lemma of ≈G, proved once for every
  -- algebra.  The graded semantics computes the specification's value
  -- up to the relation (equality below arrows).
  private
    mapG-rel : (A B : Ty) (base : List (GVal ℳ B) → ℳ)
               (fg : GVal ℳ A → ℳ × GVal ℳ B) (fv : ⟦ A ⟧T → ⟦ B ⟧T)
             → (∀ gx x → ≈G ℳ A gx x → ≈G ℳ B (proj₂ (fg gx)) (fv x))
             → (gxs : List (GVal ℳ A)) (xs : List ⟦ A ⟧T)
             → Pointwise (≈G ℳ A) gxs xs
             → Pointwise (≈G ℳ B) (proj₂ (mapG base gxs fg)) (mapV fv xs)
    mapG-rel A B base fg fv h [] [] [] = []
    mapG-rel A B base fg fv h (gx ∷ gxs) (x ∷ xs) (r ∷ rs) =
      h gx x r ∷ mapG-rel A B base fg fv h gxs xs rs

    iterG-rel : (A : Ty) (base : GVal ℳ A → ℳ) (n : ℕ)
                (fg : GVal ℳ A → ℳ × GVal ℳ A) (fv : ⟦ A ⟧T → ⟦ A ⟧T)
              → (∀ gx x → ≈G ℳ A gx x → ≈G ℳ A (proj₂ (fg gx)) (fv x))
              → ∀ ga a → ≈G ℳ A ga a
              → ≈G ℳ A (proj₂ (iterG base n fg ga)) (iterV n fv a)
    iterG-rel A base zero    fg fv h ga a rel = rel
    iterG-rel A base (suc n) fg fv h ga a rel =
      iterG-rel A base n fg fv h (proj₂ (fg ga)) (fv a) (h ga a rel)

    foldG-rel : (A B : Ty) (base : GVal ℳ B → ℳ)
                (fg : (GVal ℳ B × GVal ℳ A) → ℳ × GVal ℳ B)
                (fv : ⟦ B ⟧T × ⟦ A ⟧T → ⟦ B ⟧T)
              → (∀ gb b gx x → ≈G ℳ B gb b → ≈G ℳ A gx x
                 → ≈G ℳ B (proj₂ (fg (gb , gx))) (fv (b , x)))
              → (gxs : List (GVal ℳ A)) (xs : List ⟦ A ⟧T)
              → Pointwise (≈G ℳ A) gxs xs
              → ∀ gb b → ≈G ℳ B gb b
              → ≈G ℳ B (proj₂ (foldG base gxs fg gb)) (foldV xs fv b)
    foldG-rel A B base fg fv h [] [] [] gb b relB = relB
    foldG-rel A B base fg fv h (gx ∷ gxs) (x ∷ xs) (r ∷ rs) gb b relB =
      foldG-rel A B base fg fv h gxs xs rs
        (proj₂ (fg (gb , gx))) (fv (b , x)) (h gb b gx x relB r)

    whileGo-rel : (A : Ty) (n : ℕ)
                  (tg : GVal ℳ A → ℳ × (⊤ ⊎ ⊤)) (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤)
                  (sg : GVal ℳ A → ℳ × GVal ℳ A) (sv : ⟦ A ⟧T → ⟦ A ⟧T)
                → (∀ gx x → ≈G ℳ A gx x
                   → ≈G ℳ (unit ⊕ unit) (proj₂ (tg gx)) (tv x))
                → (∀ gx x → ≈G ℳ A gx x → ≈G ℳ A (proj₂ (sg gx)) (sv x))
                → ∀ ga a → ≈G ℳ A ga a → (mt : ℳ) (r : ⊤ ⊎ ⊤)
                → ≈G ℳ A (proj₂ (whileGo A n tg sg ga mt r))
                       (whileV-go n tv sv a r)
    whileG-rel  : (A : Ty) (n : ℕ)
                  (tg : GVal ℳ A → ℳ × (⊤ ⊎ ⊤)) (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤)
                  (sg : GVal ℳ A → ℳ × GVal ℳ A) (sv : ⟦ A ⟧T → ⟦ A ⟧T)
                → (∀ gx x → ≈G ℳ A gx x
                   → ≈G ℳ (unit ⊕ unit) (proj₂ (tg gx)) (tv x))
                → (∀ gx x → ≈G ℳ A gx x → ≈G ℳ A (proj₂ (sg gx)) (sv x))
                → ∀ ga a → ≈G ℳ A ga a
                → ≈G ℳ A (proj₂ (whileG A n tg sg ga)) (whileV n tv sv a)

    whileGo-rel A n tg tv sg sv ht hs ga a rel mt (inj₁ _) = rel
    whileGo-rel A n tg tv sg sv ht hs ga a rel mt (inj₂ _) =
      whileG-rel A n tg tv sg sv ht hs
        (proj₂ (sg ga)) (sv a) (hs ga a rel)

    whileG-rel A zero    tg tv sg sv ht hs ga a rel = rel
    whileG-rel A (suc n) tg tv sg sv ht hs ga a rel
      with proj₂ (tg ga) | ≈G-verdict ℳ (proj₂ (tg ga)) (tv a) (ht ga a rel)
    ... | _ | refl =
      whileGo-rel A n tg tv sg sv ht hs ga a rel (proj₁ (tg ga)) (tv a)

  G-val : {A B : Ty} (f : A ⇨ B) {ga : GVal ℳ A} {a : ⟦ A ⟧T}
        → ≈G ℳ A ga a → ≈G ℳ B (proj₂ (⟦ f ⟧G ga)) (⟦ f ⟧V a)
  G-val idS rel = rel
  G-val (g ∘S f) rel = G-val g (G-val f rel)
  G-val (f ⊗S g) (ra , rc) = (G-val f ra , G-val g rc)
  G-val swapS (ra , rb) = (rb , ra)
  G-val assocS ((ra , rb) , rc) = (ra , (rb , rc))
  G-val unassocS (ra , (rb , rc)) = ((ra , rb) , rc)
  G-val exlS (ra , _) = ra
  G-val exrS (_ , rb) = rb
  G-val weakS _ = tt
  G-val runitS rel = (rel , tt)
  G-val lunitS rel = (tt , rel)
  G-val inlS rel = rel
  G-val inrS rel = rel
  G-val (caseS l r) {inj₁ _} {inj₁ _} rel = G-val l rel
  G-val (caseS l r) {inj₂ _} {inj₂ _} rel = G-val r rel
  G-val (caseS l r) {inj₁ _} {inj₂ _} ()
  G-val (caseS l r) {inj₂ _} {inj₁ _} ()
  G-val distlS {_ , inj₁ _} {_ , inj₁ _} (ra , rb) = (ra , rb)
  G-val distlS {_ , inj₂ _} {_ , inj₂ _} (ra , rc) = (ra , rc)
  G-val distlS {_ , inj₁ _} {_ , inj₂ _} (ra , ())
  G-val distlS {_ , inj₂ _} {_ , inj₁ _} (ra , ())
  G-val nilS _ = []
  G-val consS (rx , rxs) = rx ∷ rxs
  G-val unconsS []       = tt
  G-val unconsS (r ∷ rs) = (r , rs)
  G-val natOutS {zero}  refl = tt
  G-val natOutS {suc k} refl = refl
  G-val sucS refl = refl
  G-val addS (refl , refl) = refl
  G-val (constS k) _ = refl
  G-val dupNatS refl = (refl , refl)
  G-val (copyS _) rel = (rel , rel)
  G-val (guardS t) {ga} {a} rel
    with proj₂ (⟦ t ⟧G ga)
       | ≈G-verdict ℳ (proj₂ (⟦ t ⟧G ga)) (⟦ t ⟧V a) (G-val t rel)
  ... | _ | refl with ⟦ t ⟧V a
  ...   | inj₁ _ = rel
  ...   | inj₂ _ = tt
  G-val (curryS f) rel = λ ga a relA → G-val f (rel , relA)
  G-val applyS {gf , ga} {f , a} (relF , relA) = relF ga a relA
  G-val (mapCS {A} {B}) {gf , gxs} {f , xs} (relF , relXs) =
    mapG-rel A B (λ ys → chargeBase (! (listT B)) (sz (listT B) ys))
      gf f relF gxs xs relXs
  G-val dupS rel = (rel , rel)
  G-val (boxS f) rel = G-val f rel
  G-val (boxValS f) rel = G-val f rel
  G-val mergeS rel = rel
  G-val (mapS {A} {B} f) {gxs} {xs} relXs =
    mapG-rel A B (λ ys → chargeBase (! (listT B)) (sz (listT B) ys))
      ⟦ f ⟧G ⟦ f ⟧V (λ gx x rx → G-val f {gx} {x} rx) gxs xs relXs
  G-val (iterS {A} f) {gn , ga} {n , a} (refl , relA) =
    iterG-rel A (λ x → chargeBase (! A) (sz A x)) n
      ⟦ f ⟧G ⟦ f ⟧V (λ gx x rx → G-val f {gx} {x} rx) ga a relA
  G-val (foldS {A} {B} f) {gxs , gb} {xs , b} (relXs , relB) =
    foldG-rel A B (λ x → chargeBase (! B) (sz B x))
      ⟦ f ⟧G ⟦ f ⟧V (λ gb' b' gx x rb rx → G-val f {gb' , gx} {b' , x} (rb , rx))
      gxs xs relXs gb b relB
  G-val (whileS {A} t s) {gn , ga} {n , a} (refl , relA) =
    whileG-rel A n ⟦ t ⟧G ⟦ t ⟧V ⟦ s ⟧G ⟦ s ⟧V
      (λ gx x rx → G-val t {gx} {x} rx)
      (λ gx x rx → G-val s {gx} {x} rx)
      ga a relA

-- ── The three measured instances ────────────────────────────────────────────

-- Work (tel): 1 per natOut look, 1 per apply (paid before the body's
-- dynamic grade), 1 per taken loop step; everything else free; boxes
-- free (their contents pay when run).
workAlg : CostAlgebra
workAlg = record
  { ℳ = ℕ ; _⋄_ = _+_ ; _∥_ = _+_
  ; chargePrim  = λ _ _ t _ _ → chargeW t
  ; chargeStep  = 1
  ; chargeBase  = λ _ _ → 0
  ; chargeProbe = λ _ _ → 0
  }
  where
    chargeW : PrimTag → ℕ
    chargeW natOutT = 1
    chargeW applyT  = 1
    chargeW _       = 0

-- Dup grade: explicit accounting for copying.
-- Zero on all affine code; input size at dupS (THE charge) and at copyS
-- (costed data copy — the charge IS the license), 1 at dupNatS (atom
-- exemption), and size per guardS/whileS probe: a test reads the value
-- it does not consume, and that read is a copy.
dupAlg : CostAlgebra
dupAlg = record
  { ℳ = ℕ ; _⋄_ = _+_ ; _∥_ = _+_
  ; chargePrim  = chargeD
  ; chargeStep  = 0
  ; chargeBase  = λ _ _ → 0
  ; chargeProbe = λ _ sz → sz
  }
  where
    chargeD : (A B : Ty) → PrimTag → ℕ → ℕ → ℕ
    chargeD _ _ dupT    szA _ = szA
    chargeD _ _ dupNatT _   _ = 1
    chargeD _ _ copyT   szA _ = szA
    chargeD _ _ _       _   _ = 0

-- Space: (⊔,+) — sequential stages reuse memory, parallel branches
-- co-live; every leaf's peak is the larger of its input and output.
spaceAlg : CostAlgebra
spaceAlg = record
  { ℳ = ℕ ; _⋄_ = _⊔_ ; _∥_ = _+_
  ; chargePrim  = λ _ _ _ szA szB → szA ⊔ szB
  ; chargeStep  = 0
  ; chargeBase  = λ _ sz → sz
  ; chargeProbe = λ _ sz → sz
  }

open Interp workAlg  public using ()
  renaming (⟦_⟧G to ⟦_⟧C; G-val to C-val;
            mapG to mapGW; iterG to iterGW; foldG to foldGW;
            whileGo to whileGoW; whileG to whileGW)
open Interp dupAlg   public using () renaming (⟦_⟧G to ⟦_⟧D)
open Interp spaceAlg public using () renaming (⟦_⟧G to ⟦_⟧SP)

work : {A B : Ty} → A ⇨ B → GVal ℕ A → ℕ
work f a = proj₁ (⟦ f ⟧C a)

dupGrade : {A B : Ty} → A ⇨ B → GVal ℕ A → ℕ
dupGrade f a = proj₁ (⟦ f ⟧D a)

space : {A B : Ty} → A ⇨ B → GVal ℕ A → ℕ
space f a = proj₁ (⟦ f ⟧SP a)
