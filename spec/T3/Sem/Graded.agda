------------------------------------------------------------------------
-- T3.Sem.Graded — ONE graded interpretation, many cost algebras.
--
-- Work, duplication, and space resource readings collapse into one interpretation ⟦_⟧G
-- parameterized by a CostAlgebra.  The execution semantics ⟦_⟧K
-- (T3.Sem.Exec) deliberately stays separate: it is not a grading but the
-- machine, and T3.Adequacy proves it precise against the work instance.
--
-- Value coherence is proved ONCE, generically: for every algebra R,
-- proj₂ ∘ ⟦_⟧G ≡ ⟦_⟧V (G-val).  This is the homomorphism obligation that
-- makes "resources = graded interpretations of the same syntax" a theorem
-- rather than a slogan.
--
-- Machine-independence: the cost object is the algebra's carrier ℳ; a backend
-- can interpret it through a monotone homomorphism without changing values.
--
-- towerHeight is NOT an instance (see T3.Core.Syntax): it is the sup over
-- all inputs, a quotient of the grade read directly off the syntax.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Sem.Graded where

open import Data.Nat     using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                         using (_≡_; refl; trans; cong; cong₂)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value

-- Leaf-primitive tags: what chargePrim discriminates on.  Structural
-- constructors (∘S, ⊗S, caseS, boxS, boxValS, guardS, iterS, foldS,
-- whileS) are interpreted recursively and charge through chargeStep /
-- chargeBase / chargeProbe instead.
data PrimTag : Set where
  idT swapT assocT unassocT exlT exrT weakT runitT lunitT
    inlT inrT distlT nilT consT unconsT
    natOutT sucT addT constT dupNatT dupT mergeT : PrimTag

record CostAlgebra : Set₁ where
  infixr 7 _⋄_
  infixr 6 _∥_
  field
    ℳ           : Set
    _⋄_         : ℳ → ℳ → ℳ      -- sequential composition of grades
    _∥_         : ℳ → ℳ → ℳ      -- parallel (tensor) composition
    chargePrim  : (A B : Ty) → PrimTag → ⟦ A ⟧T → ⟦ B ⟧T → ℳ
    chargeStep  : ℳ                -- per taken iterS/foldS/whileS step
    chargeBase  : (A : Ty) → ⟦ A ⟧T → ℳ
                                   -- at loop exhaustion/stop (space: live size)
    chargeProbe : (A : Ty) → ⟦ A ⟧T → ℳ
                                   -- guardS / whileS test: the implicit
                                   -- copy of the probed value, never free

module Interp (R : CostAlgebra) where
  open CostAlgebra R

  private
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
            → (⟦ A ⟧T → ℳ × (⊤ ⊎ ⊤)) → (⟦ A ⟧T → ℳ × ⟦ A ⟧T)
            → ⟦ A ⟧T → ℳ → ⊤ ⊎ ⊤ → ℳ × ⟦ A ⟧T
    whileG  : (A : Ty) → ℕ
            → (⟦ A ⟧T → ℳ × (⊤ ⊎ ⊤)) → (⟦ A ⟧T → ℳ × ⟦ A ⟧T)
            → ⟦ A ⟧T → ℳ × ⟦ A ⟧T

    whileGo A n t s a mt (inj₁ _) = (chargeProbe A a ⋄ mt , a)
    whileGo A n t s a mt (inj₂ _) =
      let (ms , b) = s a
          (r , c)  = whileG A n t s b
      in (chargeProbe A a ⋄ (mt ⋄ (chargeStep ⋄ (ms ⋄ r))) , c)

    whileG A zero    t s a = (chargeBase (! A) a , a)
    whileG A (suc n) t s a = let (mt , r) = t a in whileGo A n t s a mt r

  ⟦_⟧G : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ℳ × ⟦ B ⟧T
  ⟦_⟧G {A} idS a = (chargePrim A A idT a a , a)
  ⟦ g ∘S f ⟧G a =
    let (m , b) = ⟦ f ⟧G a
        (r , c) = ⟦ g ⟧G b
    in (m ⋄ r , c)
  ⟦ f ⊗S g ⟧G (a , c) =
    let (m , b) = ⟦ f ⟧G a
        (r , d) = ⟦ g ⟧G c
    in (m ∥ r , (b , d))
  ⟦ swapS {A} {B} ⟧G p@(a , b) =
    (chargePrim (A ⊗ B) (B ⊗ A) swapT p (b , a) , (b , a))
  ⟦ assocS {A} {B} {C} ⟧G p@((a , b) , c) =
    (chargePrim ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C)) assocT p (a , (b , c)) , (a , (b , c)))
  ⟦ unassocS {A} {B} {C} ⟧G p@(a , (b , c)) =
    (chargePrim (A ⊗ (B ⊗ C)) ((A ⊗ B) ⊗ C) unassocT p ((a , b) , c) , ((a , b) , c))
  ⟦ exlS {A} {B} ⟧G p@(a , _) = (chargePrim (A ⊗ B) A exlT p a , a)
  ⟦ exrS {A} {B} ⟧G p@(_ , b) = (chargePrim (A ⊗ B) B exrT p b , b)
  ⟦ weakS {A} ⟧G a = (chargePrim A unit weakT a tt , tt)
  ⟦ runitS {A} ⟧G a = (chargePrim A (A ⊗ unit) runitT a (a , tt) , (a , tt))
  ⟦ lunitS {A} ⟧G a = (chargePrim A (unit ⊗ A) lunitT a (tt , a) , (tt , a))
  ⟦ inlS {A} {B} ⟧G a = (chargePrim A (A ⊕ B) inlT a (inj₁ a) , inj₁ a)
  ⟦ inrS {A} {B} ⟧G b = (chargePrim B (A ⊕ B) inrT b (inj₂ b) , inj₂ b)
  ⟦ caseS l r ⟧G (inj₁ a) = ⟦ l ⟧G a
  ⟦ caseS l r ⟧G (inj₂ b) = ⟦ r ⟧G b
  ⟦ distlS {A} {B} {C} ⟧G p@(a , inj₁ b) =
    (chargePrim (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C)) distlT p (inj₁ (a , b))
    , inj₁ (a , b))
  ⟦ distlS {A} {B} {C} ⟧G p@(a , inj₂ c) =
    (chargePrim (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C)) distlT p (inj₂ (a , c))
    , inj₂ (a , c))
  ⟦ nilS {A} ⟧G u = (chargePrim unit (listT A) nilT u [] , [])
  ⟦ consS {A} ⟧G p@(x , xs) =
    (chargePrim (A ⊗ listT A) (listT A) consT p (x ∷ xs) , (x ∷ xs))
  ⟦ unconsS {A} ⟧G [] =
    (chargePrim (listT A) (unit ⊕ (A ⊗ listT A)) unconsT [] (inj₁ tt) , inj₁ tt)
  ⟦ unconsS {A} ⟧G l@(x ∷ xs) =
    (chargePrim (listT A) (unit ⊕ (A ⊗ listT A)) unconsT l (inj₂ (x , xs))
    , inj₂ (x , xs))
  ⟦ natOutS ⟧G zero = (chargePrim nat (unit ⊕ nat) natOutT zero (inj₁ tt) , inj₁ tt)
  ⟦ natOutS ⟧G n@(suc k) =
    (chargePrim nat (unit ⊕ nat) natOutT n (inj₂ k) , inj₂ k)
  ⟦ sucS ⟧G n = (chargePrim nat nat sucT n (suc n) , suc n)
  ⟦ addS ⟧G p@(a , b) = (chargePrim (nat ⊗ nat) nat addT p (a + b) , a + b)
  ⟦ constS {A} k ⟧G a = (chargePrim A nat constT a k , k)
  ⟦ dupNatS ⟧G n = (chargePrim nat (nat ⊗ nat) dupNatT n (n , n) , (n , n))
  ⟦ guardS {A} t ⟧G a =
    let (mt , r) = ⟦ t ⟧G a
    in (chargeProbe A a ⋄ mt , guardV a r)
  ⟦ dupS {A} ⟧G a = (chargePrim (! A) (! A ⊗ ! A) dupT a (a , a) , (a , a))
  ⟦ boxS f ⟧G a = ⟦ f ⟧G a
  ⟦ boxValS f ⟧G a = ⟦ f ⟧G a
  ⟦ mergeS {A} {B} ⟧G p = (chargePrim (! A ⊗ ! B) (! (A ⊗ B)) mergeT p p , p)
  ⟦ iterS {A} f ⟧G (n , a) = iterG (chargeBase (! A)) n ⟦ f ⟧G a
  ⟦ foldS {A} {B} f ⟧G (xs , b) = foldG (chargeBase (! B)) xs ⟦ f ⟧G b
  ⟦ whileS {A} t s ⟧G (n , a) = whileG A n ⟦ t ⟧G ⟦ s ⟧G a

  -- Value coherence, proved once for every algebra: the graded semantics
  -- computes the specification's value.
  private
    iterG-val : {A : Set} (base : A → ℳ) (n : ℕ)
                (fg : A → ℳ × A) (fv : A → A)
              → (∀ x → proj₂ (fg x) ≡ fv x)
              → ∀ a → proj₂ (iterG base n fg a) ≡ iterV n fv a
    iterG-val base zero    fg fv h a = refl
    iterG-val base (suc n) fg fv h a =
      trans (cong (λ b → proj₂ (iterG base n fg b)) (h a))
            (iterG-val base n fg fv h (fv a))

    foldG-val : {A B : Set} (base : B → ℳ) (xs : List A)
                (fg : (B × A) → ℳ × B) (fv : B × A → B)
              → (∀ x → proj₂ (fg x) ≡ fv x)
              → ∀ b → proj₂ (foldG base xs fg b) ≡ foldV xs fv b
    foldG-val base []       fg fv h b = refl
    foldG-val base (x ∷ xs) fg fv h b =
      trans (cong (λ b' → proj₂ (foldG base xs fg b')) (h (b , x)))
            (foldG-val base xs fg fv h (fv (b , x)))

    whileGo-val : (A : Ty) (n : ℕ)
                  (tg : ⟦ A ⟧T → ℳ × (⊤ ⊎ ⊤)) (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤)
                  (sg : ⟦ A ⟧T → ℳ × ⟦ A ⟧T) (sv : ⟦ A ⟧T → ⟦ A ⟧T)
                → (∀ x → proj₂ (tg x) ≡ tv x) → (∀ x → proj₂ (sg x) ≡ sv x)
                → ∀ a mt r
                → proj₂ (whileGo A n tg sg a mt r) ≡ whileV-go n tv sv a r
    whileG-val  : (A : Ty) (n : ℕ)
                  (tg : ⟦ A ⟧T → ℳ × (⊤ ⊎ ⊤)) (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤)
                  (sg : ⟦ A ⟧T → ℳ × ⟦ A ⟧T) (sv : ⟦ A ⟧T → ⟦ A ⟧T)
                → (∀ x → proj₂ (tg x) ≡ tv x) → (∀ x → proj₂ (sg x) ≡ sv x)
                → ∀ a → proj₂ (whileG A n tg sg a) ≡ whileV n tv sv a

    whileGo-val A n tg tv sg sv ht hs a mt (inj₁ _) = refl
    whileGo-val A n tg tv sg sv ht hs a mt (inj₂ _) =
      trans (cong (λ b → proj₂ (whileG A n tg sg b)) (hs a))
            (whileG-val A n tg tv sg sv ht hs (sv a))

    whileG-val A zero    tg tv sg sv ht hs a = refl
    whileG-val A (suc n) tg tv sg sv ht hs a =
      trans (whileGo-val A n tg tv sg sv ht hs a (proj₁ (tg a)) (proj₂ (tg a)))
            (cong (whileV-go n tv sv a) (ht a))

  G-val : {A B : Ty} (f : A ⇨ B) (a : ⟦ A ⟧T)
        → proj₂ (⟦ f ⟧G a) ≡ ⟦ f ⟧V a
  G-val idS a = refl
  G-val (g ∘S f) a =
    trans (cong (λ b → proj₂ (⟦ g ⟧G b)) (G-val f a)) (G-val g (⟦ f ⟧V a))
  G-val (f ⊗S g) (a , c) = cong₂ _,_ (G-val f a) (G-val g c)
  G-val swapS (a , b) = refl
  G-val assocS ((a , b) , c) = refl
  G-val unassocS (a , (b , c)) = refl
  G-val exlS (a , _) = refl
  G-val exrS (_ , b) = refl
  G-val weakS a = refl
  G-val runitS a = refl
  G-val lunitS a = refl
  G-val inlS a = refl
  G-val inrS b = refl
  G-val (caseS l r) (inj₁ a) = G-val l a
  G-val (caseS l r) (inj₂ b) = G-val r b
  G-val distlS (a , inj₁ b) = refl
  G-val distlS (a , inj₂ c) = refl
  G-val nilS u = refl
  G-val consS (x , xs) = refl
  G-val unconsS [] = refl
  G-val unconsS (x ∷ xs) = refl
  G-val natOutS zero = refl
  G-val natOutS (suc n) = refl
  G-val sucS n = refl
  G-val addS (a , b) = refl
  G-val (constS k) a = refl
  G-val dupNatS n = refl
  G-val (guardS t) a = cong (guardV a) (G-val t a)
  G-val dupS a = refl
  G-val (boxS f) a = G-val f a
  G-val (boxValS f) a = G-val f a
  G-val mergeS p = refl
  G-val (iterS f) (n , a) =
    iterG-val _ n ⟦ f ⟧G ⟦ f ⟧V (G-val f) a
  G-val (foldS f) (xs , b) =
    foldG-val _ xs ⟦ f ⟧G ⟦ f ⟧V (G-val f) b
  G-val (whileS {A} t s) (n , a) =
    whileG-val A n ⟦ t ⟧G ⟦ t ⟧V ⟦ s ⟧G ⟦ s ⟧V (G-val t) (G-val s) a

-- ── The three measured instances ────────────────────────────────────────────

-- Work (tel): 1 per natOut look, per taken loop step; everything else free;
-- boxes free (their contents pay when run).
-- charge-for-charge, so the §10 example numbers carry over verbatim.
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
    chargeW _       = 0

-- Dup grade: explicit accounting for copying.
-- Zero on all affine code; sizeT at dupS (THE charge), 1 at dupNatS (atom
-- exemption), and sizeT per guardS/whileS probe: a
-- test reads the value it does not consume, and that read is a copy.
dupAlg : CostAlgebra
dupAlg = record
  { ℳ = ℕ ; _⋄_ = _+_ ; _∥_ = _+_
  ; chargePrim  = chargeD
  ; chargeStep  = 0
  ; chargeBase  = λ _ _ → 0
  ; chargeProbe = λ A a → sizeT A a
  }
  where
    chargeD : (A B : Ty) → PrimTag → ⟦ A ⟧T → ⟦ B ⟧T → ℕ
    chargeD A B dupT    a b = sizeT A a
    chargeD A B dupNatT a b = 1
    chargeD _ _ _       _ _ = 0

-- Space: (⊔,+) — sequential stages reuse memory, parallel branches
-- co-live; every leaf's peak is the larger of its input and output.
spaceAlg : CostAlgebra
spaceAlg = record
  { ℳ = ℕ ; _⋄_ = _⊔_ ; _∥_ = _+_
  ; chargePrim  = λ A B _ a b → sizeT A a ⊔ sizeT B b
  ; chargeStep  = 0
  ; chargeBase  = λ A a → sizeT A a
  ; chargeProbe = λ A a → sizeT A a
  }

open Interp workAlg  public using () renaming (⟦_⟧G to ⟦_⟧C; G-val to C-val)
open Interp dupAlg   public using () renaming (⟦_⟧G to ⟦_⟧D)
open Interp spaceAlg public using () renaming (⟦_⟧G to ⟦_⟧SP)

work : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ℕ
work f a = proj₁ (⟦ f ⟧C a)

dupGrade : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ℕ
dupGrade f a = proj₁ (⟦ f ⟧D a)

space : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ℕ
space f a = proj₁ (⟦ f ⟧SP a)
