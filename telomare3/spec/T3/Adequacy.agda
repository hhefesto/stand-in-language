------------------------------------------------------------------------
-- T3.Adequacy — precision ⇒ adequacy, against the work instance.
--
-- Ported from design/telomare2.agda §9 (itself the agda branch's §8e
-- technique), restated over the consolidated graded semantics: ⟦_⟧C below
-- is Interp workAlg (T3.Sem.Graded), so this single proof is the adequacy
-- statement for the whole CostAlgebra family's execution mirror.
--
-- PRECISION: running with the computed work budget plus any slack returns
-- the graded value with exactly the slack left.  ADEQUACY (extra = 0):
-- run with the computed budget ⇒ always finishes, with 0 fuel left.
-- adequateV restates the result against the specification ⟦_⟧V via the
-- generic value-coherence lemma C-val.
--
-- New cases over the predecessor: assocS/unassocS/lunitS (refl), guardS
-- (one cong through the test), whileS (the iter-prec pattern doubled: one
-- assoc-subst for the test, one for the step, case split on the test's
-- verdict).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Adequacy where

open import Data.Nat             using (ℕ; zero; suc; _+_)
open import Data.Maybe           using (Maybe; just; nothing; _>>=_)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_)
open import Data.Unit            using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat.Properties  using (+-assoc; +-identityʳ)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value
open import T3.Sem.Graded
open import T3.Sem.Exec

Precise : {A B : Ty} → A ⇨ B → Set
Precise {A} {B} f = ∀ (a : ⟦ A ⟧T) (extra : ℕ) →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a) + extra) ≡ just (proj₂ (⟦ f ⟧C a) , extra)

precise : {A B : Ty} → (f : A ⇨ B) → Precise f
precise idS         a extra = refl
precise (g ∘S f)    a extra =
  let n   = proj₁ (⟦ f ⟧C a)
      vf  = proj₂ (⟦ f ⟧C a)
      m   = proj₁ (⟦ g ⟧C vf)
      pf  = precise f a (m + extra)
      pf' = subst (λ tel → ⟦ f ⟧K a tel ≡ just (vf , m + extra))
                  (sym (+-assoc n m extra)) pf
      pg  = precise g vf extra
  in trans (cong (λ mx → mx >>= λ { (v , t') → ⟦ g ⟧K v t' }) pf') pg
precise (f ⊗S g) (a , c) extra =
  let n   = proj₁ (⟦ f ⟧C a)
      vf  = proj₂ (⟦ f ⟧C a)
      m   = proj₁ (⟦ g ⟧C c)
      vg  = proj₂ (⟦ g ⟧C c)
      pf  = precise f a (m + extra)
      pf' = subst (λ tel → ⟦ f ⟧K a tel ≡ just (vf , m + extra))
                  (sym (+-assoc n m extra)) pf
      pg  = precise g c extra
  in trans
       (cong (λ mx → mx >>= λ { (b , t') →
           ⟦ g ⟧K c t' >>= λ { (d , t'') → just ((b , d) , t'') } }) pf')
       (cong (λ mx → mx >>= λ { (d , t'') → just ((vf , d) , t'') }) pg)
precise swapS       (a , b) extra = refl
precise assocS      ((a , b) , c) extra = refl
precise unassocS    (a , (b , c)) extra = refl
precise exlS        (a , _) extra = refl
precise exrS        (_ , b) extra = refl
precise weakS       _       extra = refl
precise runitS      a       extra = refl
precise lunitS      a       extra = refl
precise inlS        a       extra = refl
precise inrS        b       extra = refl
precise (caseS l r) (inj₁ a) extra = precise l a extra
precise (caseS l r) (inj₂ b) extra = precise r b extra
precise distlS      (a , inj₁ b) extra = refl
precise distlS      (a , inj₂ c) extra = refl
precise nilS        _       extra = refl
precise consS       (x , xs) extra = refl
precise unconsS     []      extra = refl
precise unconsS     (x ∷ xs) extra = refl
precise natOutS     zero    extra = refl
precise natOutS     (suc n) extra = refl
precise sucS        n       extra = refl
precise addS        (a , b) extra = refl
precise (constS _)  _       extra = refl
precise dupNatS     n       extra = refl
precise (guardS t)  a extra =
  cong (λ mx → mx >>= λ { (r , t') → just (guardV a r , t') })
       (precise t a extra)
precise dupS        a       extra = refl
precise (boxS f)    a extra = precise f a extra
precise (boxValS f) a extra = precise f a extra
precise mergeS      p       extra = refl
precise (iterS f)   (n , a) extra = iter-prec n a extra
  where
    iter-prec : ∀ n a extra →
      iterT n ⟦ f ⟧K a (proj₁ (⟦ iterS f ⟧C (n , a)) + extra)
      ≡ just (proj₂ (⟦ iterS f ⟧C (n , a)) , extra)
    iter-prec zero    a extra = refl
    iter-prec (suc k) a extra =
      let cf  = proj₁ (⟦ f ⟧C a)
          vf  = proj₂ (⟦ f ⟧C a)
          cr  = proj₁ (⟦ iterS f ⟧C (k , vf))
          pf  = precise f a (cr + extra)
          pf' = subst (λ tel → ⟦ f ⟧K a tel ≡ just (vf , cr + extra))
                      (sym (+-assoc cf cr extra)) pf
          ih  = iter-prec k vf extra
      in trans (cong (λ mx → mx >>= λ { (v , t') → iterT k ⟦ f ⟧K v t' }) pf')
               ih
precise (foldS f)   (xs , b) extra = fold-prec xs b extra
  where
    fold-prec : ∀ xs b extra →
      foldT xs ⟦ f ⟧K b (proj₁ (⟦ foldS f ⟧C (xs , b)) + extra)
      ≡ just (proj₂ (⟦ foldS f ⟧C (xs , b)) , extra)
    fold-prec []       b extra = refl
    fold-prec (x ∷ xs) b extra =
      let cf  = proj₁ (⟦ f ⟧C (b , x))
          vf  = proj₂ (⟦ f ⟧C (b , x))
          cr  = proj₁ (⟦ foldS f ⟧C (xs , vf))
          pf  = precise f (b , x) (cr + extra)
          pf' = subst (λ tel → ⟦ f ⟧K (b , x) tel ≡ just (vf , cr + extra))
                      (sym (+-assoc cf cr extra)) pf
          ih  = fold-prec xs vf extra
      in trans (cong (λ mx → mx >>= λ { (v , t') → foldT xs ⟦ f ⟧K v t' }) pf')
               ih
precise (whileS t s) (n , a) extra = while-prec n a extra
  where
    while-prec : ∀ n a extra →
      whileT n ⟦ t ⟧K ⟦ s ⟧K a (proj₁ (⟦ whileS t s ⟧C (n , a)) + extra)
      ≡ just (proj₂ (⟦ whileS t s ⟧C (n , a)) , extra)
    while-prec zero    a extra = refl
    while-prec (suc k) a extra
      with proj₂ (⟦ t ⟧C a)
         | precise t a extra
         | precise t a (suc (proj₁ (⟦ s ⟧C a) +
                             proj₁ (⟦ whileS t s ⟧C (k , proj₂ (⟦ s ⟧C a))))
                        + extra)
    ... | inj₁ x | pf | _ =
      cong (λ mx → mx >>= λ { (r , t') → whileGoT k ⟦ t ⟧K ⟦ s ⟧K a r t' }) pf
    ... | inj₂ x | _ | pf =
      let mt   = proj₁ (⟦ t ⟧C a)
          ms   = proj₁ (⟦ s ⟧C a)
          b    = proj₂ (⟦ s ⟧C a)
          mr   = proj₁ (⟦ whileS t s ⟧C (k , b))
          pf'  = subst (λ tel → ⟦ t ⟧K a tel
                                ≡ just (inj₂ x , suc (ms + mr) + extra))
                       (sym (+-assoc mt (suc (ms + mr)) extra)) pf
          pfs  = precise s a (mr + extra)
          pfs' = subst (λ tel → ⟦ s ⟧K a tel ≡ just (b , mr + extra))
                       (sym (+-assoc ms mr extra)) pfs
          ih   = while-prec k b extra
      in trans (cong (λ mx → mx >>= λ { (r , t') →
                        whileGoT k ⟦ t ⟧K ⟦ s ⟧K a r t' }) pf')
         (trans (cong (λ mx → mx >>= λ { (v , t') →
                        whileT k ⟦ t ⟧K ⟦ s ⟧K v t' }) pfs')
                ih)

-- ADEQUACY: run with the computed budget ⇒ always finishes, with 0 left.
adequate : {A B : Ty} → (f : A ⇨ B) → ∀ a →
  ⟦ f ⟧K a (work f a) ≡ just (proj₂ (⟦ f ⟧C a) , 0)
adequate f a =
  subst (λ tel → ⟦ f ⟧K a tel ≡ just (proj₂ (⟦ f ⟧C a) , 0))
        (+-identityʳ (proj₁ (⟦ f ⟧C a)))
        (precise f a 0)

-- The same, phrased against the specification ⟦_⟧V (via value coherence).
adequateV : {A B : Ty} → (f : A ⇨ B) → ∀ a →
  ⟦ f ⟧K a (work f a) ≡ just (⟦ f ⟧V a , 0)
adequateV f a =
  trans (adequate f a) (cong (λ v → just (v , 0)) (C-val f a))
