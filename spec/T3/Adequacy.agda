------------------------------------------------------------------------
-- T3.Adequacy — precision ⇒ adequacy, against the work instance.
--
-- CLOSURES make precision a Kripke logical relation: machine values
-- (KVal) and work-graded values (GVal ℕ) differ at arrows, where the
-- former is fuel-monadic and the latter carries its grade.  ≈P relates
-- them — structural equality below arrows; at A ⊸ B, related arguments
-- yield PRECISE computations: run the machine closure with the graded
-- closure's budget plus any slack and it returns a related value with
-- exactly the slack left (PreciseAt).  The fundamental lemma `precise`
-- extends the old propositional statement — which is recovered
-- definitionally at concrete first-order types, where KVal, GVal ℕ and
-- ⟦_⟧T coincide and ≈P collapses to structural equality (the Examples'
-- adequacy facts are refl).
--
-- ADEQUACY (extra = 0): run with the computed budget ⇒ always finishes,
-- with 0 fuel left, at a related value.  adequateV further connects the
-- output to the specification ⟦_⟧V via the graded relation ≈G.
--
-- The loop lemmas are parametric in the (machine, graded) function pair
-- and its relation evidence, so one lemma serves both the syntax-bodied
-- loops (mapS/iterS/foldS/whileS, instantiated with `precise` of the
-- body) and the closure-bodied mapCS (instantiated with the relation
-- carried by the closure value itself).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Adequacy where

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Nat             using (ℕ; zero; suc; _+_)
open import Data.Maybe           using (Maybe; just; nothing; _>>=_)
open import Data.Product         using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise
                                 using (Pointwise; []; _∷_)
open import Data.Unit            using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat.Properties  using (+-assoc; +-identityʳ)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value
open import T3.Sem.Graded
open import T3.Sem.Exec

-- ── The machine/graded logical relation ─────────────────────────────────────

≈P        : (A : Ty) → KVal A → GVal ℕ A → Set
PreciseAt : (B : Ty) → TelM (KVal B) → ℕ × GVal ℕ B → Set

≈P unit      _         _         = ⊤
≈P nat       m         n         = m ≡ n
≈P (A ⊗ B)   (ka , kb) (ga , gb) = ≈P A ka ga × ≈P B kb gb
≈P (A ⊕ B)   (inj₁ ka) (inj₁ ga) = ≈P A ka ga
≈P (A ⊕ B)   (inj₂ kb) (inj₂ gb) = ≈P B kb gb
≈P (A ⊕ B)   (inj₁ _)  (inj₂ _)  = ⊥
≈P (A ⊕ B)   (inj₂ _)  (inj₁ _)  = ⊥
≈P (listT A) kxs       gxs       = Pointwise (≈P A) kxs gxs
≈P (! A)     ka        ga        = ≈P A ka ga
≈P (A ⊸ B)   kf        gf        =
  ∀ ka ga → ≈P A ka ga → PreciseAt B (kf ka) (gf ga)

PreciseAt B m (n , gb) = ∀ extra →
  Σ (KVal B) λ kb → (m (n + extra) ≡ just (kb , extra)) × ≈P B kb gb

-- The relational precision property (successor of the old propositional
-- `Precise`; that statement is definitionally recovered at concrete
-- first-order endpoints).
Precise : {A B : Ty} → A ⇨ B → Set
Precise {A} {B} f = ∀ (ka : KVal A) (ga : GVal ℕ A)
                  → ≈P A ka ga → PreciseAt B (⟦ f ⟧K ka) (⟦ f ⟧C ga)

-- ── Parametric loop lemmas ──────────────────────────────────────────────────

private
  map-prec : (A B : Ty)
             (kh : KVal A →K KVal B) (gh : GVal ℕ A → ℕ × GVal ℕ B)
           → (∀ kx gx → ≈P A kx gx → PreciseAt B (kh kx) (gh gx))
           → ∀ kxs gxs → Pointwise (≈P A) kxs gxs
           → PreciseAt (! (listT B)) (mapT kxs kh) (mapGW (λ _ → 0) gxs gh)
  map-prec A B kh gh h [] [] [] extra = ([] , refl , [])
  map-prec A B kh gh h (kx ∷ kxs) (gx ∷ gxs) (rx ∷ rxs) extra =
    let m    = proj₁ (gh gx)
        r    = proj₁ (mapGW (λ _ → 0) gxs gh)
        resh = h kx gx rx (r + extra)
        ky   = proj₁ resh
        eqh  = subst (λ tel → kh kx tel ≡ just (ky , r + extra))
                     (sym (+-assoc m r extra)) (proj₁ (proj₂ resh))
        relY = proj₂ (proj₂ resh)
        resr = map-prec A B kh gh h kxs gxs rxs extra
        kys  = proj₁ resr
        eqr  = proj₁ (proj₂ resr)
        relYs = proj₂ (proj₂ resr)
    in ( ky ∷ kys
       , trans
           (cong (λ (mx : Maybe (KVal B × Tel)) → mx >>= λ { (y , t') →
                    mapT kxs kh t' >>= λ { (ys , t'') →
                      just (y ∷ ys , t'') } }) eqh)
           (cong (λ (mx : Maybe (List (KVal B) × Tel)) → mx >>= λ { (ys , t'') →
                    just (ky ∷ ys , t'') }) eqr)
       , relY ∷ relYs)

  iter-prec : (A : Ty)
              (kh : KVal A →K KVal A) (gh : GVal ℕ A → ℕ × GVal ℕ A)
            → (∀ kx gx → ≈P A kx gx → PreciseAt A (kh kx) (gh gx))
            → ∀ n ka ga → ≈P A ka ga
            → PreciseAt (! A) (iterT n kh ka) (iterGW (λ _ → 0) n gh ga)
  iter-prec A kh gh h zero    ka ga rel extra = (ka , refl , rel)
  iter-prec A kh gh h (suc n) ka ga rel extra =
    let m    = proj₁ (gh ga)
        gb   = proj₂ (gh ga)
        r    = proj₁ (iterGW (λ _ → 0) n gh gb)
        resh = h ka ga rel (r + extra)
        kb   = proj₁ resh
        eqh  = subst (λ tel → kh ka tel ≡ just (kb , r + extra))
                     (sym (+-assoc m r extra)) (proj₁ (proj₂ resh))
        relB = proj₂ (proj₂ resh)
        resr = iter-prec A kh gh h n kb gb relB extra
    in ( proj₁ resr
       , trans (cong (λ (mx : Maybe (KVal A × Tel)) → mx >>= λ { (v , t') → iterT n kh v t' }) eqh)
               (proj₁ (proj₂ resr))
       , proj₂ (proj₂ resr))

  fold-prec : (A B : Ty)
              (kh : (KVal B × KVal A) →K KVal B)
              (gh : (GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
            → (∀ kp gp → ≈P (B ⊗ A) kp gp → PreciseAt B (kh kp) (gh gp))
            → ∀ kxs gxs → Pointwise (≈P A) kxs gxs
            → ∀ kb gb → ≈P B kb gb
            → PreciseAt (! B) (foldT kxs kh kb) (foldGW (λ _ → 0) gxs gh gb)
  fold-prec A B kh gh h [] [] [] kb gb relB extra = (kb , refl , relB)
  fold-prec A B kh gh h (kx ∷ kxs) (gx ∷ gxs) (rx ∷ rxs) kb gb relB extra =
    let m    = proj₁ (gh (gb , gx))
        gb'  = proj₂ (gh (gb , gx))
        r    = proj₁ (foldGW (λ _ → 0) gxs gh gb')
        resh = h (kb , kx) (gb , gx) (relB , rx) (r + extra)
        kb'  = proj₁ resh
        eqh  = subst (λ tel → kh (kb , kx) tel ≡ just (kb' , r + extra))
                     (sym (+-assoc m r extra)) (proj₁ (proj₂ resh))
        relB' = proj₂ (proj₂ resh)
        resr = fold-prec A B kh gh h kxs gxs rxs kb' gb' relB' extra
    in ( proj₁ resr
       , trans (cong (λ (mx : Maybe (KVal B × Tel)) → mx >>= λ { (v , t') → foldT kxs kh v t' }) eqh)
               (proj₁ (proj₂ resr))
       , proj₂ (proj₂ resr))

  while-prec : (A : Ty)
               (kt : KVal A →K (⊤ ⊎ ⊤)) (gt : GVal ℕ A → ℕ × (⊤ ⊎ ⊤))
               (ks : KVal A →K KVal A)  (gs : GVal ℕ A → ℕ × GVal ℕ A)
             → (∀ kx gx → ≈P A kx gx
                → PreciseAt (unit ⊕ unit) (kt kx) (gt gx))
             → (∀ kx gx → ≈P A kx gx → PreciseAt A (ks kx) (gs gx))
             → ∀ n ka ga → ≈P A ka ga
             → PreciseAt (! A) (whileT n kt ks ka) (whileGW A n gt gs ga)
  while-prec A kt gt ks gs ht hs zero    ka ga rel extra = (ka , refl , rel)
  while-prec A kt gt ks gs ht hs (suc n) ka ga rel extra
    with proj₂ (gt ga)
       | ht ka ga rel extra
       | ht ka ga rel
           (suc (proj₁ (gs ga)
                 + proj₁ (whileGW A n gt gs (proj₂ (gs ga)))) + extra)
  ... | inj₁ _ | (inj₁ _ , eqt , _) | _ =
    ( ka
    , cong (λ (mx : Maybe ((⊤ ⊎ ⊤) × Tel)) → mx >>= λ { (r , t') → whileGoT n kt ks ka r t' }) eqt
    , rel)
  ... | inj₁ _ | (inj₂ _ , _ , ()) | _
  ... | inj₂ _ | _ | (inj₁ _ , _ , ())
  ... | inj₂ _ | _ | (inj₂ _ , eqt , _) =
    let mt   = proj₁ (gt ga)
        ms   = proj₁ (gs ga)
        gb   = proj₂ (gs ga)
        mr   = proj₁ (whileGW A n gt gs gb)
        eqt' = subst (λ tel → kt ka tel
                              ≡ just (inj₂ _ , suc (ms + mr) + extra))
                     (sym (+-assoc mt (suc (ms + mr)) extra)) eqt
        ress = hs ka ga rel (mr + extra)
        kb   = proj₁ ress
        eqs  = subst (λ tel → ks ka tel ≡ just (kb , mr + extra))
                     (sym (+-assoc ms mr extra)) (proj₁ (proj₂ ress))
        relB = proj₂ (proj₂ ress)
        resr = while-prec A kt gt ks gs ht hs n kb gb relB extra
    in ( proj₁ resr
       , trans (cong (λ (mx : Maybe ((⊤ ⊎ ⊤) × Tel)) → mx >>= λ { (r , t') →
                        whileGoT n kt ks ka r t' }) eqt')
         (trans (cong (λ (mx : Maybe (KVal A × Tel)) → mx >>= λ { (v , t') →
                        whileT n kt ks v t' }) eqs)
                (proj₁ (proj₂ resr)))
       , proj₂ (proj₂ resr))

  -- Bounded recursion: the machine runs the test then the body, and the
  -- body's own recur applications re-enter one fuel lower — so the whole
  -- recursion is carried by the recur closure's precision (rec-prec at n),
  -- not an outer tail recursion.  Exactly two fuel segments per unfold.
  rec-prec : (A B : Ty)
             (kt : KVal A →K (⊤ ⊎ ⊤)) (gt : GVal ℕ A → ℕ × (⊤ ⊎ ⊤))
             (kr : ((KVal A →K KVal B) × KVal A) →K KVal B)
             (gr : ((GVal ℕ A → ℕ × GVal ℕ B) × GVal ℕ A) → ℕ × GVal ℕ B)
             (kl : KVal A →K KVal B) (gl : GVal ℕ A → ℕ × GVal ℕ B)
           → (∀ kx gx → ≈P A kx gx → PreciseAt (unit ⊕ unit) (kt kx) (gt gx))
           → (∀ krec grec kx gx → ≈P (A ⊸ B) krec grec → ≈P A kx gx
              → PreciseAt B (kr (krec , kx)) (gr (grec , gx)))
           → (∀ kx gx → ≈P A kx gx → PreciseAt B (kl kx) (gl gx))
           → ∀ n ka ga → ≈P A ka ga
           → PreciseAt B (recT n kt kr kl ka) (recGW A B n gt gr gl ga)
  rec-prec A B kt gt kr gr kl gl ht hr hl zero    ka ga rel extra =
    hl ka ga rel extra
  rec-prec A B kt gt kr gr kl gl ht hr hl (suc n) ka ga rel extra
    with proj₂ (gt ga)
       | ht ka ga rel (proj₁ (gl ga) + extra)
       | ht ka ga rel
           (proj₁ (gr ((λ y → recGW A B n gt gr gl y) , ga)) + extra)
  ... | inj₁ _ | (inj₁ _ , eqt , _) | _ =
    let mt   = proj₁ (gt ga)
        ml   = proj₁ (gl ga)
        eqt' = subst (λ tel → kt ka tel ≡ just (inj₁ _ , ml + extra))
                     (sym (+-assoc mt ml extra)) eqt
        resl = hl ka ga rel extra
    in ( proj₁ resl
       , trans (cong (λ (mx : Maybe ((⊤ ⊎ ⊤) × Tel)) → mx >>= λ { (r , t') →
                        recGoT n kt kr kl ka r t' }) eqt')
               (proj₁ (proj₂ resl))
       , proj₂ (proj₂ resl))
  ... | inj₁ _ | (inj₂ _ , _ , ()) | _
  ... | inj₂ _ | _ | (inj₁ _ , _ , ())
  ... | inj₂ _ | _ | (inj₂ _ , eqt , _) =
    let mt   = proj₁ (gt ga)
        grec = λ y → recGW A B n gt gr gl y
        krec = λ y → recT n kt kr kl y
        mr   = proj₁ (gr (grec , ga))
        eqt' = subst (λ tel → kt ka tel ≡ just (inj₂ _ , mr + extra))
                     (sym (+-assoc mt mr extra)) eqt
        recPrec : ≈P (A ⊸ B) krec grec
        recPrec = λ ky gy rely →
                    rec-prec A B kt gt kr gr kl gl ht hr hl n ky gy rely
        resr = hr krec grec ka ga recPrec rel extra
    in ( proj₁ resr
       , trans (cong (λ (mx : Maybe ((⊤ ⊎ ⊤) × Tel)) → mx >>= λ { (r , t') →
                        recGoT n kt kr kl ka r t' }) eqt')
               (proj₁ (proj₂ resr))
       , proj₂ (proj₂ resr))

-- ── The fundamental lemma ───────────────────────────────────────────────────

precise : {A B : Ty} (f : A ⇨ B) → Precise f
precise idS ka ga rel extra = (ka , refl , rel)
precise (_∘S_ {A} {B} {C} g f) ka ga rel extra =
  let m    = proj₁ (⟦ f ⟧C ga)
      gb   = proj₂ (⟦ f ⟧C ga)
      r    = proj₁ (⟦ g ⟧C gb)
      resf = precise f ka ga rel (r + extra)
      kb   = proj₁ resf
      eqf  = subst (λ tel → ⟦ f ⟧K ka tel ≡ just (kb , r + extra))
                   (sym (+-assoc m r extra)) (proj₁ (proj₂ resf))
      relB = proj₂ (proj₂ resf)
      resg = precise g kb gb relB extra
  in ( proj₁ resg
     , trans (cong (λ (mx : Maybe (KVal B × Tel)) → mx >>= λ { (v , t') → ⟦ g ⟧K v t' }) eqf)
             (proj₁ (proj₂ resg))
     , proj₂ (proj₂ resg))
precise (_⊗S_ {A} {B} {C} {D} f g) (ka , kc) (ga , gc) (ra , rc) extra =
  let m    = proj₁ (⟦ f ⟧C ga)
      r    = proj₁ (⟦ g ⟧C gc)
      resf = precise f ka ga ra (r + extra)
      kb   = proj₁ resf
      eqf  = subst (λ tel → ⟦ f ⟧K ka tel ≡ just (kb , r + extra))
                   (sym (+-assoc m r extra)) (proj₁ (proj₂ resf))
      resg = precise g kc gc rc extra
      kd   = proj₁ resg
      eqg  = proj₁ (proj₂ resg)
  in ( (kb , kd)
     , trans
         (cong (λ (mx : Maybe (KVal B × Tel)) → mx >>= λ { (b , t') →
             ⟦ g ⟧K kc t' >>= λ { (d , t'') → just ((b , d) , t'') } }) eqf)
         (cong (λ (mx : Maybe (KVal D × Tel)) → mx >>= λ { (d , t'') → just ((kb , d) , t'') }) eqg)
     , (proj₂ (proj₂ resf) , proj₂ (proj₂ resg)))
precise swapS (ka , kb) (ga , gb) (ra , rb) extra =
  ((kb , ka) , refl , (rb , ra))
precise assocS ((ka , kb) , kc) ((ga , gb) , gc) ((ra , rb) , rc) extra =
  ((ka , (kb , kc)) , refl , (ra , (rb , rc)))
precise unassocS (ka , (kb , kc)) (ga , (gb , gc)) (ra , (rb , rc)) extra =
  (((ka , kb) , kc) , refl , ((ra , rb) , rc))
precise exlS (ka , _) (ga , _) (ra , _) extra = (ka , refl , ra)
precise exrS (_ , kb) (_ , gb) (_ , rb) extra = (kb , refl , rb)
precise weakS _ _ _ extra = (tt , refl , tt)
precise runitS ka ga rel extra = ((ka , tt) , refl , (rel , tt))
precise lunitS ka ga rel extra = ((tt , ka) , refl , (tt , rel))
precise inlS ka ga rel extra = (inj₁ ka , refl , rel)
precise inrS kb gb rel extra = (inj₂ kb , refl , rel)
precise (caseS l r) (inj₁ ka) (inj₁ ga) rel extra = precise l ka ga rel extra
precise (caseS l r) (inj₂ kb) (inj₂ gb) rel extra = precise r kb gb rel extra
precise (caseS l r) (inj₁ _) (inj₂ _) ()
precise (caseS l r) (inj₂ _) (inj₁ _) ()
precise distlS (ka , inj₁ kb) (ga , inj₁ gb) (ra , rb) extra =
  (inj₁ (ka , kb) , refl , (ra , rb))
precise distlS (ka , inj₂ kc) (ga , inj₂ gc) (ra , rc) extra =
  (inj₂ (ka , kc) , refl , (ra , rc))
precise distlS (ka , inj₁ kb) (ga , inj₂ gc) (ra , ())
precise distlS (ka , inj₂ kc) (ga , inj₁ gb) (ra , ())
precise nilS _ _ _ extra = ([] , refl , [])
precise consS (kx , kxs) (gx , gxs) (rx , rxs) extra =
  (kx ∷ kxs , refl , rx ∷ rxs)
precise unconsS [] [] [] extra = (inj₁ tt , refl , tt)
precise unconsS (kx ∷ kxs) (gx ∷ gxs) (rx ∷ rxs) extra =
  (inj₂ (kx , kxs) , refl , (rx , rxs))
precise natOutS zero .zero refl extra = (inj₁ tt , refl , tt)
precise natOutS (suc k) .(suc k) refl extra = (inj₂ k , refl , refl)
precise sucS n .n refl extra = (suc n , refl , refl)
precise addS (a , b) (.a , .b) (refl , refl) extra = (a + b , refl , refl)
precise (constS k) _ _ _ extra = (k , refl , refl)
precise dupNatS n .n refl extra = ((n , n) , refl , (refl , refl))
precise (copyS _) ka ga rel extra = ((ka , ka) , refl , (rel , rel))
precise (guardS t) ka ga rel extra
  with proj₂ (⟦ t ⟧C ga) | precise t ka ga rel extra
... | inj₁ _ | (inj₁ _ , eqt , _) =
  ( inj₁ ka
  , cong (λ (mx : Maybe ((⊤ ⊎ ⊤) × Tel)) → mx >>= λ { (r , t') → just (guardV ka r , t') }) eqt
  , rel)
... | inj₁ _ | (inj₂ _ , _ , ())
... | inj₂ _ | (inj₂ _ , eqt , _) =
  ( inj₂ tt
  , cong (λ (mx : Maybe ((⊤ ⊎ ⊤) × Tel)) → mx >>= λ { (r , t') → just (guardV ka r , t') }) eqt
  , tt)
... | inj₂ _ | (inj₁ _ , _ , ())
precise (curryS f) kc gc rel extra =
  ( (λ ka → ⟦ f ⟧K (kc , ka))
  , refl
  , λ ka ga relA → precise f (kc , ka) (gc , ga) (rel , relA))
precise applyS (kf , ka) (gf , ga) (relF , relA) extra =
  relF ka ga relA extra
precise (mapCS {A} {B}) (kf , kxs) (gf , gxs) (relF , relXs) extra =
  map-prec A B kf gf relF kxs gxs relXs extra
precise (iterCS {A}) (kf , (kn , ka)) (gf , (.kn , ga))
  (relF , (refl , relA)) extra =
  iter-prec A kf gf relF kn ka ga relA extra
precise (foldCS {A} {B}) (kf , (kxs , kb)) (gf , (gxs , gb))
  (relF , (relXs , relB)) extra =
  fold-prec A B kf gf (λ kp gp rp → relF kp gp rp)
    kxs gxs relXs kb gb relB extra
precise (whileCS {A}) (kt , (ks , (kn , ka))) (gt , (gs , (.kn , ga)))
  (relT , (relS , (refl , relA))) extra =
  while-prec A kt gt ks gs relT relS kn ka ga relA extra
precise (promoteS _) ka ga rel extra = (ka , refl , rel)
precise dupS ka ga rel extra = ((ka , ka) , refl , (rel , rel))
precise (boxS f) ka ga rel extra = precise f ka ga rel extra
precise (boxValS f) ka ga rel extra = precise f ka ga rel extra
precise mergeS kp gp rel extra = (kp , refl , rel)
precise (mapS {A} {B} f) kxs gxs relXs extra =
  map-prec A B ⟦ f ⟧K ⟦ f ⟧C (λ kx gx rx → precise f kx gx rx)
    kxs gxs relXs extra
precise (iterS {A} f) (kn , ka) (.kn , ga) (refl , relA) extra =
  iter-prec A ⟦ f ⟧K ⟦ f ⟧C (λ kx gx rx → precise f kx gx rx)
    kn ka ga relA extra
precise (foldS {A} {B} f) (kxs , kb) (gxs , gb) (relXs , relB) extra =
  fold-prec A B ⟦ f ⟧K ⟦ f ⟧C (λ kp gp rp → precise f kp gp rp)
    kxs gxs relXs kb gb relB extra
precise (whileS {A} t s) (kn , ka) (.kn , ga) (refl , relA) extra =
  while-prec A ⟦ t ⟧K ⟦ t ⟧C ⟦ s ⟧K ⟦ s ⟧C
    (λ kx gx rx → precise t kx gx rx)
    (λ kx gx rx → precise s kx gx rx)
    kn ka ga relA extra
precise (recS {A} {B} t r l) (kn , ka) (.kn , ga) (refl , relA) extra =
  rec-prec A B ⟦ t ⟧K ⟦ t ⟧C ⟦ r ⟧K ⟦ r ⟧C ⟦ l ⟧K ⟦ l ⟧C
    (λ kx gx rx → precise t kx gx rx)
    (λ krec grec kx gx relF relX → precise r (krec , kx) (grec , gx) (relF , relX))
    (λ kx gx rx → precise l kx gx rx)
    kn ka ga relA extra

-- ── ADEQUACY: run with the computed budget ⇒ finish with 0 left ────────────

adequate : {A B : Ty} (f : A ⇨ B) (ka : KVal A) (ga : GVal ℕ A)
         → ≈P A ka ga
         → Σ (KVal B) λ kb
           → (⟦ f ⟧K ka (work f ga) ≡ just (kb , 0))
             × ≈P B kb (proj₂ (⟦ f ⟧C ga))
adequate f ka ga rel =
  let res = precise f ka ga rel 0
  in ( proj₁ res
     , subst (λ tel → ⟦ f ⟧K ka tel ≡ just (proj₁ res , 0))
             (+-identityʳ (proj₁ (⟦ f ⟧C ga))) (proj₁ (proj₂ res))
     , proj₂ (proj₂ res))

-- The same, connected to the specification ⟦_⟧V via the graded relation:
-- the machine output relates to a graded output that relates to the
-- specification's value.
adequateV : {A B : Ty} (f : A ⇨ B)
            (ka : KVal A) (ga : GVal ℕ A) (a : ⟦ A ⟧T)
          → ≈P A ka ga → ≈G ℕ A ga a
          → Σ (KVal B) λ kb
            → (⟦ f ⟧K ka (work f ga) ≡ just (kb , 0))
              × ≈P B kb (proj₂ (⟦ f ⟧C ga))
              × ≈G ℕ B (proj₂ (⟦ f ⟧C ga)) (⟦ f ⟧V a)
adequateV f ka ga a relP relG =
  let res = adequate f ka ga relP
  in (proj₁ res , proj₁ (proj₂ res) , proj₂ (proj₂ res) , C-val f relG)
