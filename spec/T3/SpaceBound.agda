------------------------------------------------------------------------
-- T3.SpaceBound — the certified static space bound (design/SPACE.md).
--
-- T3.Sem.Space computes the EXACT live-heap peak of a run.  This module
-- derives an A-PRIORI bound: spaceS over the T3.Abstract Shape domain
-- returns an upper bound in ℕ∞, and spaceS-sound proves the actual peak
-- of any covered input never exceeds it.  Allocate that many words and
-- the run cannot exhaust them.
--
-- The structure mirrors T3.Bound (costW/costW-sound) with the space
-- combinators: sequential stages combine by ⊔∞ (memory is reused), a
-- tensor adds the retained sibling's static size, loops retain the
-- un-consumed container per round and join rounds by ⊔∞ (aiterSp also
-- charges the current shape's size every round, so an early dynamic
-- stop is dominated without a static invariant), and a map's produced
-- prefix is retained through the rest of the traversal (mapSpC).
--
-- The Kripke relation is T3.Bound's γW unchanged: ⟦_⟧S's closures carry
-- their space peak as their grade, so lollyS bounds read off directly.
-- mapCS carries only the closure's peak bound, not its result shape, so
-- its prefix retention is bounded through topS element sizes — finite
-- only at atomic element types (flagged in design/SPACE.md).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.SpaceBound where

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Nat             using (ℕ; zero; suc; pred; _+_; _⊔_;
                                        _≤_; z≤n; s≤s)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; +-mono-≤;
                                        ⊔-lub; m≤n+m; n≤1+n)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Unit            using (⊤; tt)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Graded        using (GVal; sizeG)
open import T3.Sem.Space
open import T3.Abstract          using (Shape; topS; unitS; natLE; pairS;
                                        sumS; listS; bangS; lollyS; _⊔S_;
                                        splitP; splitE; unbang; fuelOf;
                                        lenOf; elemOf)
open import T3.Bound             using (ℕ∞; _+∞_; _⊔∞_; _≤∞_; ≤∞-zero;
                                        ≤∞-+; ≤∞-suc; ≤∞-⊔l; ≤∞-⊔r;
                                        ≤∞-wksuc; sizeS; listSizeS;
                                        lollyCostOf; γW; γWMaybe;
                                        sizeS-sound; unbang-γW;
                                        ⊔S-lW; ⊔S-rW; list-size-bound;
                                        shapeOfTy; γW-shapeOfTy)

-- ── ℕ∞ helpers for ⊔ ───────────────────────────────────────────────────────

≤∞-⊔₂ : {a b : ℕ} (z : ℕ∞) → a ≤∞ z → b ≤∞ z → (a ⊔ b) ≤∞ z
≤∞-⊔₂ nothing  _  _  = tt
≤∞-⊔₂ (just _) ha hb = ⊔-lub ha hb

≤∞-+nothing : (x : ℕ∞) {a : ℕ} → a ≤∞ (x +∞ nothing)
≤∞-+nothing nothing  = tt
≤∞-+nothing (just _) = tt

-- ── Static loop combinators ────────────────────────────────────────────────

-- Fuel-bounded abstract unrolling for the space reading: rounds combine
-- by ⊔∞; every round also charges the current shape's size, so a
-- dynamic run that stops early (its state still live) is dominated.
aiterSp : {A : Ty} → (Shape A → ℕ∞ × Shape A) → ℕ → Shape A → ℕ∞ × Shape A
aiterSp f zero    s = (sizeS s , s)
aiterSp f (suc n) s =
  let (c₁ , s₁) = f s
      (cₙ , sₙ) = aiterSp f n s₁
  in (sizeS s ⊔∞ (c₁ ⊔∞ cₙ) , s ⊔S sₙ)

-- Static mirror of mapSp: the un-consumed tail is retained through each
-- round, the produced element through the rest of the traversal.
mapSpC : {A B : Ty} → ℕ → Shape A → Shape B → ℕ∞ → ℕ∞
mapSpC zero    es re cb = just 1
mapSpC (suc n) es re cb =
  (listSizeS n es +∞ cb) ⊔∞ (sizeS re +∞ mapSpC n es re cb)

one≤mapSpC : {A B : Ty} (n : ℕ) (es : Shape A) (re : Shape B) (cb : ℕ∞)
           → 1 ≤∞ mapSpC n es re cb
one≤mapSpC zero    es re cb = s≤s z≤n
one≤mapSpC (suc n) es re cb =
  ≤∞-⊔r (listSizeS n es +∞ cb) (sizeS re +∞ mapSpC n es re cb)
    (embed (sizeS re) (mapSpC n es re cb) (one≤mapSpC n es re cb))
  where
    embed : (x y : ℕ∞) → 1 ≤∞ y → 1 ≤∞ (x +∞ y)
    embed nothing  _        _ = tt
    embed (just _) nothing  _ = tt
    embed (just r) (just k) h = ≤-trans h (m≤n+m k r)

-- ── The analysis ───────────────────────────────────────────────────────────

spaceS : {A B : Ty} (f : A ⇨ B) → Shape A → ℕ∞ × Shape B
spaceS idS          s = (sizeS s , s)
spaceS (g ∘S f)     s =
  let (cf , sf) = spaceS f s
      (cg , sg) = spaceS g sf
  in (cf ⊔∞ cg , sg)
spaceS (f ⊗S g)     s =
  let (sa , sc) = splitP s
      (cf , sb) = spaceS f sa
      (cg , sd) = spaceS g sc
  in ((sizeS sc +∞ cf) ⊔∞ (sizeS sb +∞ cg) , pairS sb sd)
spaceS swapS        s = let (a , b) = splitP s in (sizeS s , pairS b a)
spaceS assocS       s =
  let (ab , c) = splitP s ; (a , b) = splitP ab
  in (sizeS s , pairS a (pairS b c))
spaceS unassocS     s =
  let (a , bc) = splitP s ; (b , c) = splitP bc
  in (sizeS s , pairS (pairS a b) c)
spaceS exlS         s = (sizeS s , proj₁ (splitP s))
spaceS exrS         s = (sizeS s , proj₂ (splitP s))
spaceS weakS        s = (sizeS s , unitS)
spaceS runitS       s = (just 1 +∞ sizeS s , pairS s unitS)
spaceS lunitS       s = (just 1 +∞ sizeS s , pairS unitS s)
spaceS inlS         s = (just 1 +∞ sizeS s , sumS (just s) nothing)
spaceS inrS         s = (just 1 +∞ sizeS s , sumS nothing (just s))
spaceS (caseS l r)  s =
  let (ml , mr) = splitE s
  in (sizeS s ⊔∞ (costMB (mapMB (spaceS l) ml) ⊔∞ costMB (mapMB (spaceS r) mr))
     , joinResC (mapMB (spaceS l) ml) (mapMB (spaceS r) mr))
  where
    mapMB : {A B : Ty}
          → (Shape A → ℕ∞ × Shape B)
          → Maybe (Shape A) → Maybe (ℕ∞ × Shape B)
    mapMB f (just x) = just (f x)
    mapMB _ nothing  = nothing
    costMB : {B : Ty} → Maybe (ℕ∞ × Shape B) → ℕ∞
    costMB (just (c , _)) = c
    costMB nothing        = just 0
    joinResC : {B : Ty}
             → Maybe (ℕ∞ × Shape B) → Maybe (ℕ∞ × Shape B) → Shape B
    joinResC (just (_ , x)) (just (_ , y)) = x ⊔S y
    joinResC (just (_ , x)) nothing        = x
    joinResC nothing        (just (_ , y)) = y
    joinResC nothing        nothing        = topS
spaceS distlS       s =
  let (a , bc) = splitP s
      (mb , mc) = splitE bc
  in (sizeS s , sumS (wrapC a mb) (wrapC a mc))
  where
    wrapC : {X Y : Ty} → Shape X → Maybe (Shape Y) → Maybe (Shape (X ⊗ Y))
    wrapC x (just y) = just (pairS x y)
    wrapC _ nothing  = nothing
spaceS nilS         s = (just 1 , listS 0 topS)
spaceS consS        s =
  let (e , l) = splitP s
  in (just 1 +∞ sizeS s , listSucC e l)
  where
    listSucC : {A : Ty} → Shape A → Shape (listT A) → Shape (listT A)
    listSucC e (listS n es) = listS (suc n) (e ⊔S es)
    listSucC e topS         = topS
spaceS unconsS      s = (just 1 +∞ sizeS s
  , sumS (just unitS) (just (pairS (elemOf s) (predListC s))))
  where
    predListC : {A : Ty} → Shape (listT A) → Shape (listT A)
    predListC (listS n es) = listS (pred n) es
    predListC topS         = topS
spaceS natOutS      s = (just 2 , outC s)
  where
    outC : Shape nat → Shape (unit ⊕ nat)
    outC (natLE n) = sumS (just unitS) (just (natLE (pred n)))
    outC topS      = sumS (just unitS) (just topS)
spaceS sucS         s = (just 1 , sucC s)
  where
    sucC : Shape nat → Shape nat
    sucC (natLE n) = natLE (suc n)
    sucC topS      = topS
spaceS addS         s =
  let (a , b) = splitP s in (just 2 , addC a b)
  where
    addC : Shape nat → Shape nat → Shape nat
    addC (natLE n) (natLE m) = natLE (n + m)
    addC _         _         = topS
spaceS (constS k)   s = (sizeS s , natLE k)
spaceS dupNatS      s = (just 2 , pairS s s)
spaceS (copyS _)    s = (sizeS s +∞ sizeS s , pairS s s)
spaceS (guardS t)   s =
  (proj₁ (spaceS t s) ⊔∞ (just 1 +∞ sizeS s) , sumS (just s) (just unitS))
spaceS (curryS f)   s =
  (sizeS s , lollyS (proj₁ (spaceS f (pairS s topS))))
spaceS applyS       s =
  let (sf , sa) = splitP s
  in ((just 1 +∞ sizeS sa) ⊔∞ lollyCostOf sf , topS)
spaceS (mapCS {A} {B}) s =
  let (sbf , sl) = splitP s
  in (goC (lenOf sl) (elemOf sl) (lollyCostOf (unbang sbf)) , topS)
  where
    goC : Maybe ℕ → Shape A → ℕ∞ → ℕ∞
    goC nothing  _  _  = nothing
    goC (just n) es mc = just 1 +∞ mapSpC n es (topS {B}) mc
spaceS (promoteS _) s = (sizeS s , bangS s)
spaceS dupS         s = (sizeS s +∞ sizeS s , pairS s s)
spaceS (boxS f)     s = let (c , r) = spaceS f (unbang s) in (c , bangS r)
spaceS (boxValS f)  s = let (c , r) = spaceS f s in (c , bangS r)
spaceS mergeS       s =
  let (a , b) = splitP s in (sizeS s , bangS (pairS (unbang a) (unbang b)))
spaceS (mapS {A} {B} f) s =
  (goC (lenOf s) (elemOf s) , topS)
  where
    goC : Maybe ℕ → Shape A → ℕ∞
    goC nothing  _  = nothing
    goC (just n) es = mapSpC n es (proj₂ (spaceS f es)) (proj₁ (spaceS f es))
spaceS (iterS f)    s =
  let (fu , a0) = splitP s
  in loopC (fuelOf fu) (unbang a0)
  where
    loopC : Maybe ℕ → Shape _ → ℕ∞ × Shape _
    loopC (just n) a0 =
      let (c , r) = aiterSp (spaceS f) n a0
      in (just 1 +∞ c , bangS r)
    loopC nothing  a0 = (nothing , topS)
spaceS (foldS {A} {B} f) s =
  let (ls , b0) = splitP s
  in loopC (lenOf ls) (elemOf ls) (unbang b0)
  where
    loopC : Maybe ℕ → Shape A → Shape B → ℕ∞ × Shape (! B)
    loopC (just n) es a0 =
      let (c , r) = aiterSp
            (λ x → (listSizeS n es +∞ proj₁ (spaceS f (pairS x es))
                   , proj₂ (spaceS f (pairS x es)))) n a0
      in (sizeS s ⊔∞ c , bangS r)
    loopC nothing  _  a0 = (nothing , topS)
spaceS (whileS t st) s =
  let (fu , a0) = splitP s
  in loopC (fuelOf fu) (unbang a0)
  where
    stepC : Shape _ → ℕ∞ × Shape _
    stepC x =
      let ct = proj₁ (spaceS t x)
          (cs , r) = spaceS st x
      in (ct ⊔∞ cs , r)
    loopC : Maybe ℕ → Shape _ → ℕ∞ × Shape _
    loopC (just n) a0 =
      let (c , r) = aiterSp stepC n a0
      in (just 1 +∞ c , bangS r)
    loopC nothing  a0 = (nothing , topS)

-- ── Loop bound lemmas ──────────────────────────────────────────────────────

private
  iterSp-bound : (A : Ty) (fC : Shape A → ℕ∞ × Shape A)
                 (fG : GVal ℕ A → ℕ × GVal ℕ A)
               → (h : ∀ x {ga} → γW A x ga
                    → (proj₁ (fG ga) ≤∞ proj₁ (fC x))
                      × γW A (proj₂ (fC x)) (proj₂ (fG ga)))
               → ∀ n k (s : Shape A) {ga} → k ≤ n → γW A s ga
               → (proj₁ (iterSp A fG k ga) ≤∞ proj₁ (aiterSp fC n s))
                 × γW A (proj₂ (aiterSp fC n s))
                        (proj₂ (iterSp A fG k ga))
  iterSp-bound A fC fG h zero    zero    s rel-kn rel = (sizeS-sound s rel , rel)
  iterSp-bound A fC fG h (suc n) zero    s rel-kn rel =
    (≤∞-⊔l _ _ (sizeS-sound s rel) , ⊔S-lW s _ rel)
  iterSp-bound A fC fG h (suc n) (suc k) s {ga} (s≤s kn) rel =
    let (hb , relB) = h s rel
        (ihc , ihs) = iterSp-bound A fC fG h n k (proj₂ (fC s))
                        {proj₂ (fG ga)} kn relB
    in ( ≤∞-⊔₂ _
           (≤∞-⊔r (sizeS s) _ (≤∞-⊔l _ _ hb))
           (≤∞-⊔r (sizeS s) _ (≤∞-⊔r _ _ ihc))
       , ⊔S-rW s _ ihs)

  foldSp-bound : (A B : Ty) (N : ℕ) (es : Shape A)
                 (sC : Shape B → ℕ∞ × Shape B)
                 (fG : (GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
               → (h : ∀ x {gb ge} → γW B x gb → γW A es ge
                    → (proj₁ (fG (gb , ge)) ≤∞ proj₁ (sC x))
                      × γW B (proj₂ (sC x)) (proj₂ (fG (gb , ge))))
               → ∀ n xs (s : Shape B) {gb} → n ≤ N → length xs ≤ n
               → All (γW A es) xs → γW B s gb
               → (proj₁ (foldSp A B fG xs gb)
                  ≤∞ proj₁ (aiterSp
                    (λ x → (listSizeS N es +∞ proj₁ (sC x) , proj₂ (sC x)))
                    n s))
                 × γW B (proj₂ (aiterSp
                    (λ x → (listSizeS N es +∞ proj₁ (sC x) , proj₂ (sC x)))
                    n s))
                        (proj₂ (foldSp A B fG xs gb))
  foldSp-bound A B N es sC fG h zero [] s nN hl hall rel =
    (sizeS-sound s rel , rel)
  foldSp-bound A B N es sC fG h (suc n) [] s nN hl hall rel =
    (≤∞-⊔l _ _ (sizeS-sound s rel) , ⊔S-lW s _ rel)
  foldSp-bound A B N es sC fG h (suc n) (x ∷ xs) s {gb}
    nN (s≤s hl) (hx ∷ hall) rel =
    let (hb , relB) = h s rel hx
        (ihc , ihs) = foldSp-bound A B N es sC fG h n xs (proj₂ (sC s))
                        {proj₂ (fG (gb , x))} (≤-trans (n≤1+n n) nN)
                        hl hall relB
        tail-le = list-size-bound A es N xs
                    (≤-trans hl (≤-trans (n≤1+n n) nN)) hall
    in ( ≤∞-⊔₂ _
           (≤∞-⊔r (sizeS s) _ (≤∞-⊔l _ _ (≤∞-+ _ _ tail-le hb)))
           (≤∞-⊔r (sizeS s) _ (≤∞-⊔r _ _ ihc))
       , ⊔S-rW s _ ihs)

  whileSp-bound : (A : Ty) (tC : Shape A → ℕ∞)
                  (sC : Shape A → ℕ∞ × Shape A)
                  (tG : GVal ℕ A → ℕ × (⊤ ⊎ ⊤))
                  (sG : GVal ℕ A → ℕ × GVal ℕ A)
                → (ht : ∀ x {ga} → γW A x ga → proj₁ (tG ga) ≤∞ tC x)
                → (hs : ∀ x {ga} → γW A x ga
                     → (proj₁ (sG ga) ≤∞ proj₁ (sC x))
                       × γW A (proj₂ (sC x)) (proj₂ (sG ga)))
                → ∀ n k (s : Shape A) {ga} → k ≤ n → γW A s ga
                → (proj₁ (whileSp A k tG sG ga)
                   ≤∞ proj₁ (aiterSp
                     (λ x → (tC x ⊔∞ proj₁ (sC x) , proj₂ (sC x))) n s))
                  × γW A (proj₂ (aiterSp
                     (λ x → (tC x ⊔∞ proj₁ (sC x) , proj₂ (sC x))) n s))
                         (proj₂ (whileSp A k tG sG ga))
  whileSp-bound A tC sC tG sG ht hs zero zero s kn rel =
    (sizeS-sound s rel , rel)
  whileSp-bound A tC sC tG sG ht hs (suc n) zero s kn rel =
    (≤∞-⊔l _ _ (sizeS-sound s rel) , ⊔S-lW s _ rel)
  whileSp-bound A tC sC tG sG ht hs (suc n) (suc k) s {ga} (s≤s kn) rel
    with proj₂ (tG ga)
  ... | inj₁ _ =
    ( ≤∞-⊔₂ _
        (≤∞-⊔r (sizeS s) _ (≤∞-⊔l _ _ (≤∞-⊔l _ _ (ht s rel))))
        (≤∞-⊔l _ _ (sizeS-sound s rel))
    , ⊔S-lW s _ rel)
  ... | inj₂ _ =
    let (hsc , relB) = hs s rel
        (ihc , ihs) = whileSp-bound A tC sC tG sG ht hs n k (proj₂ (sC s))
                        {proj₂ (sG ga)} kn relB
    in ( ≤∞-⊔₂ _
           (≤∞-⊔r (sizeS s) _ (≤∞-⊔l _ _ (≤∞-⊔l _ _ (ht s rel))))
           (≤∞-⊔₂ _
             (≤∞-⊔r (sizeS s) _ (≤∞-⊔l _ _ (≤∞-⊔r _ _ hsc)))
             (≤∞-⊔r (sizeS s) _ (≤∞-⊔r _ _ ihc)))
       , ⊔S-rW s _ ihs)

  mapSp-bound : (A B : Ty) (es : Shape A) (re : Shape B) (cb : ℕ∞)
                (fG : GVal ℕ A → ℕ × GVal ℕ B)
              → (h : ∀ x → γW A es x
                   → (proj₁ (fG x) ≤∞ cb) × γW B re (proj₂ (fG x)))
              → ∀ n xs → length xs ≤ n → All (γW A es) xs
              → proj₁ (mapSp A B fG xs) ≤∞ mapSpC n es re cb
  mapSp-bound A B es re cb fG h zero [] hl hall = s≤s z≤n
  mapSp-bound A B es re cb fG h (suc n) [] hl hall =
    one≤mapSpC (suc n) es re cb
  mapSp-bound A B es re cb fG h (suc n) (x ∷ xs) (s≤s hl) (hx ∷ hall) =
    let (hb , hy) = h x hx
        ih = mapSp-bound A B es re cb fG h n xs hl hall
        tail-le = list-size-bound A es n xs hl hall
    in ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (≤∞-+ _ _ tail-le hb))
         (≤∞-⊔r _ _ (≤∞-+ _ _ (sizeS-sound re hy) ih))

-- ── THE THEOREM: static space bound ────────────────────────────────────────

spaceS-sound : {A B : Ty} (f : A ⇨ B) (s : Shape A) {ga : GVal ℕ A}
             → γW A s ga
             → (proj₁ (⟦ f ⟧S ga) ≤∞ proj₁ (spaceS f s))
               × γW B (proj₂ (spaceS f s)) (proj₂ (⟦ f ⟧S ga))
spaceS-sound idS s h = (sizeS-sound s h , h)
spaceS-sound (g ∘S f) s h =
  let (cf , rf) = spaceS-sound f s h
      (cg , rg) = spaceS-sound g (proj₂ (spaceS f s)) rf
  in ( ≤∞-⊔₂ _ (≤∞-⊔l _ _ cf) (≤∞-⊔r _ _ cg)
     , rg)
spaceS-sound (_⊗S_ {A} {B} {C} {D} f g) topS {a , c} h =
  let (cf , rf) = spaceS-sound f topS {a} tt
      (cg , rg) = spaceS-sound g topS {c} tt
  in ( ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (≤∞-+ _ _ (sizeS-sound (topS {C}) tt) cf))
         (≤∞-⊔r _ _ (≤∞-+ _ _ (sizeS-sound (proj₂ (spaceS f topS)) rf) cg))
     , (rf , rg))
spaceS-sound (_⊗S_ {A} {B} {C} {D} f g) (pairS sa sc) {a , c} (ha , hc) =
  let (cf , rf) = spaceS-sound f sa ha
      (cg , rg) = spaceS-sound g sc hc
  in ( ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (≤∞-+ _ _ (sizeS-sound sc hc) cf))
         (≤∞-⊔r _ _ (≤∞-+ _ _ (sizeS-sound (proj₂ (spaceS f sa)) rf) cg))
     , (rf , rg))
spaceS-sound swapS topS h = (tt , (tt , tt))
spaceS-sound swapS (pairS a b) (ha , hb) =
  (≤∞-+ _ _ (sizeS-sound a ha) (sizeS-sound b hb) , (hb , ha))
spaceS-sound assocS topS h = (tt , (tt , (tt , tt)))
spaceS-sound assocS (pairS topS c) {(_ , _) , _} (_ , hc) =
  (tt , (tt , (tt , hc)))
spaceS-sound assocS (pairS (pairS a b) c) ((ha , hb) , hc) =
  ( ≤∞-+ _ _ (≤∞-+ _ _ (sizeS-sound a ha) (sizeS-sound b hb))
      (sizeS-sound c hc)
  , (ha , (hb , hc)))
spaceS-sound unassocS topS h = (tt , ((tt , tt) , tt))
spaceS-sound unassocS (pairS a topS) {_ , (_ , _)} (ha , _) =
  (≤∞-+ _ _ (sizeS-sound a ha) tt , ((ha , tt) , tt))
spaceS-sound unassocS (pairS a (pairS b c)) (ha , (hb , hc)) =
  ( ≤∞-+ _ _ (sizeS-sound a ha)
      (≤∞-+ _ _ (sizeS-sound b hb) (sizeS-sound c hc))
  , ((ha , hb) , hc))
spaceS-sound exlS topS h = (tt , tt)
spaceS-sound exlS (pairS a b) (ha , hb) =
  (≤∞-+ _ _ (sizeS-sound a ha) (sizeS-sound b hb) , ha)
spaceS-sound exrS topS h = (tt , tt)
spaceS-sound exrS (pairS a b) (ha , hb) =
  (≤∞-+ _ _ (sizeS-sound a ha) (sizeS-sound b hb) , hb)
spaceS-sound weakS s h = (sizeS-sound s h , tt)
spaceS-sound runitS s h = (≤∞-suc _ (sizeS-sound s h) , (h , tt))
spaceS-sound lunitS s h = (≤∞-suc _ (sizeS-sound s h) , (tt , h))
spaceS-sound inlS s h = (≤∞-suc _ (sizeS-sound s h) , h)
spaceS-sound inrS s h = (≤∞-suc _ (sizeS-sound s h) , h)
spaceS-sound (caseS l r) topS {inj₁ a} h =
  let (cl , rl) = spaceS-sound l topS {a} tt
  in (tt , ⊔S-lW (proj₂ (spaceS l topS)) (proj₂ (spaceS r topS)) rl)
spaceS-sound (caseS l r) topS {inj₂ b} h =
  let (cr , rr) = spaceS-sound r topS {b} tt
  in (tt , ⊔S-rW (proj₂ (spaceS l topS)) (proj₂ (spaceS r topS)) rr)
spaceS-sound (caseS {A} {B} {C} l r) (sumS (just sl) mr) {inj₁ a} h with mr
... | just sr =
  let (cl , rl) = spaceS-sound l sl h
  in ( ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (sizeS-sound (sumS (just sl) (just sr)) {inj₁ a} h))
         (≤∞-⊔r _ _ (≤∞-⊔l _ _ cl))
     , ⊔S-lW (proj₂ (spaceS l sl)) (proj₂ (spaceS r sr)) rl)
... | nothing =
  let (cl , rl) = spaceS-sound l sl h
  in ( ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (sizeS-sound (sumS {A} {B} (just sl) nothing) {inj₁ a} h))
         (≤∞-⊔r _ _ (≤∞-⊔l _ _ cl))
     , rl)
spaceS-sound (caseS l r) (sumS nothing mr) {inj₁ a} h = ⊥-elim h
spaceS-sound (caseS {A} {B} {C} l r) (sumS ml (just sr)) {inj₂ b} h with ml
... | just sl =
  let (cr , rr) = spaceS-sound r sr h
  in ( ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (sizeS-sound (sumS (just sl) (just sr)) {inj₂ b} h))
         (≤∞-⊔r _ _ (≤∞-⊔r _ _ cr))
     , ⊔S-rW (proj₂ (spaceS l sl)) (proj₂ (spaceS r sr)) rr)
... | nothing =
  let (cr , rr) = spaceS-sound r sr h
  in ( ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (sizeS-sound (sumS {A} {B} nothing (just sr)) {inj₂ b} h))
         (≤∞-⊔r _ _ (≤∞-⊔r _ _ cr))
     , rr)
spaceS-sound (caseS l r) (sumS ml nothing) {inj₂ b} h = ⊥-elim h
spaceS-sound distlS topS {a , inj₁ b} h = (tt , (tt , tt))
spaceS-sound distlS topS {a , inj₂ c} h = (tt , (tt , tt))
spaceS-sound (distlS {A} {B} {C}) (pairS sa topS) {a , inj₁ b} (ha , _) =
  ( sizeS-sound (pairS sa (topS {B ⊕ C})) {a , inj₁ b} (ha , tt)
  , (ha , tt))
spaceS-sound (distlS {A} {B} {C}) (pairS sa topS) {a , inj₂ c} (ha , _) =
  ( sizeS-sound (pairS sa (topS {B ⊕ C})) {a , inj₂ c} (ha , tt)
  , (ha , tt))
spaceS-sound distlS (pairS sa (sumS (just sb) mc)) {a , inj₁ b} (ha , hb) =
  ( sizeS-sound (pairS sa (sumS (just sb) mc)) {a , inj₁ b} (ha , hb)
  , (ha , hb))
spaceS-sound distlS (pairS sa (sumS nothing mc)) {a , inj₁ b} (ha , hb) =
  ⊥-elim hb
spaceS-sound distlS (pairS sa (sumS mb (just sc))) {a , inj₂ c} (ha , hc) =
  ( sizeS-sound (pairS sa (sumS mb (just sc))) {a , inj₂ c} (ha , hc)
  , (ha , hc))
spaceS-sound distlS (pairS sa (sumS mb nothing)) {a , inj₂ c} (ha , hc) =
  ⊥-elim hc
spaceS-sound nilS s h = (s≤s z≤n , (z≤n , []))
spaceS-sound consS topS {x , xs} h = (tt , tt)
spaceS-sound consS (pairS se topS) {x , xs} (he , _) =
  (≤∞-suc _ (≤∞-+ _ _ (sizeS-sound se he) tt) , tt)
spaceS-sound consS (pairS se (listS n ses)) {x , xs} (he , (hl , hes)) =
  ( ≤∞-suc _ (≤∞-+ _ _ (sizeS-sound se he)
      (sizeS-sound (listS n ses) (hl , hes)))
  , (s≤s hl , ⊔S-lW se ses he ∷ All.map (λ {y} → ⊔S-rW se ses {y}) hes))
spaceS-sound unconsS s {[]} h =
  (≤∞-suc _ (sizeS-sound s h) , tt)
spaceS-sound unconsS topS {x ∷ xs} h = (tt , (tt , tt))
spaceS-sound unconsS (listS n se) {x ∷ xs} (hl , hx ∷ hxs) =
  ( ≤∞-wksuc _ (sizeS-sound (listS n se) (hl , hx ∷ hxs))
  , (hx , (pred-len n hl , hxs)))
  where
    pred-len : ∀ {m} n → suc m ≤ n → m ≤ pred n
    pred-len (suc k) (s≤s p) = p
spaceS-sound natOutS topS {zero} h = (s≤s (s≤s z≤n) , tt)
spaceS-sound natOutS topS {suc m} h = (s≤s (s≤s z≤n) , tt)
spaceS-sound natOutS (natLE n) {zero} h = (s≤s (s≤s z≤n) , tt)
spaceS-sound natOutS (natLE n) {suc m} h = (s≤s (s≤s z≤n) , pred-le h)
  where
    pred-le : ∀ {m n} → suc m ≤ n → m ≤ pred n
    pred-le (s≤s p) = p
spaceS-sound sucS topS h = (s≤s z≤n , tt)
spaceS-sound sucS (natLE n) h = (s≤s z≤n , s≤s h)
spaceS-sound addS topS h = (s≤s (s≤s z≤n) , tt)
spaceS-sound addS (pairS topS _) h = (s≤s (s≤s z≤n) , tt)
spaceS-sound addS (pairS (natLE n) topS) h = (s≤s (s≤s z≤n) , tt)
spaceS-sound addS (pairS (natLE n) (natLE m)) (ha , hb) =
  (s≤s (s≤s z≤n) , +-mono-≤ ha hb)
spaceS-sound (constS k) s h = (sizeS-sound s h , ≤-refl)
spaceS-sound dupNatS s h = (s≤s (s≤s z≤n) , (h , h))
spaceS-sound (copyS _) s h =
  (≤∞-+ _ _ (sizeS-sound s h) (sizeS-sound s h) , (h , h))
spaceS-sound (guardS t) s {ga} h
  with proj₂ (⟦ t ⟧S ga) | spaceS-sound t s {ga} h
... | inj₁ _ | (ct , _) =
  ( ≤∞-⊔₂ _ (≤∞-⊔l _ _ ct) (≤∞-⊔r _ _ (≤∞-suc _ (sizeS-sound s h)))
  , h)
... | inj₂ _ | (ct , _) =
  ( ≤∞-⊔₂ _ (≤∞-⊔l _ _ ct) (≤∞-⊔r _ _ (≤∞-suc _ (sizeS-sound s h)))
  , tt)
spaceS-sound (curryS f) s h =
  ( sizeS-sound s h
  , λ ga → proj₁ (spaceS-sound f (pairS s topS) {_ , ga} (h , tt)))
spaceS-sound (applyS {A} {B}) topS {gf , ga} h =
  (≤∞-⊔r (just 1 +∞ sizeS (topS {A})) nothing tt , tt)
spaceS-sound (applyS {A} {B}) (pairS topS sa) {gf , ga} h =
  (≤∞-⊔r (just 1 +∞ sizeS sa) nothing tt , tt)
spaceS-sound applyS (pairS (lollyS mc) sa) {gf , ga} (relF , ha) =
  ( ≤∞-⊔₂ _
      (≤∞-⊔l _ _ (≤∞-suc _ (sizeS-sound sa ha)))
      (≤∞-⊔r _ _ (relF ga))
  , tt)
spaceS-sound mapCS topS h = (tt , tt)
spaceS-sound mapCS (pairS sbf topS) h = (tt , tt)
spaceS-sound (mapCS {A} {B}) (pairS topS (listS n es)) {gf , gxs}
  (_ , (hlen , hall)) = (go n gxs hlen , tt)
  where
    go : ∀ n xs → length xs ≤ n
       → suc (proj₁ (mapSp A B gf xs))
         ≤∞ (just 1 +∞ mapSpC n es (topS {B}) nothing)
    go zero    [] hl = s≤s (s≤s z≤n)
    go (suc m) xs hl =
      ≤∞-suc _ (≤∞-⊔l _ _ (≤∞-+nothing (listSizeS m es)))
    go zero (_ ∷ _) ()
spaceS-sound (mapCS {A} {B}) (pairS (bangS topS) (listS n es)) {gf , gxs}
  (_ , (hlen , hall)) = (go n gxs hlen , tt)
  where
    go : ∀ n xs → length xs ≤ n
       → suc (proj₁ (mapSp A B gf xs))
         ≤∞ (just 1 +∞ mapSpC n es (topS {B}) nothing)
    go zero    [] hl = s≤s (s≤s z≤n)
    go (suc m) xs hl =
      ≤∞-suc _ (≤∞-⊔l _ _ (≤∞-+nothing (listSizeS m es)))
    go zero (_ ∷ _) ()
spaceS-sound (mapCS {A} {B}) (pairS (bangS (lollyS mc)) (listS n es))
  {gf , gxs} (relF , (hlen , hall)) =
  ( ≤∞-suc _ (mapSp-bound A B es (topS {B}) mc gf
      (λ x _ → (relF x , tt)) n gxs hlen hall)
  , tt)
spaceS-sound (promoteS _) s h = (sizeS-sound s h , h)
spaceS-sound dupS s h =
  (≤∞-+ _ _ (sizeS-sound s h) (sizeS-sound s h) , (h , h))
spaceS-sound (boxS f) topS h =
  let (c , r) = spaceS-sound f topS tt in (c , r)
spaceS-sound (boxS f) (bangS s) h =
  let (c , r) = spaceS-sound f s h in (c , r)
spaceS-sound (boxValS f) s h =
  let (c , r) = spaceS-sound f s h in (c , r)
spaceS-sound mergeS topS {a , b} h = (tt , (tt , tt))
spaceS-sound mergeS (pairS topS sb) {a , b} (_ , hb) =
  (tt , (tt , unbang-γW sb hb))
spaceS-sound (mergeS {A} {B}) (pairS (bangS sa) sb) {a , b} (ha , hb) =
  ( ≤∞-+ _ _ (sizeS-sound (bangS sa) {a} ha) (sizeS-sound sb {b} hb)
  , (ha , unbang-γW sb hb))
spaceS-sound (mapS f) topS h = (tt , tt)
spaceS-sound (mapS {A} {B} f) (listS n es) {gxs} (hlen , hall) =
  ( mapSp-bound A B es (proj₂ (spaceS f es)) (proj₁ (spaceS f es)) ⟦ f ⟧S
      (λ x hx → spaceS-sound f es {x} hx) n gxs hlen hall
  , tt)
spaceS-sound (iterS f) topS {gn , ga} h = (tt , tt)
spaceS-sound (iterS f) (pairS topS a0) {gn , ga} h = (tt , tt)
spaceS-sound (iterS {A} f) (pairS (natLE N) a0) {gn , ga} (hn , ha) =
  let (c , r) = iterSp-bound A (spaceS f) ⟦ f ⟧S
                  (λ x {gx} rel → spaceS-sound f x {gx} rel)
                  N gn (unbang a0) {ga} hn (unbang-γW a0 ha)
  in (≤∞-suc _ c , r)
spaceS-sound (foldS f) topS {gxs , gb} h = (tt , tt)
spaceS-sound (foldS f) (pairS topS b0) {gxs , gb} h = (tt , tt)
spaceS-sound (foldS {A} {B} f) (pairS (listS N es) b0) {gxs , gb}
  ((hlen , hxs) , hb) =
  let (c , r) = foldSp-bound A B N es (λ x → spaceS f (pairS x es)) ⟦ f ⟧S
                  (λ x {gb′} {ge} relB he →
                    spaceS-sound f (pairS x es) {gb′ , ge} (relB , he))
                  N gxs (unbang b0) {gb} ≤-refl hlen hxs (unbang-γW b0 hb)
  in ( ≤∞-⊔₂ _
         (≤∞-⊔l _ _ (sizeS-sound (pairS (listS N es) b0) ((hlen , hxs) , hb)))
         (≤∞-⊔r _ _ c)
     , r)
spaceS-sound (whileS t st) topS {gn , ga} h = (tt , tt)
spaceS-sound (whileS t st) (pairS topS a0) {gn , ga} h = (tt , tt)
spaceS-sound (whileS {A} t st) (pairS (natLE N) a0) {gn , ga} (hn , ha) =
  let (c , r) = whileSp-bound A (λ x → proj₁ (spaceS t x)) (spaceS st)
                  ⟦ t ⟧S ⟦ st ⟧S
                  (λ x {gx} rel → proj₁ (spaceS-sound t x {gx} rel))
                  (λ x {gx} rel → spaceS-sound st x {gx} rel)
                  N gn (unbang a0) {ga} hn (unbang-γW a0 ha)
  in (≤∞-suc _ c , r)

-- ── Entry-point corollaries ────────────────────────────────────────────────

-- Certified static space bound at a covered input shape.
space-bounded-at : {A B : Ty} (f : A ⇨ B) (s : Shape A) {ga : GVal ℕ A}
                 → γW A s ga → spacePeak f ga ≤∞ proj₁ (spaceS f s)
space-bounded-at f s h = proj₁ (spaceS-sound f s h)

-- Certified static space bound for an arbitrary input.
space-bounded : {A B : Ty} (f : A ⇨ B) (ga : GVal ℕ A)
              → spacePeak f ga ≤∞ proj₁ (spaceS f (shapeOfTy A))
space-bounded {A} f ga = space-bounded-at f (shapeOfTy A) (γW-shapeOfTy A ga)
