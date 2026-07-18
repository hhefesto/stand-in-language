------------------------------------------------------------------------
-- T3.Bound — the certified static work bound (milestone R3, work slice).
--
-- The graded semantics computes the EXACT work of each run (T3.Sem.Graded
-- workAlg; by T3.Adequacy that number is exactly the fuel the machine
-- needs).  This module derives an A-PRIORI bound: an abstract
-- interpretation costW over the T3.Abstract Shape domain returns an
-- upper bound in ℕ∞ (Maybe ℕ, nothing = unbounded), and costW-sound
-- proves the actual work of any covered input never exceeds it.
-- Composed with adequacy, a static bound IS a fuel bound: run the
-- machine with that much fuel and it always completes.
--
-- Work only charges counts — 1 per natOut look, 1 per apply, 1 per
-- taken loop step — so this analysis needs no size machinery at all.
-- Duplication/space bounds need a static size domain and are a separate
-- future slice.
--
-- Closures: a topS arrow shape can never bound applyS, so the domain's
-- lollyS carries the closure's body-cost bound and the work relation γW
-- interprets it Kripke-style over work-graded values (a closure carries
-- its own grade — GVal ℕ (A ⊸ B) = GVal ℕ A → ℕ × GVal ℕ B): a covered
-- closure costs at most the carried bound on EVERY argument.  curryS
-- discharges it by bounding its body at an unknown (topS) argument.
--
-- Loops are bounded by fuel-many abstract unrollings (aiterC), summing
-- 1 + step-cost per round with shapes joined over every prefix — the
-- cost analogue of T3.Abstract.aiter, proved by the same induction shape
-- as aiter-covers.  A while's early stop only drops nonnegative terms,
-- so the full-unroll sum dominates every actual run.
--
-- costW computes its own output shapes (T3.Abstract.transfer stays
-- untouched); they may differ from transfer's — only γW-soundness
-- matters here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Bound where

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Nat             using (ℕ; zero; suc; pred; _+_; _*_;
                                        _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; +-mono-≤;
                                        m≤m⊔n; m≤n⊔m; m≤m+n; +-assoc;
                                        +-suc; n≤1+n)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Unit            using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; subst)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value using (guardV)
open import T3.Sem.Graded
open import T3.Abstract using (Shape; topS; unitS; natLE; pairS; sumS;
                               listS; bangS; lollyS; _⊔S_; joinMB;
                               splitP; splitE; unbang; fuelOf; lenOf;
                               elemOf)

-- ── ℕ∞ cost arithmetic ─────────────────────────────────────────────────────

ℕ∞ : Set
ℕ∞ = Maybe ℕ

infixl 6 _+∞_
_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
just a +∞ just b = just (a + b)
_      +∞ _      = nothing

infixl 6 _⊔∞_
_⊔∞_ : ℕ∞ → ℕ∞ → ℕ∞
_⊔∞_ = joinMB

_*∞_ : ℕ∞ → ℕ∞ → ℕ∞
just a *∞ just b = just (a * b)
_      *∞ _      = nothing

infix 4 _≤∞_
_≤∞_ : ℕ → ℕ∞ → Set
n ≤∞ nothing = ⊤
n ≤∞ just m  = n ≤ m

≤∞-zero : (x : ℕ∞) → 0 ≤∞ x
≤∞-zero nothing  = tt
≤∞-zero (just _) = z≤n

≤∞-+ : {a b : ℕ} (x y : ℕ∞) → a ≤∞ x → b ≤∞ y → (a + b) ≤∞ (x +∞ y)
≤∞-+ nothing  _        _  _  = tt
≤∞-+ (just _) nothing  _  _  = tt
≤∞-+ (just _) (just _) ha hb = +-mono-≤ ha hb

≤∞-suc : {a : ℕ} (x : ℕ∞) → a ≤∞ x → suc a ≤∞ (just 1 +∞ x)
≤∞-suc nothing  _ = tt
≤∞-suc (just _) h = s≤s h

≤∞-⊔l : {a : ℕ} (x y : ℕ∞) → a ≤∞ x → a ≤∞ (x ⊔∞ y)
≤∞-⊔l nothing  _        _ = tt
≤∞-⊔l (just _) nothing  _ = tt
≤∞-⊔l (just m) (just n) h = ≤-trans h (m≤m⊔n m n)

≤∞-⊔r : {a : ℕ} (x y : ℕ∞) → a ≤∞ y → a ≤∞ (x ⊔∞ y)
≤∞-⊔r nothing  _        _ = tt
≤∞-⊔r (just _) nothing  _ = tt
≤∞-⊔r (just m) (just n) h = ≤-trans h (m≤n⊔m m n)

-- weaken through a +∞ on the right, and through the round's leading suc
≤∞-padr : {a : ℕ} (x y : ℕ∞) → a ≤∞ x → a ≤∞ (x +∞ y)
≤∞-padr nothing  _        _ = tt
≤∞-padr (just _) nothing  _ = tt
≤∞-padr (just m) (just n) h = ≤-trans h (m≤m+n m n)

≤∞-wksuc : {a : ℕ} (x : ℕ∞) → a ≤∞ x → a ≤∞ (just 1 +∞ x)
≤∞-wksuc nothing  _ = tt
≤∞-wksuc (just m) h = ≤-trans h (n≤1+n m)

-- ── The analysis ───────────────────────────────────────────────────────────

lollyCostOf : {A B : Ty} → Shape (A ⊸ B) → ℕ∞
lollyCostOf (lollyS mc) = mc
lollyCostOf topS        = nothing

-- Fuel-bounded abstract unrolling accumulating cost: one chargeStep plus
-- the round's own bound per unrolling, shapes joined over every prefix.
aiterC : {A : Ty} → (Shape A → ℕ∞ × Shape A) → ℕ → Shape A → ℕ∞ × Shape A
aiterC f zero    s = (just 0 , s)
aiterC f (suc n) s =
  let (c₁ , s₁) = f s
      (cₙ , sₙ) = aiterC f n s₁
  in (just 1 +∞ (c₁ +∞ cₙ) , s ⊔S sₙ)

costW : {A B : Ty} (f : A ⇨ B) → Shape A → ℕ∞ × Shape B
costW idS          s = (just 0 , s)
costW (g ∘S f)     s =
  let (cf , sf) = costW f s
      (cg , sg) = costW g sf
  in (cf +∞ cg , sg)
costW (f ⊗S g)     s =
  let (sa , sc) = splitP s
      (cf , sb) = costW f sa
      (cg , sd) = costW g sc
  in (cf +∞ cg , pairS sb sd)
costW swapS        s = let (a , b) = splitP s in (just 0 , pairS b a)
costW assocS       s =
  let (ab , c) = splitP s ; (a , b) = splitP ab
  in (just 0 , pairS a (pairS b c))
costW unassocS     s =
  let (a , bc) = splitP s ; (b , c) = splitP bc
  in (just 0 , pairS (pairS a b) c)
costW exlS         s = (just 0 , proj₁ (splitP s))
costW exrS         s = (just 0 , proj₂ (splitP s))
costW weakS        s = (just 0 , unitS)
costW runitS       s = (just 0 , pairS s unitS)
costW lunitS       s = (just 0 , pairS unitS s)
costW inlS         s = (just 0 , sumS (just s) nothing)
costW inrS         s = (just 0 , sumS nothing (just s))
costW (caseS l r)  s =
  let (ml , mr) = splitE s
  in (costMB (mapMB (costW l) ml) ⊔∞ costMB (mapMB (costW r) mr)
     , joinResC (mapMB (costW l) ml) (mapMB (costW r) mr))
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
costW distlS       s =
  let (a , bc) = splitP s
      (mb , mc) = splitE bc
  in (just 0 , sumS (wrapC a mb) (wrapC a mc))
  where
    wrapC : {X Y : Ty} → Shape X → Maybe (Shape Y) → Maybe (Shape (X ⊗ Y))
    wrapC x (just y) = just (pairS x y)
    wrapC _ nothing  = nothing
costW nilS         s = (just 0 , listS 0 topS)
costW consS        s =
  let (e , l) = splitP s
  in (just 0 , listSucC e l)
  where
    listSucC : {A : Ty} → Shape A → Shape (listT A) → Shape (listT A)
    listSucC e (listS n es) = listS (suc n) (e ⊔S es)
    listSucC e topS         = topS
costW unconsS      s = (just 0
  , sumS (just unitS) (just (pairS (elemOf s) (predListC s))))
  where
    predListC : {A : Ty} → Shape (listT A) → Shape (listT A)
    predListC (listS n es) = listS (pred n) es
    predListC topS         = topS
costW natOutS      s = (just 1 , outC s)
  where
    outC : Shape nat → Shape (unit ⊕ nat)
    outC (natLE n) = sumS (just unitS) (just (natLE (pred n)))
    outC topS      = sumS (just unitS) (just topS)
costW sucS         s = (just 0 , sucC s)
  where
    sucC : Shape nat → Shape nat
    sucC (natLE n) = natLE (suc n)
    sucC topS      = topS
costW addS         s =
  let (a , b) = splitP s in (just 0 , addC a b)
  where
    addC : Shape nat → Shape nat → Shape nat
    addC (natLE n) (natLE m) = natLE (n + m)
    addC _         _         = topS
costW (constS k)   s = (just 0 , natLE k)
costW dupNatS      s = (just 0 , pairS s s)
costW (copyS _)    s = (just 0 , pairS s s)
costW (curryS f)   s =
  (just 0 , lollyS (proj₁ (costW f (pairS s topS))))
costW applyS       s =
  (just 1 +∞ lollyCostOf (proj₁ (splitP s)) , topS)
costW mapCS        s =
  let (sbf , sl) = splitP s
  in (lenOf sl *∞ (just 1 +∞ lollyCostOf (unbang sbf)) , topS)
costW (guardS t)   s =
  (proj₁ (costW t s) , sumS (just s) (just unitS))
costW dupS         s = (just 0 , pairS s s)
costW (boxS f)     s = let (c , r) = costW f (unbang s) in (c , bangS r)
costW (boxValS f)  s = let (c , r) = costW f s in (c , bangS r)
costW mergeS       s =
  let (a , b) = splitP s in (just 0 , bangS (pairS (unbang a) (unbang b)))
costW (mapS f)     s =
  (lenOf s *∞ (just 1 +∞ proj₁ (costW f (elemOf s))) , topS)
costW (iterS f)    s =
  let (fu , a0) = splitP s
  in loopC (fuelOf fu) (unbang a0)
  where
    loopC : Maybe ℕ → Shape _ → ℕ∞ × Shape _
    loopC (just n) a0 =
      let (c , r) = aiterC (costW f) n a0
      in (c , bangS r)
    loopC nothing  a0 = (nothing , topS)
costW (foldS f)    s =
  let (ls , b0) = splitP s
  in loopC (lenOf ls) (elemOf ls) (unbang b0)
  where
    loopC : Maybe ℕ → Shape _ → Shape _ → ℕ∞ × Shape _
    loopC (just n) es a0 =
      let (c , r) = aiterC (λ x → costW f (pairS x es)) n a0
      in (c , bangS r)
    loopC nothing  _  a0 = (nothing , topS)
costW (whileS t st) s =
  let (fu , a0) = splitP s
  in loopC (fuelOf fu) (unbang a0)
  where
    stepC : Shape _ → ℕ∞ × Shape _
    stepC x =
      let (ct , _) = costW t x
          (cs , r) = costW st x
      in (ct +∞ cs , r)
    loopC : Maybe ℕ → Shape _ → ℕ∞ × Shape _
    loopC (just n) a0 =
      let (c , r) = aiterC stepC n a0
      in (c , bangS r)
    loopC nothing  a0 = (nothing , topS)

-- ── The work relation ──────────────────────────────────────────────────────

γW      : (A : Ty) → Shape A → GVal ℕ A → Set
γWMaybe : (A : Ty) → Maybe (Shape A) → GVal ℕ A → Set

γW A         topS         _        = ⊤
γW unit      unitS        _        = ⊤
γW nat       (natLE n)    m        = m ≤ n
γW (A ⊗ B)   (pairS s t)  (a , b)  = γW A s a × γW B t b
γW (A ⊕ B)   (sumS ms _)  (inj₁ a) = γWMaybe A ms a
γW (A ⊕ B)   (sumS _ mt)  (inj₂ b) = γWMaybe B mt b
γW (listT A) (listS n s)  xs       = (length xs ≤ n) × All (γW A s) xs
γW (! A)     (bangS s)    a        = γW A s a
γW (A ⊸ B)   (lollyS mc)  gf       = ∀ ga → proj₁ (gf ga) ≤∞ mc

γWMaybe A (just s) a = γW A s a
γWMaybe A nothing  _ = ⊥

unbang-γW : {A : Ty} (s : Shape (! A)) {a : GVal ℕ A}
          → γW (! A) s a → γW A (unbang s) a
unbang-γW (bangS x) h = h
unbang-γW topS      h = tt

-- shape join is sound for γW (mirrors T3.Abstract.⊔S-l/⊔S-r, plus the
-- lollyS case via ≤∞-⊔l/r).
⊔S-lW : {A : Ty} (x y : Shape A) {a : GVal ℕ A} → γW A x a → γW A (x ⊔S y) a
⊔S-rW : {A : Ty} (x y : Shape A) {a : GVal ℕ A} → γW A y a → γW A (x ⊔S y) a

⊔S-lW topS        _           _  = tt
⊔S-lW unitS       topS        _  = tt
⊔S-lW unitS       unitS       _  = tt
⊔S-lW (natLE a)   topS        _  = tt
⊔S-lW (natLE a)   (natLE b)   h  = ≤-trans h (m≤m⊔n a b)
⊔S-lW (pairS a b) topS        _  = tt
⊔S-lW (pairS a b) (pairS c d) (ha , hb) = (⊔S-lW a c ha , ⊔S-lW b d hb)
⊔S-lW (sumS l r)  topS        _  = tt
⊔S-lW (sumS (just l) r)  (sumS l′ r′) {inj₁ _} h with l′
... | just l″ = ⊔S-lW l l″ h
... | nothing = h
⊔S-lW (sumS nothing r)   (sumS l′ r′) {inj₁ _} h = ⊥-elim h
⊔S-lW (sumS l (just r))  (sumS l′ r′) {inj₂ _} h with r′
... | just r″ = ⊔S-lW r r″ h
... | nothing = h
⊔S-lW (sumS l nothing)   (sumS l′ r′) {inj₂ _} h = ⊥-elim h
⊔S-lW (listS n a) topS        _  = tt
⊔S-lW (listS n a) (listS m b) (hl , he) =
  (≤-trans hl (m≤m⊔n n m) , All.map (λ {x} → ⊔S-lW a b {x}) he)
⊔S-lW (bangS a)   topS        _  = tt
⊔S-lW (bangS a)   (bangS b)   h  = ⊔S-lW a b h
⊔S-lW (lollyS a)  topS        _  = tt
⊔S-lW (lollyS a)  (lollyS b)  h  = λ ga → ≤∞-⊔l a b (h ga)

⊔S-rW topS        y           _  = tt
⊔S-rW unitS       topS        _  = tt
⊔S-rW unitS       unitS       _  = tt
⊔S-rW (natLE a)   topS        _  = tt
⊔S-rW (natLE a)   (natLE b)   h  = ≤-trans h (m≤n⊔m a b)
⊔S-rW (pairS a b) topS        _  = tt
⊔S-rW (pairS a b) (pairS c d) (hc , hd) = (⊔S-rW a c hc , ⊔S-rW b d hd)
⊔S-rW (sumS l r)  topS        _  = tt
⊔S-rW (sumS l r)  (sumS (just l′) r′) {inj₁ _} h with l
... | just l″ = ⊔S-rW l″ l′ h
... | nothing = h
⊔S-rW (sumS l r)  (sumS nothing r′)   {inj₁ _} h = ⊥-elim h
⊔S-rW (sumS l r)  (sumS l′ (just r′)) {inj₂ _} h with r
... | just r″ = ⊔S-rW r″ r′ h
... | nothing = h
⊔S-rW (sumS l r)  (sumS l′ nothing)   {inj₂ _} h = ⊥-elim h
⊔S-rW (listS n a) topS        _  = tt
⊔S-rW (listS n a) (listS m b) (hl , he) =
  (≤-trans hl (m≤n⊔m n m) , All.map (λ {x} → ⊔S-rW a b {x}) he)
⊔S-rW (bangS a)   topS        _  = tt
⊔S-rW (bangS a)   (bangS b)   h  = ⊔S-rW a b h
⊔S-rW (lollyS a)  topS        _  = tt
⊔S-rW (lollyS a)  (lollyS b)  h  = λ ga → ≤∞-⊔r a b (h ga)

-- ── Loop bound lemmas ──────────────────────────────────────────────────────

private
  all-⊤ : {X : Set} (xs : List X) → All (λ _ → ⊤) xs
  all-⊤ []       = []
  all-⊤ (_ ∷ xs) = tt ∷ all-⊤ xs

  -- one map: every element covered ⇒ total cost ≤ n · (1 + per-element)
  map-bound : (A B : Ty) (P : GVal ℕ A → Set)
              (fG : GVal ℕ A → ℕ × GVal ℕ B) (c : ℕ∞)
            → (∀ x → P x → proj₁ (fG x) ≤∞ c)
            → ∀ n xs → length xs ≤ n → All P xs
            → proj₁ (mapGW (λ _ → 0) xs fG)
              ≤∞ (just n *∞ (just 1 +∞ c))
  map-bound A B P fG nothing  h n xs hl hall = tt
  map-bound A B P fG (just k) h n [] hl hall = z≤n
  map-bound A B P fG (just k) h (suc n) (x ∷ xs) (s≤s hl) (hx ∷ hall) =
    s≤s (+-mono-≤ (h x hx) (map-bound A B P fG (just k) h n xs hl hall))

  iter-bound : (A : Ty) (fC : Shape A → ℕ∞ × Shape A)
               (fG : GVal ℕ A → ℕ × GVal ℕ A)
             → (h : ∀ x {ga} → γW A x ga
                  → (proj₁ (fG ga) ≤∞ proj₁ (fC x))
                    × γW A (proj₂ (fC x)) (proj₂ (fG ga)))
             → ∀ n k (s : Shape A) {ga} → k ≤ n → γW A s ga
             → (proj₁ (iterGW (λ _ → 0) k fG ga) ≤∞ proj₁ (aiterC fC n s))
               × γW A (proj₂ (aiterC fC n s)) (proj₂ (iterGW (λ _ → 0) k fG ga))
  iter-bound A fC fG h zero    zero    s _ rel = (z≤n , rel)
  iter-bound A fC fG h (suc n) zero    s _ rel =
    (≤∞-zero _ , ⊔S-lW s _ rel)
  iter-bound A fC fG h (suc n) (suc k) s {ga} (s≤s kn) rel =
    let (hb , relB) = h s rel
        (ihc , ihs) = iter-bound A fC fG h n k (proj₂ (fC s))
                        {proj₂ (fG ga)} kn relB
    in (≤∞-suc _ (≤∞-+ _ _ hb ihc) , ⊔S-rW s _ ihs)

  fold-bound : (A B : Ty) (P : GVal ℕ A → Set)
               (fC : Shape B → ℕ∞ × Shape B)
               (fG : (GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
             → (h : ∀ x {gb ge} → γW B x gb → P ge
                  → (proj₁ (fG (gb , ge)) ≤∞ proj₁ (fC x))
                    × γW B (proj₂ (fC x)) (proj₂ (fG (gb , ge))))
             → ∀ n xs (s : Shape B) {gb} → length xs ≤ n → All P xs
             → γW B s gb
             → (proj₁ (foldGW (λ _ → 0) xs fG gb) ≤∞ proj₁ (aiterC fC n s))
               × γW B (proj₂ (aiterC fC n s))
                      (proj₂ (foldGW (λ _ → 0) xs fG gb))
  fold-bound A B P fC fG h zero    []       s hl hall relB = (z≤n , relB)
  fold-bound A B P fC fG h (suc n) []       s hl hall relB =
    (≤∞-zero _ , ⊔S-lW s _ relB)
  fold-bound A B P fC fG h (suc n) (x ∷ xs) s {gb} (s≤s hl) (hx ∷ hall) relB =
    let (hb , relB′) = h s relB hx
        (ihc , ihs) = fold-bound A B P fC fG h n xs (proj₂ (fC s))
                        {proj₂ (fG (gb , x))} hl hall relB′
    in (≤∞-suc _ (≤∞-+ _ _ hb ihc) , ⊔S-rW s _ ihs)

  while-bound : (A : Ty) (tC : Shape A → ℕ∞)
                (sC : Shape A → ℕ∞ × Shape A)
                (tG : GVal ℕ A → ℕ × (⊤ ⊎ ⊤))
                (sG : GVal ℕ A → ℕ × GVal ℕ A)
              → (ht : ∀ x {ga} → γW A x ga → proj₁ (tG ga) ≤∞ tC x)
              → (hs : ∀ x {ga} → γW A x ga
                    → (proj₁ (sG ga) ≤∞ proj₁ (sC x))
                      × γW A (proj₂ (sC x)) (proj₂ (sG ga)))
              → ∀ n k (s : Shape A) {ga} → k ≤ n → γW A s ga
              → (proj₁ (whileGW A k tG sG ga)
                 ≤∞ proj₁ (aiterC (λ x → (tC x +∞ proj₁ (sC x)
                                         , proj₂ (sC x))) n s))
                × γW A (proj₂ (aiterC (λ x → (tC x +∞ proj₁ (sC x)
                                             , proj₂ (sC x))) n s))
                       (proj₂ (whileGW A k tG sG ga))
  while-bound A tC sC tG sG ht hs zero    zero    s _ rel = (z≤n , rel)
  while-bound A tC sC tG sG ht hs (suc n) zero    s _ rel =
    (≤∞-zero _ , ⊔S-lW s _ rel)
  while-bound A tC sC tG sG ht hs (suc n) (suc k) s {ga} (s≤s kn) rel
    with proj₂ (tG ga)
  ... | inj₁ _ =
    ( ≤∞-wksuc _ (≤∞-padr _ _ (≤∞-padr _ _ (ht s rel)))
    , ⊔S-lW s _ rel)
  ... | inj₂ _ =
    let mt = proj₁ (tG ga)
        ms = proj₁ (sG ga)
        gb = proj₂ (sG ga)
        rC = proj₁ (whileGW A k tG sG gb)
        stepA = λ x → (tC x +∞ proj₁ (sC x) , proj₂ (sC x))
        rest = proj₁ (aiterC stepA n (proj₂ (sC s)))
        bound = just 1 +∞ ((tC s +∞ proj₁ (sC s)) +∞ rest)
        (hsc , relB) = hs s rel
        (ihc , ihs) = while-bound A tC sC tG sG ht hs n k (proj₂ (sC s))
                        {gb} kn relB
        inner : (mt + ms) + rC
              ≤∞ ((tC s +∞ proj₁ (sC s)) +∞ rest)
        inner = ≤∞-+ _ _ (≤∞-+ _ _ (ht s rel) hsc) ihc
        inner′ : mt + (ms + rC)
               ≤∞ ((tC s +∞ proj₁ (sC s)) +∞ rest)
        inner′ = subst (λ z → z ≤∞ ((tC s +∞ proj₁ (sC s)) +∞ rest))
                   (+-assoc mt ms rC) inner
        outer : suc (mt + (ms + rC)) ≤∞ bound
        outer = ≤∞-suc _ inner′
    in ( subst (λ z → z ≤∞ bound) (sym (+-suc mt (ms + rC))) outer
       , ⊔S-rW s _ ihs)

-- ── THE THEOREM: static work bound ─────────────────────────────────────────

costW-sound : {A B : Ty} (f : A ⇨ B) (s : Shape A) {ga : GVal ℕ A}
            → γW A s ga
            → (proj₁ (⟦ f ⟧C ga) ≤∞ proj₁ (costW f s))
              × γW B (proj₂ (costW f s)) (proj₂ (⟦ f ⟧C ga))
costW-sound idS s h = (≤∞-zero _ , h)
costW-sound (g ∘S f) s h =
  let (cf , rf) = costW-sound f s h
      (cg , rg) = costW-sound g (proj₂ (costW f s)) rf
  in (≤∞-+ _ _ cf cg , rg)
costW-sound (f ⊗S g) topS {a , c} h =
  let (cf , rf) = costW-sound f topS {a} tt
      (cg , rg) = costW-sound g topS {c} tt
  in (≤∞-+ _ _ cf cg , (rf , rg))
costW-sound (f ⊗S g) (pairS sa sc) {a , c} (ha , hc) =
  let (cf , rf) = costW-sound f sa ha
      (cg , rg) = costW-sound g sc hc
  in (≤∞-+ _ _ cf cg , (rf , rg))
costW-sound swapS topS h = (≤∞-zero _ , (tt , tt))
costW-sound swapS (pairS a b) (ha , hb) = (≤∞-zero _ , (hb , ha))
costW-sound assocS topS h = (≤∞-zero _ , (tt , (tt , tt)))
costW-sound assocS (pairS topS c) {(_ , _) , _} (_ , hc) =
  (≤∞-zero _ , (tt , (tt , hc)))
costW-sound assocS (pairS (pairS a b) c) ((ha , hb) , hc) =
  (≤∞-zero _ , (ha , (hb , hc)))
costW-sound unassocS topS h = (≤∞-zero _ , ((tt , tt) , tt))
costW-sound unassocS (pairS a topS) {_ , (_ , _)} (ha , _) =
  (≤∞-zero _ , ((ha , tt) , tt))
costW-sound unassocS (pairS a (pairS b c)) (ha , (hb , hc)) =
  (≤∞-zero _ , ((ha , hb) , hc))
costW-sound exlS topS h = (≤∞-zero _ , tt)
costW-sound exlS (pairS a b) (ha , _) = (≤∞-zero _ , ha)
costW-sound exrS topS h = (≤∞-zero _ , tt)
costW-sound exrS (pairS a b) (_ , hb) = (≤∞-zero _ , hb)
costW-sound weakS s h = (≤∞-zero _ , tt)
costW-sound runitS s h = (≤∞-zero _ , (h , tt))
costW-sound lunitS s h = (≤∞-zero _ , (tt , h))
costW-sound inlS s h = (≤∞-zero _ , h)
costW-sound inrS s h = (≤∞-zero _ , h)
costW-sound (caseS l r) topS {inj₁ a} h =
  let (cl , rl) = costW-sound l topS {a} tt
  in (≤∞-⊔l _ _ cl , ⊔S-lW (proj₂ (costW l topS)) (proj₂ (costW r topS)) rl)
costW-sound (caseS l r) topS {inj₂ b} h =
  let (cr , rr) = costW-sound r topS {b} tt
  in (≤∞-⊔r _ _ cr , ⊔S-rW (proj₂ (costW l topS)) (proj₂ (costW r topS)) rr)
costW-sound (caseS l r) (sumS (just sl) mr) {inj₁ a} h with mr
... | just sr =
  let (cl , rl) = costW-sound l sl h
  in (≤∞-⊔l _ _ cl , ⊔S-lW (proj₂ (costW l sl)) (proj₂ (costW r sr)) rl)
... | nothing =
  let (cl , rl) = costW-sound l sl h
  in (≤∞-⊔l _ _ cl , rl)
costW-sound (caseS l r) (sumS nothing mr) {inj₁ a} h = ⊥-elim h
costW-sound (caseS l r) (sumS ml (just sr)) {inj₂ b} h with ml
... | just sl =
  let (cr , rr) = costW-sound r sr h
  in (≤∞-⊔r _ _ cr , ⊔S-rW (proj₂ (costW l sl)) (proj₂ (costW r sr)) rr)
... | nothing =
  let (cr , rr) = costW-sound r sr h
  in (≤∞-⊔r _ _ cr , rr)
costW-sound (caseS l r) (sumS ml nothing) {inj₂ b} h = ⊥-elim h
costW-sound distlS topS {a , inj₁ b} h = (≤∞-zero _ , (tt , tt))
costW-sound distlS topS {a , inj₂ c} h = (≤∞-zero _ , (tt , tt))
costW-sound distlS (pairS sa topS) {a , inj₁ b} (ha , _) =
  (≤∞-zero _ , (ha , tt))
costW-sound distlS (pairS sa topS) {a , inj₂ c} (ha , _) =
  (≤∞-zero _ , (ha , tt))
costW-sound distlS (pairS sa (sumS (just sb) mc)) {a , inj₁ b} (ha , hb) =
  (≤∞-zero _ , (ha , hb))
costW-sound distlS (pairS sa (sumS nothing mc)) {a , inj₁ b} (ha , hb) =
  ⊥-elim hb
costW-sound distlS (pairS sa (sumS mb (just sc))) {a , inj₂ c} (ha , hc) =
  (≤∞-zero _ , (ha , hc))
costW-sound distlS (pairS sa (sumS mb nothing)) {a , inj₂ c} (ha , hc) =
  ⊥-elim hc
costW-sound nilS s h = (≤∞-zero _ , (z≤n , []))
costW-sound consS topS {x , xs} h = (≤∞-zero _ , tt)
costW-sound consS (pairS se topS) {x , xs} _ = (≤∞-zero _ , tt)
costW-sound consS (pairS se (listS n ses)) {x , xs} (he , (hl , hes)) =
  (≤∞-zero _
  , (s≤s hl , ⊔S-lW se ses he ∷ All.map (λ {y} → ⊔S-rW se ses {y}) hes))
costW-sound unconsS s {[]} h = (≤∞-zero _ , tt)
costW-sound unconsS topS {x ∷ xs} h = (≤∞-zero _ , (tt , tt))
costW-sound unconsS (listS n se) {x ∷ xs} (hl , hx ∷ hxs) =
  (≤∞-zero _ , (hx , (pred-len n hl , hxs)))
  where
    pred-len : ∀ {m} n → suc m ≤ n → m ≤ pred n
    pred-len (suc k) (s≤s p) = p
costW-sound natOutS topS {zero} h = (≤-refl , tt)
costW-sound natOutS topS {suc m} h = (≤-refl , tt)
costW-sound natOutS (natLE n) {zero} h = (≤-refl , tt)
costW-sound natOutS (natLE n) {suc m} h = (≤-refl , pred-le h)
  where
    pred-le : ∀ {m n} → suc m ≤ n → m ≤ pred n
    pred-le (s≤s p) = p
costW-sound sucS topS h = (≤∞-zero _ , tt)
costW-sound sucS (natLE n) h = (≤∞-zero _ , s≤s h)
costW-sound addS topS h = (≤∞-zero _ , tt)
costW-sound addS (pairS topS _) h = (≤∞-zero _ , tt)
costW-sound addS (pairS (natLE n) topS) h = (≤∞-zero _ , tt)
costW-sound addS (pairS (natLE n) (natLE m)) (ha , hb) =
  (≤∞-zero _ , +-mono-≤ ha hb)
costW-sound (constS k) s h = (≤∞-zero _ , ≤-refl)
costW-sound dupNatS s h = (≤∞-zero _ , (h , h))
costW-sound (copyS _) s h = (≤∞-zero _ , (h , h))
costW-sound (curryS f) s h =
  ( ≤∞-zero _
  , λ ga → proj₁ (costW-sound f (pairS s topS) {_ , ga} (h , tt)))
costW-sound applyS topS {gf , ga} h = (tt , tt)
costW-sound applyS (pairS topS sa) {gf , ga} h = (tt , tt)
costW-sound applyS (pairS (lollyS mc) sa) {gf , ga} (relF , _) =
  (≤∞-suc mc (relF ga) , tt)
costW-sound mapCS topS h = (tt , tt)
costW-sound mapCS (pairS sbf topS) h = (tt , tt)
costW-sound mapCS (pairS topS (listS n es)) h = (tt , tt)
costW-sound mapCS (pairS (bangS topS) (listS n es)) h = (tt , tt)
costW-sound mapCS (pairS (bangS (lollyS nothing)) (listS n es)) h = (tt , tt)
costW-sound (mapCS {A} {B}) (pairS (bangS (lollyS (just k))) (listS n es))
  {gf , gxs} (relF , (hlen , _)) =
  ( map-bound A B (λ _ → ⊤) gf (just k) (λ x _ → relF x) n gxs hlen
      (all-⊤ gxs)
  , tt)
costW-sound (guardS t) s {ga} h
  with proj₂ (⟦ t ⟧C ga) | costW-sound t s {ga} h
... | inj₁ _ | (ct , _) = (ct , h)
... | inj₂ _ | (ct , _) = (ct , tt)
costW-sound dupS s h = (≤∞-zero _ , (h , h))
costW-sound (boxS f) topS h =
  let (c , r) = costW-sound f topS tt in (c , r)
costW-sound (boxS f) (bangS s) h =
  let (c , r) = costW-sound f s h in (c , r)
costW-sound (boxValS f) s h =
  let (c , r) = costW-sound f s h in (c , r)
costW-sound mergeS topS {a , b} h = (≤∞-zero _ , (tt , tt))
costW-sound mergeS (pairS topS sb) {a , b} (_ , hb) =
  (≤∞-zero _ , (tt , unbang-γW sb hb))
costW-sound mergeS (pairS (bangS sa) sb) {a , b} (ha , hb) =
  (≤∞-zero _ , (ha , unbang-γW sb hb))
costW-sound (mapS f) topS h = (tt , tt)
costW-sound (mapS {A} {B} f) (listS n es) {gxs} (hlen , hall) =
  ( map-bound A B (γW A es) ⟦ f ⟧C (proj₁ (costW f es))
      (λ x hx → proj₁ (costW-sound f es {x} hx)) n gxs hlen hall
  , tt)
costW-sound (iterS f) topS {gn , ga} h = (tt , tt)
costW-sound (iterS f) (pairS topS a0) {gn , ga} h = (tt , tt)
costW-sound (iterS {A} f) (pairS (natLE N) a0) {gn , ga} (hn , ha) =
  let (c , r) = iter-bound A (costW f) ⟦ f ⟧C
                  (λ x {gx} rel → costW-sound f x {gx} rel)
                  N gn (unbang a0) {ga} hn (unbang-γW a0 ha)
  in (c , r)
costW-sound (foldS f) topS {gxs , gb} h = (tt , tt)
costW-sound (foldS f) (pairS topS b0) {gxs , gb} h = (tt , tt)
costW-sound (foldS {A} {B} f) (pairS (listS N es) b0) {gxs , gb}
  ((hlen , hxs) , hb) =
  let (c , r) = fold-bound A B (γW A es) (λ x → costW f (pairS x es)) ⟦ f ⟧C
                  (λ x {gb′} {ge} relB he →
                    costW-sound f (pairS x es) {gb′ , ge} (relB , he))
                  N gxs (unbang b0) {gb} hlen hxs (unbang-γW b0 hb)
  in (c , r)
costW-sound (whileS t st) topS {gn , ga} h = (tt , tt)
costW-sound (whileS t st) (pairS topS a0) {gn , ga} h = (tt , tt)
costW-sound (whileS {A} t st) (pairS (natLE N) a0) {gn , ga} (hn , ha) =
  let (c , r) = while-bound A (λ x → proj₁ (costW t x)) (costW st)
                  ⟦ t ⟧C ⟦ st ⟧C
                  (λ x {gx} rel → proj₁ (costW-sound t x {gx} rel))
                  (λ x {gx} rel → costW-sound st x {gx} rel)
                  N gn (unbang a0) {ga} hn (unbang-γW a0 ha)
  in (c , r)

-- ── Entry-point corollaries ────────────────────────────────────────────────

-- The all-top shape of a type: what the CLI can assume about an
-- arbitrary input.  Covers EVERY graded value.
shapeOfTy : (A : Ty) → Shape A
shapeOfTy unit      = unitS
shapeOfTy nat       = topS
shapeOfTy (A ⊗ B)   = pairS (shapeOfTy A) (shapeOfTy B)
shapeOfTy (A ⊕ B)   = sumS (just (shapeOfTy A)) (just (shapeOfTy B))
shapeOfTy (listT A) = topS
shapeOfTy (! A)     = bangS (shapeOfTy A)
shapeOfTy (A ⊸ B)   = topS

γW-shapeOfTy : (A : Ty) (ga : GVal ℕ A) → γW A (shapeOfTy A) ga
γW-shapeOfTy unit      _        = tt
γW-shapeOfTy nat       _        = tt
γW-shapeOfTy (A ⊗ B)   (a , b)  = (γW-shapeOfTy A a , γW-shapeOfTy B b)
γW-shapeOfTy (A ⊕ B)   (inj₁ a) = γW-shapeOfTy A a
γW-shapeOfTy (A ⊕ B)   (inj₂ b) = γW-shapeOfTy B b
γW-shapeOfTy (listT A) _        = tt
γW-shapeOfTy (! A)     a        = γW-shapeOfTy A a
γW-shapeOfTy (A ⊸ B)   _        = tt

-- Certified static work bound at a covered input shape.
work-bounded-at : {A B : Ty} (f : A ⇨ B) (s : Shape A) {ga : GVal ℕ A}
                → γW A s ga → work f ga ≤∞ proj₁ (costW f s)
work-bounded-at f s h = proj₁ (costW-sound f s h)

-- Certified static work bound for ARBITRARY input: what --certificate
-- reports.  With T3.Adequacy this is a machine fuel bound.
work-bounded : {A B : Ty} (f : A ⇨ B) (ga : GVal ℕ A)
             → work f ga ≤∞ proj₁ (costW f (shapeOfTy A))
work-bounded {A} f ga = work-bounded-at f (shapeOfTy A) (γW-shapeOfTy A ga)
