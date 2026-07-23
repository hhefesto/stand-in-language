------------------------------------------------------------------------
-- T3.Bound — certified static work and duplication bounds (milestone R3).
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
-- Work charges counts.  Duplication mirrors dupAlg: explicit copies and
-- probes charge a type-sensitive static upper bound on value word size.
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
-- costW and costD compute their own output shapes (T3.Abstract.transfer
-- stays untouched); only their logical-relation soundness matters here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Bound where

open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Nat             using (ℕ; zero; suc; pred; _+_; _*_;
                                        _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; +-mono-≤;
                                        m≤m⊔n; m≤n⊔m; m≤m+n; +-assoc;
                                        +-suc; n≤1+n; *-mono-≤)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Unit            using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong; subst)

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

*-zero-right : (n : ℕ) → n * 0 ≡ 0
*-zero-right zero    = refl
*-zero-right (suc n) rewrite *-zero-right n = refl

zero-times : (n : ℕ) → 0 * n ≡ 0
zero-times zero    = refl
zero-times (suc n) rewrite zero-times n = refl

-- Multiplication used by duplication bounds.  Unlike the historical
-- operation above (kept unchanged for costW), an unknown factor times a
-- statically zero charge is zero.
infixl 7 _*D∞_
_*D∞_ : ℕ∞ → ℕ∞ → ℕ∞
_            *D∞ just 0       = just 0
just 0       *D∞ just (suc b) = just 0
just (suc a) *D∞ just (suc b) = just (suc a * suc b)
nothing      *D∞ just (suc b) = nothing
just 0       *D∞ nothing      = just 0
just (suc a) *D∞ nothing      = nothing
nothing      *D∞ nothing      = nothing

≤∞-*D : {a b : ℕ} (x y : ℕ∞) → a ≤∞ x → b ≤∞ y → (a * b) ≤∞ (x *D∞ y)
≤∞-*D nothing  nothing  ha hb = tt
≤∞-*D {a = zero}  (just 0) nothing ha hb = z≤n
≤∞-*D {a = suc a} (just 0) nothing () hb
≤∞-*D (just (suc x)) nothing ha hb = tt
≤∞-*D {a = a} {b = zero} nothing (just 0) ha hb
  rewrite *-zero-right a = z≤n
≤∞-*D {b = suc b} nothing (just 0) ha ()
≤∞-*D nothing  (just (suc b)) ha hb = tt
≤∞-*D {a = zero} {b = zero} (just 0) (just 0) ha hb = z≤n
≤∞-*D {a = suc a} (just 0) (just 0) () hb
≤∞-*D {a = zero} {b = b} (just 0) (just (suc y)) ha hb
  rewrite zero-times b = z≤n
≤∞-*D {a = suc a} (just 0) (just (suc y)) () hb
≤∞-*D {a = a} {b = zero} (just (suc x)) (just 0) ha hb
  rewrite *-zero-right a = z≤n
≤∞-*D {b = suc b} (just (suc a)) (just 0) ha ()
≤∞-*D (just (suc a)) (just (suc b)) ha hb =
  *-mono-≤ ha hb

-- ── Static word size ────────────────────────────────────────────────────────

mutual
  listSizeS : {A : Ty} → ℕ → Shape A → ℕ∞
  listSizeS zero    s = just 1
  listSizeS (suc n) s = just 1 +∞ (sizeS s +∞ listSizeS n s)

  sizeMaybeS : {A : Ty} → Maybe (Shape A) → ℕ∞
  sizeMaybeS nothing  = just 0
  sizeMaybeS (just s) = sizeS s

  sizeS : {A : Ty} → Shape A → ℕ∞
  sizeS {unit}      topS         = just 1
  sizeS {nat}       topS         = just 1
  sizeS {A ⊗ B}     topS         = nothing
  sizeS {A ⊕ B}     topS         = nothing
  sizeS {listT A}   topS         = nothing
  sizeS {(! A)}     topS         = nothing
  sizeS {A ⊸ B}     topS         = just 1
  sizeS             unitS       = just 1
  sizeS             (natLE _)    = just 1
  sizeS             (pairS a b)  = sizeS a +∞ sizeS b
  sizeS             (sumS a b)   = just 1 +∞ (sizeMaybeS a ⊔∞ sizeMaybeS b)
  sizeS             (listS n a)  = listSizeS n a
  sizeS             (bangS a)    = sizeS a
  sizeS             (lollyS _)   = just 1

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
costW iterCS       s =
  let (sbf , rest) = splitP s
      (fu , _) = splitP rest
  in (fuelOf fu *∞ (just 1 +∞ lollyCostOf (unbang sbf)) , topS)
costW foldCS       s =
  let (sbf , rest) = splitP s
      (ls , _) = splitP rest
  in (lenOf ls *∞ (just 1 +∞ lollyCostOf (unbang sbf)) , topS)
costW whileCS      s =
  let (st , rest) = splitP s
      (sf , q) = splitP rest
      (fu , _) = splitP q
  in (fuelOf fu *∞ (just 1 +∞ (lollyCostOf (unbang st) +∞ lollyCostOf (unbang sf)))
     , topS)
costW (guardS t)   s =
  (proj₁ (costW t s) , sumS (just s) (just unitS))
costW (promoteS _) s = (just 0 , bangS s)
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
-- v1: the recur closure's own cost is the recursion itself — unknown to
-- this static pass — so bounded recursion reports unbounded work.  The
-- finite fuel-times-round bound waits for RT3's sizing (concrete fuel).
costW (recS t r l) s = (nothing , topS)

-- Duplication mirrors dupAlg exactly: only dupNatS, copyS, dupS and
-- guard/while probes charge; closure bodies contribute when applied.
aiterD : {A : Ty} → (Shape A → ℕ∞ × Shape A) → ℕ → Shape A → ℕ∞ × Shape A
aiterD f zero    s = (just 0 , s)
aiterD f (suc n) s =
  let (c₁ , s₁) = f s
      (cₙ , sₙ) = aiterD f n s₁
  in (c₁ +∞ cₙ , s ⊔S sₙ)

costD : {A B : Ty} (f : A ⇨ B) → Shape A → ℕ∞ × Shape B
costD idS          s = (just 0 , s)
costD (g ∘S f)     s =
  let (cf , sf) = costD f s ; (cg , sg) = costD g sf
  in (cf +∞ cg , sg)
costD (f ⊗S g)     s =
  let (sa , sc) = splitP s
      (cf , sb) = costD f sa
      (cg , sd) = costD g sc
  in (cf +∞ cg , pairS sb sd)
costD swapS        s = let (a , b) = splitP s in (just 0 , pairS b a)
costD assocS       s =
  let (ab , c) = splitP s ; (a , b) = splitP ab
  in (just 0 , pairS a (pairS b c))
costD unassocS     s =
  let (a , bc) = splitP s ; (b , c) = splitP bc
  in (just 0 , pairS (pairS a b) c)
costD exlS         s = (just 0 , proj₁ (splitP s))
costD exrS         s = (just 0 , proj₂ (splitP s))
costD weakS        s = (just 0 , unitS)
costD runitS       s = (just 0 , pairS s unitS)
costD lunitS       s = (just 0 , pairS unitS s)
costD inlS         s = (just 0 , sumS (just s) nothing)
costD inrS         s = (just 0 , sumS nothing (just s))
costD (caseS l r)  s =
  let (ml , mr) = splitE s
  in (costMB (mapMB (costD l) ml) ⊔∞ costMB (mapMB (costD r) mr)
     , joinRes (mapMB (costD l) ml) (mapMB (costD r) mr))
  where
    mapMB : {A B : Ty} → (Shape A → ℕ∞ × Shape B)
          → Maybe (Shape A) → Maybe (ℕ∞ × Shape B)
    mapMB f (just x) = just (f x)
    mapMB f nothing  = nothing
    costMB : {B : Ty} → Maybe (ℕ∞ × Shape B) → ℕ∞
    costMB (just (c , _)) = c
    costMB nothing        = just 0
    joinRes : {B : Ty} → Maybe (ℕ∞ × Shape B) → Maybe (ℕ∞ × Shape B) → Shape B
    joinRes (just (_ , x)) (just (_ , y)) = x ⊔S y
    joinRes (just (_ , x)) nothing        = x
    joinRes nothing        (just (_ , y)) = y
    joinRes nothing        nothing        = topS
costD distlS       s =
  let (a , bc) = splitP s ; (mb , mc) = splitE bc
  in (just 0 , sumS (wrap a mb) (wrap a mc))
  where
    wrap : {A B : Ty} → Shape A → Maybe (Shape B) → Maybe (Shape (A ⊗ B))
    wrap a (just b) = just (pairS a b)
    wrap a nothing  = nothing
costD nilS         s = (just 0 , listS 0 topS)
costD consS        s =
  let (e , l) = splitP s in (just 0 , consC e l)
  where
    consC : {A : Ty} → Shape A → Shape (listT A) → Shape (listT A)
    consC e (listS n es) = listS (suc n) (e ⊔S es)
    consC e topS         = topS
costD unconsS      s = (just 0 , sumS (just unitS) (just (pairS (elemOf s) (predC s))))
  where
    predC : {A : Ty} → Shape (listT A) → Shape (listT A)
    predC (listS n es) = listS (pred n) es
    predC topS         = topS
costD natOutS      s = (just 0 , outC s)
  where
    outC : Shape nat → Shape (unit ⊕ nat)
    outC (natLE n) = sumS (just unitS) (just (natLE (pred n)))
    outC topS      = sumS (just unitS) (just topS)
costD sucS         s = (just 0 , sucC s)
  where
    sucC : Shape nat → Shape nat
    sucC (natLE n) = natLE (suc n)
    sucC topS      = topS
costD addS         s =
  let (a , b) = splitP s in (just 0 , addC a b)
  where
    addC : Shape nat → Shape nat → Shape nat
    addC (natLE n) (natLE m) = natLE (n + m)
    addC _ _ = topS
costD (constS k)   s = (just 0 , natLE k)
costD dupNatS      s = (just 1 , pairS s s)
costD (copyS _)    s = (sizeS s , pairS s s)
costD (guardS t)   s = (sizeS s +∞ proj₁ (costD t s) , sumS (just s) (just unitS))
costD (curryS f)   s = (just 0 , lollyS (proj₁ (costD f (pairS s topS))))
costD applyS       s = (lollyCostOf (proj₁ (splitP s)) , topS)
costD mapCS        s =
  let (sbf , sl) = splitP s
  in (lenOf sl *D∞ lollyCostOf (unbang sbf) , topS)
costD iterCS       s =
  let (sbf , rest) = splitP s
      (fu , _) = splitP rest
  in (fuelOf fu *D∞ lollyCostOf (unbang sbf) , topS)
costD foldCS       s =
  let (sbf , rest) = splitP s
      (ls , _) = splitP rest
  in (lenOf ls *D∞ lollyCostOf (unbang sbf) , topS)
costD whileCS      s =
  let (_ , rest) = splitP s
      (_ , q) = splitP rest
      (fu , _) = splitP q
  in (fuelOf fu *D∞ nothing , topS)
costD (promoteS _) s = (just 0 , bangS s)
costD dupS         s = (sizeS s , pairS s s)
costD (boxS f)     s = let (c , r) = costD f (unbang s) in (c , bangS r)
costD (boxValS f)  s = let (c , r) = costD f s in (c , bangS r)
costD mergeS       s =
  let (a , b) = splitP s in (just 0 , bangS (pairS (unbang a) (unbang b)))
costD (mapS f)     s =
  (lenOf s *D∞ proj₁ (costD f (elemOf s)) , topS)
costD (iterS f)    s =
  let (fu , a0) = splitP s in loop (fuelOf fu) (unbang a0)
  where
    loop : Maybe ℕ → Shape _ → ℕ∞ × Shape _
    loop (just n) a0 = let (c , r) = aiterD (costD f) n a0 in (c , bangS r)
    loop nothing  a0 = (nothing , topS)
costD (foldS f)    s =
  let (ls , b0) = splitP s in loop (lenOf ls) (elemOf ls) (unbang b0)
  where
    loop : Maybe ℕ → Shape _ → Shape _ → ℕ∞ × Shape _
    loop (just n) es b0 =
      let (c , r) = aiterD (λ x → costD f (pairS x es)) n b0
      in (c , bangS r)
    loop nothing es b0 = (nothing , topS)
costD (whileS t st) s =
  let (fu , a0) = splitP s in loop (fuelOf fu) (unbang a0)
  where
    round : Shape _ → ℕ∞ × Shape _
    round x =
      let (ct , _) = costD t x ; (cs , r) = costD st x
      in (sizeS x +∞ (ct +∞ cs) , r)
    loop : Maybe ℕ → Shape _ → ℕ∞ × Shape _
    loop (just n) a0 = let (c , r) = aiterD round n a0 in (c , bangS r)
    loop nothing  a0 = (nothing , topS)
costD (recS t r l) s = (nothing , topS)

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

mutual
  sizeMaybeS-sound : {A : Ty} (s : Maybe (Shape A)) {a : GVal ℕ A}
                   → γWMaybe A s a → sizeG ℕ A a ≤∞ sizeMaybeS s
  sizeMaybeS-sound nothing  ()
  sizeMaybeS-sound (just s) h = sizeS-sound s h

  list-size-bound : (A : Ty) (s : Shape A) (n : ℕ) (xs : List (GVal ℕ A))
                  → length xs ≤ n → All (γW A s) xs
                  → sizeG ℕ (listT A) xs ≤∞ listSizeS n s
  list-size-bound A s zero [] hl [] = s≤s z≤n
  list-size-bound A s (suc n) [] hl [] = ≤∞-suc _ (≤∞-zero _)
  list-size-bound A s (suc n) (x ∷ xs) (s≤s hl) (hx ∷ hxs) =
    ≤∞-suc _ (≤∞-+ _ _ (sizeS-sound s hx) (list-size-bound A s n xs hl hxs))

  sizeS-sound : {A : Ty} (s : Shape A) {a : GVal ℕ A}
              → γW A s a → sizeG ℕ A a ≤∞ sizeS s
  sizeS-sound {unit}    topS h = s≤s z≤n
  sizeS-sound {nat}     topS h = s≤s z≤n
  sizeS-sound {_ ⊗ _}   topS h = tt
  sizeS-sound {_ ⊕ _}   topS h = tt
  sizeS-sound {listT _} topS h = tt
  sizeS-sound {(! _)}   topS h = tt
  sizeS-sound {_ ⊸ _}   topS h = s≤s z≤n
  sizeS-sound unitS h = s≤s z≤n
  sizeS-sound (natLE n) h = s≤s z≤n
  sizeS-sound (pairS a b) (ha , hb) =
    ≤∞-+ _ _ (sizeS-sound a ha) (sizeS-sound b hb)
  sizeS-sound (sumS (just a) b) {inj₁ x} h =
    ≤∞-suc _ (≤∞-⊔l _ _ (sizeS-sound a h))
  sizeS-sound (sumS nothing b) {inj₁ x} ()
  sizeS-sound (sumS a (just b)) {inj₂ x} h =
    ≤∞-suc _ (≤∞-⊔r _ _ (sizeS-sound b h))
  sizeS-sound (sumS a nothing) {inj₂ x} ()
  sizeS-sound (listS n s) {xs} (hl , hs) = list-size-bound _ s n xs hl hs
  sizeS-sound (bangS s) h = sizeS-sound s h
  sizeS-sound (lollyS c) h = s≤s z≤n

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
  module Dup = Interp dupAlg

  mulD-finite : (n k : ℕ) → just n *D∞ just k ≡ just (n * k)
  mulD-finite zero zero = refl
  mulD-finite zero (suc k) = refl
  mulD-finite (suc n) zero rewrite *-zero-right (suc n) = refl
  mulD-finite (suc n) (suc k) = refl

  mapD-finite : (A B : Ty) (P : GVal ℕ A → Set)
                (fG : GVal ℕ A → ℕ × GVal ℕ B) (k : ℕ)
              → (∀ x → P x → proj₁ (fG x) ≤ k)
              → ∀ n xs → length xs ≤ n → All P xs
              → proj₁ (Dup.mapG (λ _ → 0) xs fG) ≤ n * k
  mapD-finite A B P fG k h zero [] hl [] = z≤n
  mapD-finite A B P fG k h (suc n) [] hl [] = z≤n
  mapD-finite A B P fG k h (suc n) (x ∷ xs) (s≤s hl) (hx ∷ hall) =
    +-mono-≤ (h x hx) (mapD-finite A B P fG k h n xs hl hall)

  mapD-bound : (A B : Ty) (P : GVal ℕ A → Set)
               (fG : GVal ℕ A → ℕ × GVal ℕ B) (c : ℕ∞)
             → (∀ x → P x → proj₁ (fG x) ≤∞ c)
             → ∀ n xs → length xs ≤ n → All P xs
             → proj₁ (Dup.mapG (λ _ → 0) xs fG) ≤∞ (just n *D∞ c)
  mapD-bound A B P fG nothing h zero [] hl hall = z≤n
  mapD-bound A B P fG nothing h (suc n) [] hl hall = tt
  mapD-bound A B P fG nothing h (suc n) (x ∷ xs) hl hall = tt
  mapD-bound A B P fG (just k) h n xs hl hall =
    subst (λ z → proj₁ (Dup.mapG (λ _ → 0) xs fG) ≤∞ z)
      (sym (mulD-finite n k)) (mapD-finite A B P fG k h n xs hl hall)

  iterD-bound : (A : Ty) (fC : Shape A → ℕ∞ × Shape A)
                (fG : GVal ℕ A → ℕ × GVal ℕ A)
              → (h : ∀ x {ga} → γW A x ga
                   → (proj₁ (fG ga) ≤∞ proj₁ (fC x))
                     × γW A (proj₂ (fC x)) (proj₂ (fG ga)))
              → ∀ n k (s : Shape A) {ga} → k ≤ n → γW A s ga
              → (proj₁ (Dup.iterG (λ _ → 0) k fG ga) ≤∞ proj₁ (aiterD fC n s))
                × γW A (proj₂ (aiterD fC n s))
                       (proj₂ (Dup.iterG (λ _ → 0) k fG ga))
  iterD-bound A fC fG h zero zero s kn rel = (z≤n , rel)
  iterD-bound A fC fG h (suc n) zero s kn rel =
    (≤∞-zero _ , ⊔S-lW s _ rel)
  iterD-bound A fC fG h (suc n) (suc k) s {ga} (s≤s kn) rel =
    let (hc , hr) = h s rel
        (ic , ir) = iterD-bound A fC fG h n k (proj₂ (fC s))
                     {proj₂ (fG ga)} kn hr
    in (≤∞-+ _ _ hc ic , ⊔S-rW s _ ir)

  foldD-bound : (A B : Ty) (P : GVal ℕ A → Set)
                (fC : Shape B → ℕ∞ × Shape B)
                (fG : (GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
              → (h : ∀ x {gb ge} → γW B x gb → P ge
                   → (proj₁ (fG (gb , ge)) ≤∞ proj₁ (fC x))
                     × γW B (proj₂ (fC x)) (proj₂ (fG (gb , ge))))
              → ∀ n xs (s : Shape B) {gb} → length xs ≤ n → All P xs
              → γW B s gb
              → (proj₁ (Dup.foldG (λ _ → 0) xs fG gb) ≤∞ proj₁ (aiterD fC n s))
                × γW B (proj₂ (aiterD fC n s))
                       (proj₂ (Dup.foldG (λ _ → 0) xs fG gb))
  foldD-bound A B P fC fG h zero [] s hl hall rel = (z≤n , rel)
  foldD-bound A B P fC fG h (suc n) [] s hl hall rel =
    (≤∞-zero _ , ⊔S-lW s _ rel)
  foldD-bound A B P fC fG h (suc n) (x ∷ xs) s {gb}
    (s≤s hl) (hx ∷ hall) rel =
    let (hc , hr) = h s rel hx
        (ic , ir) = foldD-bound A B P fC fG h n xs (proj₂ (fC s))
                     {proj₂ (fG (gb , x))} hl hall hr
    in (≤∞-+ _ _ hc ic , ⊔S-rW s _ ir)

  whileD-bound : (A : Ty) (tC : Shape A → ℕ∞)
                 (sC : Shape A → ℕ∞ × Shape A)
                 (tG : GVal ℕ A → ℕ × (⊤ ⊎ ⊤))
                 (sG : GVal ℕ A → ℕ × GVal ℕ A)
               → (ht : ∀ x {ga} → γW A x ga → proj₁ (tG ga) ≤∞ tC x)
               → (hs : ∀ x {ga} → γW A x ga
                    → (proj₁ (sG ga) ≤∞ proj₁ (sC x))
                      × γW A (proj₂ (sC x)) (proj₂ (sG ga)))
               → ∀ n k (s : Shape A) {ga} → k ≤ n → γW A s ga
               → (proj₁ (Dup.whileG A k tG sG ga)
                  ≤∞ proj₁ (aiterD
                    (λ x → (sizeS x +∞ (tC x +∞ proj₁ (sC x)) , proj₂ (sC x))) n s))
                 × γW A (proj₂ (aiterD
                    (λ x → (sizeS x +∞ (tC x +∞ proj₁ (sC x)) , proj₂ (sC x))) n s))
                       (proj₂ (Dup.whileG A k tG sG ga))
  whileD-bound A tC sC tG sG ht hs zero zero s kn rel = (z≤n , rel)
  whileD-bound A tC sC tG sG ht hs (suc n) zero s kn rel =
    (≤∞-zero _ , ⊔S-lW s _ rel)
  whileD-bound A tC sC tG sG ht hs (suc n) (suc k) s {ga} (s≤s kn) rel
    with proj₂ (tG ga)
  ... | inj₁ _ =
    ( ≤∞-padr _ _ (≤∞-+ _ _ (sizeS-sound s rel)
        (≤∞-padr _ _ (ht s rel)))
    , ⊔S-lW s _ rel)
  ... | inj₂ _ =
    let sz = sizeG ℕ A ga
        mt = proj₁ (tG ga)
        ms = proj₁ (sG ga)
        rr = proj₁ (Dup.whileG A k tG sG (proj₂ (sG ga)))
        (hsc , relB) = hs s rel
        (ihc , ihs) = whileD-bound A tC sC tG sG ht hs n k (proj₂ (sC s))
                       {proj₂ (sG ga)} kn relB
        grouped = ≤∞-+ _ _
          (≤∞-+ _ _ (sizeS-sound s rel) (≤∞-+ _ _ (ht s rel) hsc)) ihc
        regroup : (sz + (mt + ms)) + rr ≡ sz + (mt + (ms + rr))
        regroup = trans (+-assoc sz (mt + ms) rr)
                    (cong (sz +_) (+-assoc mt ms rr))
    in (subst (λ z → z ≤∞ proj₁ (aiterD
          (λ x → (sizeS x +∞ (tC x +∞ proj₁ (sC x)) , proj₂ (sC x)))
          (suc n) s)) regroup grouped
       , ⊔S-rW s _ ihs)

  len0-fold : (A B : Ty) (fG : (GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
            → ∀ xs (b : GVal ℕ B) → length xs ≤ 0
            → proj₁ (Dup.foldG (λ _ → 0) xs fG b) ≤ 0
  len0-fold A B fG [] b z≤n = z≤n
  len0-fold A B fG (x ∷ xs) b ()

  all-⊤ : {X : Set} (xs : List X) → All (λ _ → ⊤) xs
  all-⊤ []       = []
  all-⊤ (_ ∷ xs) = tt ∷ all-⊤ xs

  -- closure-bodied loops (M5): the boxed body's Kripke bound is uniform
  -- over every argument, so no shape evolution is needed — k ≤ n rounds
  -- each cost at most 1 + c.
  iterC-bound : (A : Ty) (fG : GVal ℕ A → ℕ × GVal ℕ A) (c : ℕ)
              → (∀ x → proj₁ (fG x) ≤ c)
              → ∀ n k (a : GVal ℕ A) → k ≤ n
              → proj₁ (iterGW (λ _ → 0) k fG a) ≤ n * suc c
  iterC-bound A fG c h n zero a kn = z≤n
  iterC-bound A fG c h (suc n) (suc k) a (s≤s kn) =
    s≤s (+-mono-≤ (h a) (iterC-bound A fG c h n k (proj₂ (fG a)) kn))

  foldC-bound : (A B : Ty) (fG : (GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
                (c : ℕ)
              → (∀ p → proj₁ (fG p) ≤ c)
              → ∀ n xs (b : GVal ℕ B) → length xs ≤ n
              → proj₁ (foldGW (λ _ → 0) xs fG b) ≤ n * suc c
  foldC-bound A B fG c h n [] b hl = z≤n
  foldC-bound A B fG c h (suc n) (x ∷ xs) b (s≤s hl) =
    s≤s (+-mono-≤ (h (b , x))
      (foldC-bound A B fG c h n xs (proj₂ (fG (b , x))) hl))

  whileC-bound : (A : Ty) (tG : GVal ℕ A → ℕ × (⊤ ⊎ ⊤))
                 (sG : GVal ℕ A → ℕ × GVal ℕ A) (ct cs : ℕ)
               → (∀ x → proj₁ (tG x) ≤ ct)
               → (∀ x → proj₁ (sG x) ≤ cs)
               → ∀ n k (a : GVal ℕ A) → k ≤ n
               → proj₁ (whileGW A k tG sG a) ≤ n * suc (ct + cs)
  whileC-bound A tG sG ct cs ht hs n zero a kn = z≤n
  whileC-bound A tG sG ct cs ht hs (suc n) (suc k) a (s≤s kn)
    with proj₂ (tG a)
  ... | inj₁ _ =
    ≤-trans
      (≤-trans (ht a)
        (≤-trans (m≤m+n ct cs)
          (m≤m+n (ct + cs) (n * suc (ct + cs)))))
      (n≤1+n _)
  ... | inj₂ _ =
    let mt = proj₁ (tG a)
        ms = proj₁ (sG a)
        r  = proj₁ (whileGW A k tG sG (proj₂ (sG a)))
        ih = whileC-bound A tG sG ct cs ht hs n k (proj₂ (sG a)) kn
        inner : (mt + ms) + r ≤ (ct + cs) + n * suc (ct + cs)
        inner = +-mono-≤ (+-mono-≤ (ht a) (hs a)) ih
        inner′ : mt + (ms + r) ≤ (ct + cs) + n * suc (ct + cs)
        inner′ = subst (λ z → z ≤ (ct + cs) + n * suc (ct + cs))
                   (+-assoc mt ms r) inner
    in subst (λ z → z ≤ suc ((ct + cs) + n * suc (ct + cs)))
         (sym (+-suc mt (ms + r))) (s≤s inner′)

  -- dup-grade versions: no chargeStep, so k ≤ n rounds cost ≤ n · c.
  iterDC-bound : (A : Ty) (fG : GVal ℕ A → ℕ × GVal ℕ A) (c : ℕ)
               → (∀ x → proj₁ (fG x) ≤ c)
               → ∀ n k (a : GVal ℕ A) → k ≤ n
               → proj₁ (Dup.iterG (λ _ → 0) k fG a) ≤ n * c
  iterDC-bound A fG c h n zero a kn = z≤n
  iterDC-bound A fG c h (suc n) (suc k) a (s≤s kn) =
    +-mono-≤ (h a) (iterDC-bound A fG c h n k (proj₂ (fG a)) kn)

  foldDC-bound : (A B : Ty) (fG : (GVal ℕ B × GVal ℕ A) → ℕ × GVal ℕ B)
                 (c : ℕ)
               → (∀ p → proj₁ (fG p) ≤ c)
               → ∀ n xs (b : GVal ℕ B) → length xs ≤ n
               → proj₁ (Dup.foldG (λ _ → 0) xs fG b) ≤ n * c
  foldDC-bound A B fG c h n [] b hl = z≤n
  foldDC-bound A B fG c h (suc n) (x ∷ xs) b (s≤s hl) =
    +-mono-≤ (h (b , x))
      (foldDC-bound A B fG c h n xs (proj₂ (fG (b , x))) hl)

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
costW-sound iterCS topS h = (tt , tt)
costW-sound iterCS (pairS sbf topS) h = (tt , tt)
costW-sound iterCS (pairS sbf (pairS topS a0)) h = (tt , tt)
costW-sound iterCS (pairS topS (pairS (natLE N) a0)) h = (tt , tt)
costW-sound iterCS (pairS (bangS topS) (pairS (natLE N) a0)) h = (tt , tt)
costW-sound iterCS (pairS (bangS (lollyS nothing)) (pairS (natLE N) a0)) h =
  (tt , tt)
costW-sound (iterCS {A})
  (pairS (bangS (lollyS (just c))) (pairS (natLE N) a0))
  {gf , (gn , ga)} (relF , (hn , _)) =
  (iterC-bound A gf c (λ x → relF x) N gn ga hn , tt)
costW-sound foldCS topS h = (tt , tt)
costW-sound foldCS (pairS sbf topS) h = (tt , tt)
costW-sound foldCS (pairS sbf (pairS topS b0)) h = (tt , tt)
costW-sound foldCS (pairS topS (pairS (listS n es) b0)) h = (tt , tt)
costW-sound foldCS (pairS (bangS topS) (pairS (listS n es) b0)) h = (tt , tt)
costW-sound foldCS (pairS (bangS (lollyS nothing)) (pairS (listS n es) b0)) h =
  (tt , tt)
costW-sound (foldCS {A} {B})
  (pairS (bangS (lollyS (just c))) (pairS (listS n es) b0))
  {gf , (gxs , gb)} (relF , ((hlen , _) , _)) =
  (foldC-bound A B gf c (λ p → relF p) n gxs gb hlen , tt)
costW-sound whileCS topS h = (tt , tt)
costW-sound whileCS (pairS st topS) h = (tt , tt)
costW-sound whileCS (pairS st (pairS sf topS)) h = (tt , tt)
costW-sound whileCS (pairS st (pairS sf (pairS topS a0))) h = (tt , tt)
costW-sound whileCS (pairS topS (pairS sf (pairS (natLE N) a0))) h = (tt , tt)
costW-sound whileCS (pairS (bangS topS) (pairS sf (pairS (natLE N) a0))) h =
  (tt , tt)
costW-sound whileCS
  (pairS (bangS (lollyS nothing)) (pairS sf (pairS (natLE N) a0))) h =
  (tt , tt)
costW-sound whileCS
  (pairS (bangS (lollyS (just ct))) (pairS topS (pairS (natLE N) a0))) h =
  (tt , tt)
costW-sound whileCS
  (pairS (bangS (lollyS (just ct)))
    (pairS (bangS topS) (pairS (natLE N) a0))) h = (tt , tt)
costW-sound whileCS
  (pairS (bangS (lollyS (just ct)))
    (pairS (bangS (lollyS nothing)) (pairS (natLE N) a0))) h = (tt , tt)
costW-sound (whileCS {A})
  (pairS (bangS (lollyS (just ct)))
    (pairS (bangS (lollyS (just cs))) (pairS (natLE N) a0)))
  {gt , (gs , (gn , ga))} (relT , (relS , (hn , _))) =
  (whileC-bound A gt gs ct cs (λ x → relT x) (λ x → relS x) N gn ga hn , tt)
costW-sound (guardS t) s {ga} h
  with proj₂ (⟦ t ⟧C ga) | costW-sound t s {ga} h
... | inj₁ _ | (ct , _) = (ct , h)
... | inj₂ _ | (ct , _) = (ct , tt)
costW-sound (promoteS _) s h = (≤∞-zero _ , h)
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
-- unbounded work bound (nothing) is vacuously sound; topS output dominates.
costW-sound (recS t r l) s h = (tt , tt)

-- ── THE THEOREM: static duplication bound ──────────────────────────────────

costD-sound : {A B : Ty} (f : A ⇨ B) (s : Shape A) {ga : GVal ℕ A}
            → γW A s ga
            → (proj₁ (⟦ f ⟧D ga) ≤∞ proj₁ (costD f s))
              × γW B (proj₂ (costD f s)) (proj₂ (⟦ f ⟧D ga))
costD-sound idS s h = (≤∞-zero _ , h)
costD-sound (g ∘S f) s h =
  let (cf , rf) = costD-sound f s h
      (cg , rg) = costD-sound g (proj₂ (costD f s)) rf
  in (≤∞-+ _ _ cf cg , rg)
costD-sound (f ⊗S g) topS {a , c} h =
  let (cf , rf) = costD-sound f topS {a} tt
      (cg , rg) = costD-sound g topS {c} tt
  in (≤∞-+ _ _ cf cg , (rf , rg))
costD-sound (f ⊗S g) (pairS sa sc) {a , c} (ha , hc) =
  let (cf , rf) = costD-sound f sa ha
      (cg , rg) = costD-sound g sc hc
  in (≤∞-+ _ _ cf cg , (rf , rg))
costD-sound swapS topS h = (≤∞-zero _ , (tt , tt))
costD-sound swapS (pairS a b) (ha , hb) = (≤∞-zero _ , (hb , ha))
costD-sound assocS topS h = (≤∞-zero _ , (tt , (tt , tt)))
costD-sound assocS (pairS topS c) {(_ , _) , _} (_ , hc) =
  (≤∞-zero _ , (tt , (tt , hc)))
costD-sound assocS (pairS (pairS a b) c) ((ha , hb) , hc) =
  (≤∞-zero _ , (ha , (hb , hc)))
costD-sound unassocS topS h = (≤∞-zero _ , ((tt , tt) , tt))
costD-sound unassocS (pairS a topS) {_ , (_ , _)} (ha , _) =
  (≤∞-zero _ , ((ha , tt) , tt))
costD-sound unassocS (pairS a (pairS b c)) (ha , (hb , hc)) =
  (≤∞-zero _ , ((ha , hb) , hc))
costD-sound exlS topS h = (≤∞-zero _ , tt)
costD-sound exlS (pairS a b) (ha , _) = (≤∞-zero _ , ha)
costD-sound exrS topS h = (≤∞-zero _ , tt)
costD-sound exrS (pairS a b) (_ , hb) = (≤∞-zero _ , hb)
costD-sound weakS s h = (≤∞-zero _ , tt)
costD-sound runitS s h = (≤∞-zero _ , (h , tt))
costD-sound lunitS s h = (≤∞-zero _ , (tt , h))
costD-sound inlS s h = (≤∞-zero _ , h)
costD-sound inrS s h = (≤∞-zero _ , h)
costD-sound (caseS l r) topS {inj₁ a} h =
  let (cl , rl) = costD-sound l topS {a} tt
  in (≤∞-⊔l _ _ cl , ⊔S-lW (proj₂ (costD l topS)) (proj₂ (costD r topS)) rl)
costD-sound (caseS l r) topS {inj₂ b} h =
  let (cr , rr) = costD-sound r topS {b} tt
  in (≤∞-⊔r _ _ cr , ⊔S-rW (proj₂ (costD l topS)) (proj₂ (costD r topS)) rr)
costD-sound (caseS l r) (sumS (just sl) mr) {inj₁ a} h with mr
... | just sr =
  let (cl , rl) = costD-sound l sl h
  in (≤∞-⊔l _ _ cl , ⊔S-lW (proj₂ (costD l sl)) (proj₂ (costD r sr)) rl)
... | nothing = let (cl , rl) = costD-sound l sl h in (≤∞-⊔l _ _ cl , rl)
costD-sound (caseS l r) (sumS nothing mr) {inj₁ a} h = ⊥-elim h
costD-sound (caseS l r) (sumS ml (just sr)) {inj₂ b} h with ml
... | just sl =
  let (cr , rr) = costD-sound r sr h
  in (≤∞-⊔r _ _ cr , ⊔S-rW (proj₂ (costD l sl)) (proj₂ (costD r sr)) rr)
... | nothing = let (cr , rr) = costD-sound r sr h in (≤∞-⊔r _ _ cr , rr)
costD-sound (caseS l r) (sumS ml nothing) {inj₂ b} h = ⊥-elim h
costD-sound distlS topS {a , inj₁ b} h = (≤∞-zero _ , (tt , tt))
costD-sound distlS topS {a , inj₂ c} h = (≤∞-zero _ , (tt , tt))
costD-sound distlS (pairS sa topS) {a , inj₁ b} (ha , _) =
  (≤∞-zero _ , (ha , tt))
costD-sound distlS (pairS sa topS) {a , inj₂ c} (ha , _) =
  (≤∞-zero _ , (ha , tt))
costD-sound distlS (pairS sa (sumS (just sb) mc)) {a , inj₁ b} (ha , hb) =
  (≤∞-zero _ , (ha , hb))
costD-sound distlS (pairS sa (sumS nothing mc)) {a , inj₁ b} (ha , hb) = ⊥-elim hb
costD-sound distlS (pairS sa (sumS mb (just sc))) {a , inj₂ c} (ha , hc) =
  (≤∞-zero _ , (ha , hc))
costD-sound distlS (pairS sa (sumS mb nothing)) {a , inj₂ c} (ha , hc) = ⊥-elim hc
costD-sound nilS s h = (≤∞-zero _ , (z≤n , []))
costD-sound consS topS {x , xs} h = (≤∞-zero _ , tt)
costD-sound consS (pairS se topS) {x , xs} h = (≤∞-zero _ , tt)
costD-sound consS (pairS se (listS n ses)) {x , xs} (he , (hl , hes)) =
  (≤∞-zero _ , (s≤s hl , ⊔S-lW se ses he ∷ All.map (λ {y} → ⊔S-rW se ses {y}) hes))
costD-sound unconsS s {[]} h = (≤∞-zero _ , tt)
costD-sound unconsS topS {x ∷ xs} h = (≤∞-zero _ , (tt , tt))
costD-sound unconsS (listS n se) {x ∷ xs} (hl , hx ∷ hxs) =
  (≤∞-zero _ , (hx , (pred-len n hl , hxs)))
  where
    pred-len : ∀ {m} n → suc m ≤ n → m ≤ pred n
    pred-len (suc k) (s≤s p) = p
costD-sound natOutS topS {zero} h = (≤∞-zero _ , tt)
costD-sound natOutS topS {suc m} h = (≤∞-zero _ , tt)
costD-sound natOutS (natLE n) {zero} h = (≤∞-zero _ , tt)
costD-sound natOutS (natLE n) {suc m} h = (≤∞-zero _ , pred-le h)
  where
    pred-le : ∀ {m n} → suc m ≤ n → m ≤ pred n
    pred-le (s≤s p) = p
costD-sound sucS topS h = (≤∞-zero _ , tt)
costD-sound sucS (natLE n) h = (≤∞-zero _ , s≤s h)
costD-sound addS topS h = (≤∞-zero _ , tt)
costD-sound addS (pairS topS _) h = (≤∞-zero _ , tt)
costD-sound addS (pairS (natLE n) topS) h = (≤∞-zero _ , tt)
costD-sound addS (pairS (natLE n) (natLE m)) (ha , hb) =
  (≤∞-zero _ , +-mono-≤ ha hb)
costD-sound (constS k) s h = (≤∞-zero _ , ≤-refl)
costD-sound dupNatS s h = (≤-refl , (h , h))
costD-sound (copyS _) s h = (sizeS-sound s h , (h , h))
costD-sound (guardS t) s {ga} h with proj₂ (⟦ t ⟧D ga) | costD-sound t s {ga} h
... | inj₁ _ | (ct , _) = (≤∞-+ _ _ (sizeS-sound s h) ct , h)
... | inj₂ _ | (ct , _) = (≤∞-+ _ _ (sizeS-sound s h) ct , tt)
costD-sound (curryS f) s h =
  (≤∞-zero _ , λ ga → proj₁ (costD-sound f (pairS s topS) {_ , ga} (h , tt)))
costD-sound applyS topS {gf , ga} h = (tt , tt)
costD-sound applyS (pairS topS sa) {gf , ga} h = (tt , tt)
costD-sound applyS (pairS (lollyS mc) sa) {gf , ga} (relF , _) = (relF ga , tt)
costD-sound mapCS topS h = (tt , tt)
costD-sound mapCS (pairS topS topS) h = (tt , tt)
costD-sound mapCS (pairS (bangS topS) topS) h = (tt , tt)
costD-sound mapCS (pairS (bangS (lollyS nothing)) topS) h = (tt , tt)
costD-sound (mapCS {A} {B}) (pairS (bangS (lollyS (just 0))) topS)
  {gf , gxs} (relF , _) =
  (mapD-bound A B (λ _ → ⊤) gf (just 0) (λ x _ → relF x)
     (length gxs) gxs ≤-refl (all-⊤ gxs) , tt)
costD-sound mapCS (pairS (bangS (lollyS (just (suc k)))) topS) h = (tt , tt)
costD-sound (mapCS {A} {B}) (pairS topS (listS n es)) {gf , gxs}
  (_ , (hlen , _)) =
  (mapD-bound A B (λ _ → ⊤) gf nothing (λ _ _ → tt)
     n gxs hlen (all-⊤ gxs) , tt)
costD-sound (mapCS {A} {B}) (pairS (bangS topS) (listS n es)) {gf , gxs}
  (_ , (hlen , _)) =
  (mapD-bound A B (λ _ → ⊤) gf nothing (λ _ _ → tt)
     n gxs hlen (all-⊤ gxs) , tt)
costD-sound (mapCS {A} {B}) (pairS (bangS (lollyS nothing)) (listS n es))
  {gf , gxs} (_ , (hlen , _)) =
  (mapD-bound A B (λ _ → ⊤) gf nothing (λ _ _ → tt)
     n gxs hlen (all-⊤ gxs) , tt)
costD-sound (mapCS {A} {B}) (pairS (bangS (lollyS (just k))) (listS n es))
  {gf , gxs} (relF , (hlen , _)) =
  (mapD-bound A B (λ _ → ⊤) gf (just k) (λ x _ → relF x) n gxs hlen (all-⊤ gxs) , tt)
costD-sound iterCS topS h = (tt , tt)
costD-sound iterCS (pairS topS topS) h = (tt , tt)
costD-sound iterCS (pairS topS (pairS topS a0)) h = (tt , tt)
costD-sound iterCS (pairS topS (pairS (natLE zero) a0)) (_ , (z≤n , _)) =
  (z≤n , tt)
costD-sound iterCS (pairS topS (pairS (natLE (suc N)) a0)) h = (tt , tt)
costD-sound iterCS (pairS (bangS topS) topS) h = (tt , tt)
costD-sound iterCS (pairS (bangS topS) (pairS topS a0)) h = (tt , tt)
costD-sound iterCS (pairS (bangS topS) (pairS (natLE zero) a0))
  (_ , (z≤n , _)) = (z≤n , tt)
costD-sound iterCS (pairS (bangS topS) (pairS (natLE (suc N)) a0)) h =
  (tt , tt)
costD-sound iterCS (pairS (bangS (lollyS nothing)) topS) h = (tt , tt)
costD-sound iterCS (pairS (bangS (lollyS nothing)) (pairS topS a0)) h =
  (tt , tt)
costD-sound iterCS (pairS (bangS (lollyS nothing)) (pairS (natLE zero) a0))
  (_ , (z≤n , _)) = (z≤n , tt)
costD-sound iterCS
  (pairS (bangS (lollyS nothing)) (pairS (natLE (suc N)) a0)) h = (tt , tt)
costD-sound (iterCS {A}) (pairS (bangS (lollyS (just 0))) rest)
  {gf , (gn , ga)} (relF , _) =
  ( subst (λ z → proj₁ (Dup.iterG (λ _ → 0) gn gf ga) ≤ z)
      (*-zero-right gn)
      (iterDC-bound A gf 0 (λ x → relF x) gn gn ga ≤-refl)
  , tt)
costD-sound iterCS (pairS (bangS (lollyS (just (suc k)))) topS) h = (tt , tt)
costD-sound iterCS
  (pairS (bangS (lollyS (just (suc k)))) (pairS topS a0)) h = (tt , tt)
costD-sound iterCS
  (pairS (bangS (lollyS (just (suc k)))) (pairS (natLE zero) a0))
  (_ , (z≤n , _)) = (z≤n , tt)
costD-sound (iterCS {A})
  (pairS (bangS (lollyS (just (suc k)))) (pairS (natLE (suc N)) a0))
  {gf , (gn , ga)} (relF , (hn , _)) =
  (iterDC-bound A gf (suc k) (λ x → relF x) (suc N) gn ga hn , tt)
costD-sound foldCS (pairS topS topS) h = (tt , tt)
costD-sound foldCS topS h = (tt , tt)
costD-sound foldCS (pairS topS (pairS topS b0)) h = (tt , tt)
costD-sound (foldCS {A} {B}) (pairS topS (pairS (listS zero es) b0))
  {gf , (gxs , gb)} h =
  (len0-fold A B gf gxs gb (proj₁ (proj₁ (proj₂ h))) , tt)
costD-sound foldCS (pairS topS (pairS (listS (suc n) es) b0)) h = (tt , tt)
costD-sound foldCS (pairS (bangS topS) topS) h = (tt , tt)
costD-sound foldCS (pairS (bangS topS) (pairS topS b0)) h = (tt , tt)
costD-sound (foldCS {A} {B}) (pairS (bangS topS) (pairS (listS zero es) b0))
  {gf , (gxs , gb)} h =
  (len0-fold A B gf gxs gb (proj₁ (proj₁ (proj₂ h))) , tt)
costD-sound foldCS (pairS (bangS topS) (pairS (listS (suc n) es) b0)) h =
  (tt , tt)
costD-sound foldCS (pairS (bangS (lollyS nothing)) topS) h = (tt , tt)
costD-sound foldCS (pairS (bangS (lollyS nothing)) (pairS topS b0)) h =
  (tt , tt)
costD-sound (foldCS {A} {B})
  (pairS (bangS (lollyS nothing)) (pairS (listS zero es) b0))
  {gf , (gxs , gb)} h =
  (len0-fold A B gf gxs gb (proj₁ (proj₁ (proj₂ h))) , tt)
costD-sound foldCS
  (pairS (bangS (lollyS nothing)) (pairS (listS (suc n) es) b0)) h = (tt , tt)
costD-sound (foldCS {A} {B}) (pairS (bangS (lollyS (just 0))) rest)
  {gf , (gxs , gb)} (relF , _) =
  ( subst (λ z → proj₁ (Dup.foldG (λ _ → 0) gxs gf gb) ≤ z)
      (*-zero-right (length gxs))
      (foldDC-bound A B gf 0 (λ p → relF p) (length gxs) gxs gb ≤-refl)
  , tt)
costD-sound foldCS (pairS (bangS (lollyS (just (suc k)))) topS) h = (tt , tt)
costD-sound foldCS
  (pairS (bangS (lollyS (just (suc k)))) (pairS topS b0)) h = (tt , tt)
costD-sound (foldCS {A} {B})
  (pairS (bangS (lollyS (just (suc k)))) (pairS (listS zero es) b0))
  {gf , (gxs , gb)} h =
  (len0-fold A B gf gxs gb (proj₁ (proj₁ (proj₂ h))) , tt)
costD-sound (foldCS {A} {B})
  (pairS (bangS (lollyS (just (suc k)))) (pairS (listS (suc n) es) b0))
  {gf , (gxs , gb)} (relF , ((hlen , _) , _)) =
  (foldDC-bound A B gf (suc k) (λ p → relF p) (suc n) gxs gb hlen , tt)
costD-sound whileCS topS h = (tt , tt)
costD-sound whileCS (pairS st topS) h = (tt , tt)
costD-sound whileCS (pairS st (pairS sf topS)) h = (tt , tt)
costD-sound whileCS (pairS st (pairS sf (pairS topS a0))) h = (tt , tt)
costD-sound whileCS (pairS st (pairS sf (pairS (natLE zero) a0)))
  (_ , (_ , (z≤n , _))) = (z≤n , tt)
costD-sound whileCS (pairS st (pairS sf (pairS (natLE (suc N)) a0))) h =
  (tt , tt)
costD-sound (promoteS _) s h = (≤∞-zero _ , h)
costD-sound dupS s h = (sizeS-sound s h , (h , h))
costD-sound (boxS f) topS h = let (c , r) = costD-sound f topS tt in (c , r)
costD-sound (boxS f) (bangS s) h = let (c , r) = costD-sound f s h in (c , r)
costD-sound (boxValS f) s h = let (c , r) = costD-sound f s h in (c , r)
costD-sound mergeS topS {a , b} h = (≤∞-zero _ , (tt , tt))
costD-sound mergeS (pairS topS sb) {a , b} (_ , hb) =
  (≤∞-zero _ , (tt , unbang-γW sb hb))
costD-sound mergeS (pairS (bangS sa) sb) {a , b} (ha , hb) =
  (≤∞-zero _ , (ha , unbang-γW sb hb))
costD-sound (mapS {A} {B} f) topS {gxs} h
  with proj₁ (costD f topS) in eq
... | nothing = (tt , tt)
... | just 0 =
  (mapD-bound A B (λ _ → ⊤) ⟦ f ⟧D (just 0)
     (λ x _ → subst (λ z → proj₁ (⟦ f ⟧D x) ≤∞ z) eq
       (proj₁ (costD-sound f topS {x} tt)))
     (length gxs) gxs ≤-refl (all-⊤ gxs) , tt)
... | just (suc k) = (tt , tt)
costD-sound (mapS {A} {B} f) (listS n es) {gxs} (hlen , hall) =
  (mapD-bound A B (γW A es) ⟦ f ⟧D (proj₁ (costD f es))
     (λ x hx → proj₁ (costD-sound f es {x} hx)) n gxs hlen hall , tt)
costD-sound (iterS f) topS {gn , ga} h = (tt , tt)
costD-sound (iterS f) (pairS topS a0) {gn , ga} h = (tt , tt)
costD-sound (iterS {A} f) (pairS (natLE N) a0) {gn , ga} (hn , ha) =
  let (c , r) = iterD-bound A (costD f) ⟦ f ⟧D
                 (λ x {gx} rel → costD-sound f x {gx} rel)
                 N gn (unbang a0) {ga} hn (unbang-γW a0 ha)
  in (c , r)
costD-sound (foldS f) topS {gxs , gb} h = (tt , tt)
costD-sound (foldS f) (pairS topS b0) {gxs , gb} h = (tt , tt)
costD-sound (foldS {A} {B} f) (pairS (listS N es) b0) {gxs , gb}
  ((hlen , hxs) , hb) =
  let (c , r) = foldD-bound A B (γW A es) (λ x → costD f (pairS x es)) ⟦ f ⟧D
                 (λ x {gb′} {ge} relB he →
                   costD-sound f (pairS x es) {gb′ , ge} (relB , he))
                 N gxs (unbang b0) {gb} hlen hxs (unbang-γW b0 hb)
  in (c , r)
costD-sound (whileS t st) topS {gn , ga} h = (tt , tt)
costD-sound (whileS t st) (pairS topS a0) {gn , ga} h = (tt , tt)
costD-sound (whileS {A} t st) (pairS (natLE N) a0) {gn , ga} (hn , ha) =
  let (c , r) = whileD-bound A (λ x → proj₁ (costD t x)) (costD st)
                 ⟦ t ⟧D ⟦ st ⟧D
                 (λ x {gx} rel → proj₁ (costD-sound t x {gx} rel))
                 (λ x {gx} rel → costD-sound st x {gx} rel)
                 N gn (unbang a0) {ga} hn (unbang-γW a0 ha)
  in (c , r)
costD-sound (recS t r l) s h = (tt , tt)

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

-- Certified static duplication bound at a covered input shape.
dup-bounded-at : {A B : Ty} (f : A ⇨ B) (s : Shape A) {ga : GVal ℕ A}
               → γW A s ga → dupGrade f ga ≤∞ proj₁ (costD f s)
dup-bounded-at f s h = proj₁ (costD-sound f s h)

-- Certified static duplication bound for an arbitrary input.
dup-bounded : {A B : Ty} (f : A ⇨ B) (ga : GVal ℕ A)
            → dupGrade f ga ≤∞ proj₁ (costD f (shapeOfTy A))
dup-bounded {A} f ga = dup-bounded-at f (shapeOfTy A) (γW-shapeOfTy A ga)
