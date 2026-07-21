------------------------------------------------------------------------
-- T3.Abstract — budgets by calculated abstract interpretation.
--
-- Because Telomare recursion carries its fuel as DATA, "recursion
-- sizing" is value-range analysis of the nat flowing into each
-- iterS/foldS/whileS site.  This module gives:
--
--   * the abstract domain 'Shape' with meaning γ (a per-type predicate;
--     the input refinement is the initial shape — "refinements bound
--     open input" is the definition of the starting point);
--   * a sound join _⊔S_;
--   * budget trees 'BudgetD' indexed by the M3 recursion skeletons
--     (T3.Place.Skel): one Maybe ℕ per site, nothing = unsizable ⊤ —
--     which is a NOTICE (Tier 2 runs it metered), never a rejection;
--   * the transfer function 'transfer' — per-combinator best
--     abstractions where the calculation closes, topS (trivially sound)
--     where it does not; loops are FUEL-BOUNDED ABSTRACT UNROLLING
--     ('aiter'): iterate the step's transfer bound-many times, joining
--     shapes over every prefix and budgets over every unrolling.
--     an inner site is sized to the max over all outer iterations — Girard's
--     level-by-level bound — and is therefore the
--     DEFINITION, not an emergent behavior; S3 (producer evaluated
--     before its consumer is sized) is sequential composition.
--   * SOUNDNESS ('sound'): the logical relation γ s a →
--     γ (transfer f s) (⟦f⟧V a), proved for every combinator (loops via
--     'aiter-covers' + 'whileV-runs-as-iterV');
--   * the STABILITY lemma ('while-stable'): once the test stops the
--     loop, any additional fuel returns the same value — the
--     denotational content of "the inferred budget suffices".
--
-- test/BudgetOracle.hs mirrors this module with frozen compatibility oracles.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Abstract where

open import Data.Nat             using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s; pred)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; ⊔-mono-≤)
open import Data.Maybe           using (Maybe; just; nothing)
open import Data.Product         using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Unit            using (⊤; tt)
open import Data.Empty           using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong; subst)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value
open import T3.Place using (Skel; tip; bin; rec; call; skelOf; ε)

-- ────────────────────────────────────────────────────────────────────────────
-- § 1  The abstract domain
-- ────────────────────────────────────────────────────────────────────────────

data Shape : Ty → Set where
  topS   : {A : Ty} → Shape A
  unitS  : Shape unit
  natLE  : ℕ → Shape nat
  pairS  : {A B : Ty} → Shape A → Shape B → Shape (A ⊗ B)
  sumS   : {A B : Ty} → Maybe (Shape A) → Maybe (Shape B) → Shape (A ⊕ B)
  listS  : {A : Ty} → ℕ → Shape A → Shape (listT A)
  bangS  : {A : Ty} → Shape A → Shape (! A)
  lollyS : {A B : Ty} → Maybe ℕ → Shape (A ⊸ B)
    -- "applying this closure costs ≤ n work" (nothing = unbounded).
    -- Value-level meaning is trivial (γ below); the cost meaning lives
    -- in T3.Bound's work relation γW.

-- Meaning: which values a shape covers.
γ : {A : Ty} → Shape A → ⟦ A ⟧T → Set
γ topS          _        = ⊤
γ unitS         _        = ⊤
γ (natLE n)     m        = m ≤ n
γ (pairS s t)   (a , b)  = γ s a × γ t b
γ (sumS ms _)   (inj₁ a) = γMaybe ms a
  where γMaybe : {A : Ty} → Maybe (Shape A) → ⟦ A ⟧T → Set
        γMaybe (just s) a = γ s a
        γMaybe nothing  _ = ⊥
γ (sumS _ mt)   (inj₂ b) = γMaybe mt b
  where γMaybe : {A : Ty} → Maybe (Shape A) → ⟦ A ⟧T → Set
        γMaybe (just s) a = γ s a
        γMaybe nothing  _ = ⊥
γ (listS n s)   xs       = (length xs ≤ n) × All (γ s) xs
γ (bangS s)     a        = γ s a
γ (lollyS _)    _        = ⊤

joinMB : Maybe ℕ → Maybe ℕ → Maybe ℕ
joinMB (just a) (just b) = just (a ⊔ b)
joinMB _        _        = nothing

-- Join (⊔S): sound upper bound of two shapes.
joinM : {A : Ty} → (Shape A → Shape A → Shape A)
      → Maybe (Shape A) → Maybe (Shape A) → Maybe (Shape A)
joinM j (just x) (just y) = just (j x y)
joinM _ (just x) nothing  = just x
joinM _ nothing  y        = y

infixl 6 _⊔S_
_⊔S_ : {A : Ty} → Shape A → Shape A → Shape A
topS       ⊔S _          = topS
_          ⊔S topS       = topS
unitS      ⊔S unitS      = unitS
natLE a    ⊔S natLE b    = natLE (a ⊔ b)
pairS a b  ⊔S pairS c d  = pairS (a ⊔S c) (b ⊔S d)
sumS l r   ⊔S sumS l′ r′ = sumS (joinM _⊔S_ l l′) (joinM _⊔S_ r r′)
listS n a  ⊔S listS m b  = listS (n ⊔ m) (a ⊔S b)
bangS a    ⊔S bangS b    = bangS (a ⊔S b)
lollyS a   ⊔S lollyS b   = lollyS (joinMB a b)

⊔S-l : {A : Ty} (x y : Shape A) {a : ⟦ A ⟧T} → γ x a → γ (x ⊔S y) a
⊔S-r : {A : Ty} (x y : Shape A) {a : ⟦ A ⟧T} → γ y a → γ (x ⊔S y) a

⊔S-l topS        _           _  = tt
⊔S-l unitS       topS        _  = tt
⊔S-l unitS       unitS       _  = tt
⊔S-l (natLE a)   topS        _  = tt
⊔S-l (natLE a)   (natLE b)   h  = ≤-trans h (m≤m⊔n a b)
⊔S-l (pairS a b) topS        _  = tt
⊔S-l (pairS a b) (pairS c d) (ha , hb) = (⊔S-l a c ha , ⊔S-l b d hb)
⊔S-l (sumS l r)  topS        _  = tt
⊔S-l (sumS (just l) r)  (sumS l′ r′) {inj₁ _} h with l′
... | just l″ = ⊔S-l l l″ h
... | nothing = h
⊔S-l (sumS nothing r)   (sumS l′ r′) {inj₁ _} h = ⊥-elim h
⊔S-l (sumS l (just r))  (sumS l′ r′) {inj₂ _} h with r′
... | just r″ = ⊔S-l r r″ h
... | nothing = h
⊔S-l (sumS l nothing)   (sumS l′ r′) {inj₂ _} h = ⊥-elim h
⊔S-l (listS n a) topS        _  = tt
⊔S-l (listS n a) (listS m b) (hl , he) =
  (≤-trans hl (m≤m⊔n n m) , All.map (λ {x} → ⊔S-l a b {x}) he)
⊔S-l (bangS a)   topS        _  = tt
⊔S-l (bangS a)   (bangS b)   h  = ⊔S-l a b h
⊔S-l (lollyS a)  topS        _  = tt
⊔S-l (lollyS a)  (lollyS b)  _  = tt

⊔S-r topS        y           h  = tt
⊔S-r unitS       topS        _  = tt
⊔S-r unitS       unitS       _  = tt
⊔S-r (natLE a)   topS        _  = tt
⊔S-r (natLE a)   (natLE b)   h  = ≤-trans h (m≤n⊔m a b)
⊔S-r (pairS a b) topS        _  = tt
⊔S-r (pairS a b) (pairS c d) (hc , hd) = (⊔S-r a c hc , ⊔S-r b d hd)
⊔S-r (sumS l r)  topS        _  = tt
⊔S-r (sumS l r)  (sumS (just l′) r′) {inj₁ _} h with l
... | just l″ = ⊔S-r l″ l′ h
... | nothing = h
⊔S-r (sumS l r)  (sumS nothing r′)   {inj₁ _} h = ⊥-elim h
⊔S-r (sumS l r)  (sumS l′ (just r′)) {inj₂ _} h with r
... | just r″ = ⊔S-r r″ r′ h
... | nothing = h
⊔S-r (sumS l r)  (sumS l′ nothing)   {inj₂ _} h = ⊥-elim h
⊔S-r (listS n a) topS        _  = tt
⊔S-r (listS n a) (listS m b) (hl , he) =
  (≤-trans hl (m≤n⊔m n m) , All.map (λ {x} → ⊔S-r a b {x}) he)
⊔S-r (bangS a)   topS        _  = tt
⊔S-r (bangS a)   (bangS b)   h  = ⊔S-r a b h
⊔S-r (lollyS a)  topS        _  = tt
⊔S-r (lollyS a)  (lollyS b)  _  = tt

-- Structure-view helpers (each trivially sound, established inline in
-- `sound`): every Shape at a composite type views as its components.
splitP : {A B : Ty} → Shape (A ⊗ B) → Shape A × Shape B
splitP (pairS a b) = (a , b)
splitP topS        = (topS , topS)

splitE : {A B : Ty} → Shape (A ⊕ B) → Maybe (Shape A) × Maybe (Shape B)
splitE (sumS l r) = (l , r)
splitE topS       = (just topS , just topS)

unbang : {A : Ty} → Shape (! A) → Shape A
unbang (bangS s) = s
unbang topS      = topS

fuelOf : Shape nat → Maybe ℕ
fuelOf (natLE n) = just n
fuelOf topS      = nothing

lenOf : {A : Ty} → Shape (listT A) → Maybe ℕ
lenOf (listS n _) = just n
lenOf topS        = nothing

elemOf : {A : Ty} → Shape (listT A) → Shape A
elemOf (listS _ s) = s
elemOf topS        = topS

-- ────────────────────────────────────────────────────────────────────────────
-- § 2  Budgets: one Maybe ℕ per recursion site (nothing = unsizable ⊤)
-- ────────────────────────────────────────────────────────────────────────────

data BudgetD : Skel → Set where
  tipB  : BudgetD tip
  binB  : {s₁ s₂ : Skel} → BudgetD s₁ → BudgetD s₂ → BudgetD (bin s₁ s₂)
  recB  : {s : Skel} → Maybe ℕ → BudgetD s → BudgetD (rec s)
  callB : {k : ℕ} {s : Skel} → BudgetD s → BudgetD (call k s)

-- neutral (never-entered) budgets: 0 at every site
botBD : (s : Skel) → BudgetD s
botBD tip        = tipB
botBD (bin x y)  = binB (botBD x) (botBD y)
botBD (rec s)    = recB (just 0) (botBD s)
botBD (call _ s) = callB (botBD s)

-- unknown budgets: ⊤ at every site (used under unbounded fuel)
topBD : (s : Skel) → BudgetD s
topBD tip        = tipB
topBD (bin x y)  = binB (topBD x) (topBD y)
topBD (rec s)    = recB nothing (topBD s)
topBD (call _ s) = callB (topBD s)

joinBD : {s : Skel} → BudgetD s → BudgetD s → BudgetD s
joinBD tipB        tipB        = tipB
joinBD (binB a b)  (binB c d)  = binB (joinBD a c) (joinBD b d)
joinBD (recB m a)  (recB n b)  = recB (joinMB m n) (joinBD a b)
joinBD (callB a)   (callB b)   = callB (joinBD a b)

-- ────────────────────────────────────────────────────────────────────────────
-- § 3  The transfer function (with budget collection)
-- ────────────────────────────────────────────────────────────────────────────

-- Fuel-bounded abstract unrolling: shapes joined over every prefix
-- (a fuel value k ≤ n may stop anywhere), budgets joined over every
-- unrolling (S2: max over outer iterations, by construction).
aiter : {A : Ty} {sk : Skel}
      → (Shape A → BudgetD sk × Shape A) → ℕ → Shape A
      → BudgetD sk × Shape A
aiter {sk = sk} f zero    s = (botBD sk , s)
aiter          f (suc n) s =
  let (b₁ , s₁) = f s
      (bₙ , sₙ) = aiter f n s₁
  in (joinBD b₁ bₙ , s ⊔S sₙ)

transfer : {A B : Ty} (f : A ⇨ B) → Shape A
         → BudgetD (skelOf (ε f)) × Shape B
transfer idS          s = (tipB , s)
transfer (g ∘S f)     s =
  let (bf , sf) = transfer f s
      (bg , sg) = transfer g sf
  in (binB bg bf , sg)
transfer (f ⊗S g)     s =
  let (sa , sc) = splitP s
      (bf , sb) = transfer f sa
      (bg , sd) = transfer g sc
  in (binB bf bg , pairS sb sd)
transfer swapS        s = let (a , b) = splitP s in (tipB , pairS b a)
transfer assocS       s =
  let (ab , c) = splitP s ; (a , b) = splitP ab
  in (tipB , pairS a (pairS b c))
transfer unassocS     s =
  let (a , bc) = splitP s ; (b , c) = splitP bc
  in (tipB , pairS (pairS a b) c)
transfer exlS         s = (tipB , proj₁ (splitP s))
transfer exrS         s = (tipB , proj₂ (splitP s))
transfer weakS        s = (tipB , unitS)
transfer runitS       s = (tipB , pairS s unitS)
transfer lunitS       s = (tipB , pairS unitS s)
transfer inlS         s = (tipB , sumS (just s) nothing)
transfer inrS         s = (tipB , sumS nothing (just s))
transfer (caseS l r)  s =
  let (ml , mr) = splitE s
      resL = mapMaybeT (transfer l) ml
      resR = mapMaybeT (transfer r) mr
  in (binB (budgetOf (skelOf (ε l)) resL) (budgetOf (skelOf (ε r)) resR)
     , joinRes resL resR)
  where
    mapMaybeT : {A B : Ty} {sk : Skel}
              → (Shape A → BudgetD sk × Shape B)
              → Maybe (Shape A) → Maybe (BudgetD sk × Shape B)
    mapMaybeT f (just s) = just (f s)
    mapMaybeT _ nothing  = nothing
    budgetOf : {B : Ty} (sk : Skel) → Maybe (BudgetD sk × Shape B) → BudgetD sk
    budgetOf sk (just (b , _)) = b
    budgetOf sk nothing        = botBD sk
    joinRes : {B : Ty} {sk₁ sk₂ : Skel}
            → Maybe (BudgetD sk₁ × Shape B) → Maybe (BudgetD sk₂ × Shape B)
            → Shape B
    joinRes (just (_ , x)) (just (_ , y)) = x ⊔S y
    joinRes (just (_ , x)) nothing        = x
    joinRes nothing        (just (_ , y)) = y
    joinRes nothing        nothing        = topS
transfer distlS       s =
  let (a , bc) = splitP s
      (mb , mc) = splitE bc
  in (tipB , sumS (wrapP a mb) (wrapP a mc))
  where
    wrapP : {X Y : Ty} → Shape X → Maybe (Shape Y) → Maybe (Shape (X ⊗ Y))
    wrapP x (just y) = just (pairS x y)
    wrapP _ nothing  = nothing
transfer nilS         s = (tipB , listS 0 topS)
transfer consS        s =
  let (e , l) = splitP s
  in (tipB , listSuc e l)
  where
    listSuc : {A : Ty} → Shape A → Shape (listT A) → Shape (listT A)
    listSuc e (listS n es) = listS (suc n) (e ⊔S es)
    listSuc e topS         = topS
transfer unconsS      s = (tipB
  , sumS (just unitS) (just (pairS (elemOf s) (predList s))))
  where
    predList : {A : Ty} → Shape (listT A) → Shape (listT A)
    predList (listS n es) = listS (pred n) es
    predList topS         = topS
transfer natOutS      s = (tipB , out s)
  where
    out : Shape nat → Shape (unit ⊕ nat)
    out (natLE n) = sumS (just unitS) (just (natLE (pred n)))
    out topS      = sumS (just unitS) (just topS)
transfer sucS         s = (tipB , sucSh s)
  where
    sucSh : Shape nat → Shape nat
    sucSh (natLE n) = natLE (suc n)
    sucSh topS      = topS
transfer addS         s =
  let (a , b) = splitP s in (tipB , addSh a b)
  where
    addSh : Shape nat → Shape nat → Shape nat
    addSh (natLE n) (natLE m) = natLE (n + m)
    addSh _         _         = topS
transfer (constS k)   s = (tipB , natLE k)
transfer dupNatS      s = (tipB , pairS s s)
transfer (copyS _)    s = (tipB , pairS s s)
transfer (curryS f)   s =
  -- run the body abstractly at ⊤ to produce a budget of the right
  -- skeleton index; the closure value itself is unanalyzed (topS)
  (proj₁ (transfer f topS) , topS)
transfer applyS       s = (tipB , topS)
transfer mapCS        s = (recB nothing (topBD tip) , topS)
transfer (guardS t)   s =
  let (bt , _) = transfer t s
  in (bt , sumS (just s) (just unitS))
transfer (promoteS _) s = (tipB , bangS s)
transfer dupS         s = (tipB , pairS s s)
transfer (boxS f)     s = let (b , r) = transfer f (unbang s) in (b , bangS r)
transfer (boxValS f)  s = let (b , r) = transfer f s in (b , bangS r)
transfer mergeS       s =
  let (a , b) = splitP s in (tipB , bangS (pairS (unbang a) (unbang b)))
transfer (mapS f)     s = (recB nothing (topBD _) , topS)
transfer (iterS f)    s =
  let (fu , a0) = splitP s
  in loop (fuelOf fu) (unbang a0)
  where
    loop : Maybe ℕ → Shape _ → BudgetD _ × Shape _
    loop (just n) a0 =
      let (b , r) = aiter (transfer f) n a0
      in (recB (just n) b , bangS r)
    loop nothing  a0 = (recB nothing (topBD _) , topS)
transfer (foldS f)    s =
  let (ls , b0) = splitP s
  in loop (lenOf ls) (elemOf ls) (unbang b0)
  where
    loop : Maybe ℕ → Shape _ → Shape _ → BudgetD _ × Shape _
    loop (just n) es a0 =
      let (b , r) = aiter (λ x → transfer f (pairS x es)) n a0
      in (recB (just n) b , bangS r)
    loop nothing  _  a0 = (recB nothing (topBD _) , topS)
transfer (whileS t st) s =
  let (fu , a0) = splitP s
  in loop (fuelOf fu) (unbang a0)
  where
    step : Shape _ → BudgetD _ × Shape _
    step x =
      let (bt , _) = transfer t x
          (bs , r) = transfer st x
      in (binB bt bs , r)
    loop : Maybe ℕ → Shape _ → BudgetD _ × Shape _
    loop (just n) a0 =
      let (b , r) = aiter step n a0
      in (recB (just n) b , bangS r)
    loop nothing  a0 = (recB nothing (topBD _) , topS)

-- ────────────────────────────────────────────────────────────────────────────
-- § 4  Soundness: the logical relation
-- ────────────────────────────────────────────────────────────────────────────

-- shapes at !A view down soundly
unbang-γ : {A : Ty} (s : Shape (! A)) {a : ⟦ A ⟧T} → γ s a → γ (unbang s) a
unbang-γ (bangS x) h = h
unbang-γ topS      h = tt

-- aiter covers every k-fold iterate with k ≤ n.
aiter-covers : {A : Ty} {sk : Skel}
             → (f♯ : Shape A → BudgetD sk × Shape A) (fv : ⟦ A ⟧T → ⟦ A ⟧T)
             → (h : ∀ (x : Shape A) {a} → γ x a → γ (proj₂ (f♯ x)) (fv a))
             → ∀ n k (s : Shape A) {a} → k ≤ n → γ s a
             → γ (proj₂ (aiter f♯ n s)) (iterV k fv a)
aiter-covers f♯ fv h zero    zero    s _  hs = hs
aiter-covers f♯ fv h (suc n) zero    s _  hs =
  ⊔S-l s (proj₂ (aiter f♯ n (proj₂ (f♯ s)))) hs
aiter-covers f♯ fv h (suc n) (suc k) s (s≤s kn) hs =
  ⊔S-r s (proj₂ (aiter f♯ n (proj₂ (f♯ s))))
    (aiter-covers f♯ fv h n k (proj₂ (f♯ s)) kn (h s hs))

-- afold covers every fold over a covered list of bounded length.
afold-covers : {A B : Ty} {sk : Skel}
  → (f♯ : Shape B → BudgetD sk × Shape B)
  → (fv : ⟦ B ⟧T × ⟦ A ⟧T → ⟦ B ⟧T) (se : Shape A)
  → (h : ∀ (x : Shape B) {b e} → γ x b → γ se e
       → γ (proj₂ (f♯ x)) (fv (b , e)))
  → ∀ (s0 : Shape B) (xs : List ⟦ A ⟧T) n {b} → length xs ≤ n
  → All (γ se) xs → γ s0 b
  → γ (proj₂ (aiter f♯ n s0)) (foldV xs fv b)
afold-covers f♯ fv se h s0 []       zero    _        _          hb = hb
afold-covers f♯ fv se h s0 []       (suc n) _        _          hb =
  ⊔S-l s0 (proj₂ (aiter f♯ n (proj₂ (f♯ s0)))) hb
afold-covers f♯ fv se h s0 (x ∷ xs) (suc n) (s≤s hl) (hx ∷ hxs) hb =
  ⊔S-r s0 (proj₂ (aiter f♯ n (proj₂ (f♯ s0))))
    (afold-covers f♯ fv se h (proj₂ (f♯ s0)) xs n hl hxs (h s0 hb hx))

-- whileV runs as some ≤-fuel iterate of its step.
whileV-runs-as-iterV : {A : Set} (n : ℕ) (t : A → ⊤ ⊎ ⊤) (st : A → A) (a : A)
  → Σ ℕ (λ k → (k ≤ n) × (whileV n t st a ≡ iterV k st a))
whileV-runs-as-iterV zero    t st a = (zero , (z≤n , refl))
whileV-runs-as-iterV (suc n) t st a with t a
... | inj₁ _ = (zero , (z≤n , refl))
... | inj₂ _ =
  let (k , (kn , eq)) = whileV-runs-as-iterV n t st (st a)
  in (suc k , (s≤s kn , eq))

sound : {A B : Ty} (f : A ⇨ B) (s : Shape A) {a : ⟦ A ⟧T}
      → γ s a → γ (proj₂ (transfer f s)) (⟦ f ⟧V a)
sound idS s h = h
sound (g ∘S f) s h = sound g (proj₂ (transfer f s)) (sound f s h)
sound (f ⊗S g) topS {a , c} h = (sound f topS tt , sound g topS tt)
sound (f ⊗S g) (pairS sa sc) {a , c} (ha , hc) =
  (sound f sa ha , sound g sc hc)
sound swapS topS h = (tt , tt)
sound swapS (pairS a b) (ha , hb) = (hb , ha)
sound assocS topS h = (tt , (tt , tt))
sound assocS (pairS topS c) {( _ , _ ) , _} (_ , hc) = (tt , (tt , hc))
sound assocS (pairS (pairS a b) c) ((ha , hb) , hc) = (ha , (hb , hc))
sound unassocS topS h = ((tt , tt) , tt)
sound unassocS (pairS a topS) {_ , (_ , _)} (ha , _) = ((ha , tt) , tt)
sound unassocS (pairS a (pairS b c)) (ha , (hb , hc)) = ((ha , hb) , hc)
sound exlS topS h = tt
sound exlS (pairS a b) (ha , _) = ha
sound exrS topS h = tt
sound exrS (pairS a b) (_ , hb) = hb
sound weakS s h = tt
sound runitS s h = (h , tt)
sound lunitS s h = (tt , h)
sound inlS s h = h
sound inrS s h = h
sound (caseS l r) topS {inj₁ a} h =
  ⊔S-l (proj₂ (transfer l topS)) (proj₂ (transfer r topS)) (sound l topS tt)
sound (caseS l r) topS {inj₂ b} h =
  ⊔S-r (proj₂ (transfer l topS)) (proj₂ (transfer r topS)) (sound r topS tt)
sound (caseS l r) (sumS (just sl) mr) {inj₁ a} h with mr
... | just sr = ⊔S-l (proj₂ (transfer l sl)) (proj₂ (transfer r sr)) (sound l sl h)
... | nothing = sound l sl h
sound (caseS l r) (sumS nothing mr) {inj₁ a} h = ⊥-elim h
sound (caseS l r) (sumS ml (just sr)) {inj₂ b} h with ml
... | just sl = ⊔S-r (proj₂ (transfer l sl)) (proj₂ (transfer r sr)) (sound r sr h)
... | nothing = sound r sr h
sound (caseS l r) (sumS ml nothing) {inj₂ b} h = ⊥-elim h
sound distlS topS {a , inj₁ b} h = (tt , tt)
sound distlS topS {a , inj₂ c} h = (tt , tt)
sound distlS (pairS sa topS) {a , inj₁ b} (ha , _) = (ha , tt)
sound distlS (pairS sa topS) {a , inj₂ c} (ha , _) = (ha , tt)
sound distlS (pairS sa (sumS (just sb) mc)) {a , inj₁ b} (ha , hb) = (ha , hb)
sound distlS (pairS sa (sumS nothing mc)) {a , inj₁ b} (ha , hb) = ⊥-elim hb
sound distlS (pairS sa (sumS mb (just sc))) {a , inj₂ c} (ha , hc) = (ha , hc)
sound distlS (pairS sa (sumS mb nothing)) {a , inj₂ c} (ha , hc) = ⊥-elim hc
sound nilS s h = (z≤n , [])
sound consS topS {x , xs} h = tt
sound consS (pairS se topS) {x , xs} _ = tt
sound consS (pairS se (listS n ses)) {x , xs} (he , (hl , hes)) =
  (s≤s hl , ⊔S-l se ses he ∷ All.map (λ {y} → ⊔S-r se ses {y}) hes)
sound (unconsS {A}) s {[]} h = tt
sound (unconsS {A}) topS {x ∷ xs} h = (tt , tt)
sound (unconsS {A}) (listS n se) {x ∷ xs} (hl , hx ∷ hxs) =
  (hx , (pred-len n hl , hxs))
  where
    pred-len : ∀ {m} n → suc m ≤ n → m ≤ pred n
    pred-len (suc k) (s≤s p) = p
sound natOutS topS {zero} h = tt
sound natOutS topS {suc m} h = tt
sound natOutS (natLE n) {zero} h = tt
sound natOutS (natLE n) {suc m} h = pred-le h
  where
    pred-le : ∀ {m n} → suc m ≤ n → m ≤ pred n
    pred-le (s≤s p) = p
sound sucS topS h = tt
sound sucS (natLE n) h = s≤s h
sound addS topS h = tt
sound addS (pairS topS _) h = tt
sound addS (pairS (natLE n) topS) h = tt
sound addS (pairS (natLE n) (natLE m)) (ha , hb) = +-mono-≤′ ha hb
  where
    open import Data.Nat.Properties using (+-mono-≤)
    +-mono-≤′ = +-mono-≤
sound (constS k) s h = ≤-refl
sound dupNatS s h = (h , h)
sound (copyS _) s h = (h , h)
sound (curryS f) s h = tt
sound applyS s h = tt
sound mapCS s h = tt
sound (guardS t) s {a} h with ⟦ t ⟧V a
... | inj₁ _ = h
... | inj₂ _ = tt
sound (promoteS _) s h = h
sound dupS s h = (h , h)
sound (boxS f) topS h = sound f topS tt
sound (boxS f) (bangS s) h = sound f s h
sound (boxValS f) s h = sound f s h
sound mergeS topS {a , b} h = (tt , tt)
sound mergeS (pairS topS sb) {a , b} (_ , hb) = (tt , unbang-γ sb hb)
sound mergeS (pairS (bangS sa) sb) {a , b} (ha , hb) = (ha , unbang-γ sb hb)
sound (mapS f) s h = tt
sound (iterS f) topS {n , a} h = tt
sound (iterS f) (pairS topS sa) {n , a} h = tt
sound (iterS f) (pairS (natLE N) sa) {n , a} (hn , ha) =
  aiter-covers (transfer f) ⟦ f ⟧V (sound f) N n (unbang sa) hn
    (unbang-γ sa ha)
sound (foldS f) topS {xs , b} h = tt
sound (foldS f) (pairS topS sb) {xs , b} h = tt
sound (foldS f) (pairS (listS N se) sb) {xs , b} ((hl , hxs) , hb) =
  afold-covers (λ x → transfer f (pairS x se)) ⟦ f ⟧V se
    (λ x hx he → sound f (pairS x se) (hx , he))
    (unbang sb) xs N hl hxs (unbang-γ sb hb)
sound (whileS t st) topS {n , a} h = tt
sound (whileS t st) (pairS topS sa) {n , a} h = tt
sound (whileS {A} t st) (pairS (natLE N) sa) {n , a} (hn , ha) =
  let (k , (kn , eq)) = whileV-runs-as-iterV n ⟦ t ⟧V ⟦ st ⟧V a
  in subst (γ (proj₂ (aiter step N (unbang sa)))) (sym eq)
       (aiter-covers step ⟦ st ⟧V hstep N k (unbang sa)
         (≤-trans kn hn) (unbang-γ sa ha))
  where
    step : Shape A
         → BudgetD (bin (skelOf (ε t)) (skelOf (ε st))) × Shape A
    step x = let (bt , _) = transfer t x
                 (bs , r) = transfer st x
             in (binB bt bs , r)
    hstep : ∀ (x : Shape A) {a′} → γ x a′ → γ (proj₂ (step x)) (⟦ st ⟧V a′)
    hstep x hx = sound st x hx

-- ────────────────────────────────────────────────────────────────────────────
-- § 5  Stability: a sufficient budget is canonical
-- ────────────────────────────────────────────────────────────────────────────

-- Once the loop has stopped (its test fails at the reached state), any
-- additional fuel returns the same value. The surface meaning "run at the
-- inferred budget" does not depend on WHICH sufficient budget inference
-- found.
while-stable : {A : Set} (n k : ℕ) (t : A → ⊤ ⊎ ⊤) (st : A → A) (a : A)
  → t (whileV n t st a) ≡ inj₁ tt
  → whileV (n + k) t st a ≡ whileV n t st a
while-stable zero k t st a stop = stopped k stop
  where
    stopped : ∀ k → t a ≡ inj₁ tt → whileV k t st a ≡ a
    stopped zero    _  = refl
    stopped (suc k) eq with t a | eq
    ... | inj₁ tt | _ = refl
    ... | inj₂ tt | ()
while-stable (suc n) k t st a stop with t a | stop
... | inj₁ tt | _     = refl
... | inj₂ tt | stop′ = while-stable n k t st (st a) stop′
