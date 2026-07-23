------------------------------------------------------------------------
-- T3.Place — erasure, factorization, and placement as a universal
-- property on the compiler-owned fragment.
--
-- Three layers:
--
-- 1. ERASURE ε : E → S and the FACTORIZATION THEOREM
--        stripV ∘ ⟦_⟧V ≡ ⟦ ε _ ⟧VS ∘ stripV
--    — ⟦!A⟧T = ⟦A⟧T upgraded to a functor identity:
--    decorations are semantically invisible.  Both tiers compute the same
--    function; tier assignment is observationally invisible (the
--    fidelity theorem's semantic half).
--
-- 2. PLACEMENT.  A decoration is abstracted to its LEVEL STRUCTURE: a
--    recursion skeleton (Skel) with a ℕ at every recursion site (Deco).
--    `Solves d` is stratification ("every site sits at or below its
--    ambient level; contents run one level deeper; call arguments are
--    pulled `k` levels down").  Theorems:
--      * solves-meet : solutions are closed under pointwise ⊓
--        (difference constraints are min-closed — the reason a least
--        decoration EXISTS);
--      * place-solves, place-least : the structural walk (the Levels.hs
--        recipe: containment + offsets, no search) computes a solution
--        that is ⊑ every solution — THE least-boxing universal property.
--
-- 3. THE BRIDGE core-dominates: every well-typed core term e, read at
--    ambient depth d, IS a solution (core-solves), hence sits above the
--    structural placement of its own erasure.  This is the Galois-
--    insertion content, machine-checked: place ∘ ε is a lower bound of
--    the identity on decorations.
--
-- Scope note (honest): Deco abstracts a decoration to its site levels;
-- the full syntactic fiber over two-level types (which box constructor
-- goes where) is finer, but every element of it projects to a Deco that
-- core-solves covers.  The same-level-feedback emptiness (λn.n n) is the
-- one-line arithmetic fact sameLevelFeedback-unsat below: a level
-- constraint ℓ ≥ ℓ + 1 has no solution — in the first-order core the
-- pattern is unwritable by construction (iterS takes its step as
-- syntax); the constraint form is what the higher-order surface (M6
-- elaboration) will emit for it, routing the program to Tier 2.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module T3.Place where

open import Data.Nat             using (ℕ; zero; suc; _+_; _⊓_; _≤_; s≤s)
open import Data.Nat.Properties  using (≤-refl; ≤-trans; +-monoˡ-≤; ⊓-glb;
                                        ⊓-mono-≤; ⊓-idem; m⊓n≤m; m⊓n≤n;
                                        n≤1+n; 1+n≰n)
open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Product         using (_×_; _,_)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Unit            using (⊤; tt)
open import Data.List            using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise
                                 using (Pointwise; []; _∷_)
open import Relation.Nullary     using (¬_)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import T3.Core.Ty
open import T3.Core.Syntax
open import T3.Sem.Value
open import T3.Surface.Ty
open import T3.Surface.Syntax
open import T3.Surface.Sem

-- ────────────────────────────────────────────────────────────────────────────
-- § 1  Erasure and factorization
-- ────────────────────────────────────────────────────────────────────────────

ε : {A B : Ty} → A ⇨ B → strip A ⇨U strip B
ε idS          = idU
ε (g ∘S f)     = ε g ∘U ε f
ε (f ⊗S g)     = ε f ⊗U ε g
ε swapS        = swapU
ε assocS       = assocU
ε unassocS     = unassocU
ε exlS         = exlU
ε exrS         = exrU
ε weakS        = weakU
ε runitS       = runitU
ε lunitS       = lunitU
ε inlS         = inlU
ε inrS         = inrU
ε (caseS l r)  = caseU (ε l) (ε r)
ε distlS       = distlU
ε nilS         = nilU
ε consS        = consU
ε unconsS      = unconsU
ε natOutS      = natOutU
ε sucS         = sucU
ε addS         = addU
ε (constS k)   = constU k
ε dupNatS      = dupU          -- the atom exemption erases to free dup
ε (copyS _)    = dupU          -- costed data copy erases to free dup
ε (curryS f)   = curryU (ε f)
ε applyS       = applyU
ε mapCS        = mapCU
ε iterCS       = iterCU
ε foldCS       = foldCU
ε whileCS      = whileCU
ε (guardS t)   = guardU (ε t)
ε (promoteS _) = idU           -- data promotion is value-invisible
ε dupS         = dupU          -- contraction erases to free dup
ε (boxS f)     = ε f           -- boxes erase
ε (boxValS f)  = ε f
ε mergeS       = idU
ε (mapS f)     = mapU (ε f)
ε (iterS f)    = iterU (ε f)
ε (foldS f)    = foldU (ε f)
ε (whileS t s) = whileU (ε t) (ε s)
ε (recS t r l) = recU (ε t) (ε r) (ε l)

-- First-order (arrow-free) types: where erasure is a value identity and
-- the factorization theorem is propositional.  Recursive ⊤/⊥ so concrete
-- instantiations are literal tt-tuples.
fo : Ty → Set
fo unit      = ⊤
fo nat       = ⊤
fo (A ⊗ B)   = fo A × fo B
fo (A ⊕ B)   = fo A × fo B
fo (listT A) = fo A
fo (! A)     = fo A
fo (A ⊸ B)   = ⊥

-- The erasure logical relation: structural equality below arrows,
-- pointwise at arrows.  Closures made the propositional factorization
-- unavailable at arrow types (function equality needs funext); ε-rel
-- below is its strongest --safe form, and the fo-gated ε-factor at the
-- bottom recovers the original propositional statement at first-order
-- endpoints.
≈ε : (A : Ty) → ⟦ A ⟧T → ⟦ strip A ⟧U → Set
≈ε unit      _        _        = ⊤
≈ε nat       n        u        = n ≡ u
≈ε (A ⊗ B)   (a , b)  (ua , ub) = ≈ε A a ua × ≈ε B b ub
≈ε (A ⊕ B)   (inj₁ a) (inj₁ u) = ≈ε A a u
≈ε (A ⊕ B)   (inj₂ b) (inj₂ u) = ≈ε B b u
≈ε (A ⊕ B)   (inj₁ _) (inj₂ _) = ⊥
≈ε (A ⊕ B)   (inj₂ _) (inj₁ _) = ⊥
≈ε (listT A) xs       us       = Pointwise (≈ε A) xs us
≈ε (! A)     a        u        = ≈ε A a u
≈ε (A ⊸ B)   f        g        = ∀ a u → ≈ε A a u → ≈ε B (f a) (g u)

private
  ≈ε-verdict : (v : ⟦ unit ⊕ unit ⟧T) (u : ⟦ strip (unit ⊕ unit) ⟧U)
             → ≈ε (unit ⊕ unit) v u → v ≡ u
  ≈ε-verdict (inj₁ tt) (inj₁ tt) _ = refl
  ≈ε-verdict (inj₂ tt) (inj₂ tt) _ = refl
  ≈ε-verdict (inj₁ tt) (inj₂ tt) ()
  ≈ε-verdict (inj₂ tt) (inj₁ tt) ()

  map-rel : (A B : Ty)
            (fv : ⟦ A ⟧T → ⟦ B ⟧T) (fu : ⟦ strip A ⟧U → ⟦ strip B ⟧U)
          → (∀ x u → ≈ε A x u → ≈ε B (fv x) (fu u))
          → ∀ xs us → Pointwise (≈ε A) xs us
          → Pointwise (≈ε B) (mapV fv xs) (mapV fu us)
  map-rel A B fv fu h [] [] [] = []
  map-rel A B fv fu h (x ∷ xs) (u ∷ us) (r ∷ rs) =
    h x u r ∷ map-rel A B fv fu h xs us rs

  iter-rel : (A : Ty) (n : ℕ)
             (fv : ⟦ A ⟧T → ⟦ A ⟧T) (fu : ⟦ strip A ⟧U → ⟦ strip A ⟧U)
           → (∀ x u → ≈ε A x u → ≈ε A (fv x) (fu u))
           → ∀ a u → ≈ε A a u → ≈ε A (iterV n fv a) (iterV n fu u)
  iter-rel A zero    fv fu h a u r = r
  iter-rel A (suc n) fv fu h a u r =
    iter-rel A n fv fu h (fv a) (fu u) (h a u r)

  fold-rel : (A B : Ty)
             (fv : ⟦ B ⟧T × ⟦ A ⟧T → ⟦ B ⟧T)
             (fu : ⟦ strip B ⟧U × ⟦ strip A ⟧U → ⟦ strip B ⟧U)
           → (∀ b ub x ux → ≈ε B b ub → ≈ε A x ux
              → ≈ε B (fv (b , x)) (fu (ub , ux)))
           → ∀ xs us → Pointwise (≈ε A) xs us
           → ∀ b ub → ≈ε B b ub
           → ≈ε B (foldV xs fv b) (foldV us fu ub)
  fold-rel A B fv fu h [] [] [] b ub rb = rb
  fold-rel A B fv fu h (x ∷ xs) (u ∷ us) (r ∷ rs) b ub rb =
    fold-rel A B fv fu h xs us rs (fv (b , x)) (fu (ub , u)) (h b ub x u rb r)

  whileGo-rel : (A : Ty) (n : ℕ)
                (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤) (tu : ⟦ strip A ⟧U → ⊤ ⊎ ⊤)
                (sv : ⟦ A ⟧T → ⟦ A ⟧T) (su : ⟦ strip A ⟧U → ⟦ strip A ⟧U)
              → (∀ x u → ≈ε A x u → tv x ≡ tu u)
              → (∀ x u → ≈ε A x u → ≈ε A (sv x) (su u))
              → ∀ a u → ≈ε A a u → (r : ⊤ ⊎ ⊤)
              → ≈ε A (whileV-go n tv sv a r) (whileV-go n tu su u r)
  while-rel   : (A : Ty) (n : ℕ)
                (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤) (tu : ⟦ strip A ⟧U → ⊤ ⊎ ⊤)
                (sv : ⟦ A ⟧T → ⟦ A ⟧T) (su : ⟦ strip A ⟧U → ⟦ strip A ⟧U)
              → (∀ x u → ≈ε A x u → tv x ≡ tu u)
              → (∀ x u → ≈ε A x u → ≈ε A (sv x) (su u))
              → ∀ a u → ≈ε A a u
              → ≈ε A (whileV n tv sv a) (whileV n tu su u)

  whileGo-rel A n tv tu sv su ht hs a u rel (inj₁ _) = rel
  whileGo-rel A n tv tu sv su ht hs a u rel (inj₂ _) =
    while-rel A n tv tu sv su ht hs (sv a) (su u) (hs a u rel)

  while-rel A zero    tv tu sv su ht hs a u rel = rel
  while-rel A (suc n) tv tu sv su ht hs a u rel
    with tv a | tu u | ht a u rel
  ... | inj₁ _ | .(inj₁ _) | refl = rel
  ... | inj₂ _ | .(inj₂ _) | refl =
    while-rel A n tv tu sv su ht hs (sv a) (su u) (hs a u rel)

  rec-rel : (A B : Ty) (n : ℕ)
            (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤) (tu : ⟦ strip A ⟧U → ⊤ ⊎ ⊤)
            (rv : ((⟦ A ⟧T → ⟦ B ⟧T) × ⟦ A ⟧T) → ⟦ B ⟧T)
            (ru : ((⟦ strip A ⟧U → ⟦ strip B ⟧U) × ⟦ strip A ⟧U) → ⟦ strip B ⟧U)
            (lv : ⟦ A ⟧T → ⟦ B ⟧T) (lu : ⟦ strip A ⟧U → ⟦ strip B ⟧U)
          → (∀ x u → ≈ε A x u → tv x ≡ tu u)
          → (∀ fv fu x u → ≈ε (A ⊸ B) fv fu → ≈ε A x u
             → ≈ε B (rv (fv , x)) (ru (fu , u)))
          → (∀ x u → ≈ε A x u → ≈ε B (lv x) (lu u))
          → ∀ a u → ≈ε A a u
          → ≈ε B (recV n tv rv lv a) (recV n tu ru lu u)
  rec-rel A B zero    tv tu rv ru lv lu ht hr hl a u rel = hl a u rel
  rec-rel A B (suc n) tv tu rv ru lv lu ht hr hl a u rel
    with tv a | tu u | ht a u rel
  ... | inj₁ _ | .(inj₁ _) | refl = hl a u rel
  ... | inj₂ _ | .(inj₂ _) | refl =
    hr (λ y → recV n tv rv lv y) (λ y → recV n tu ru lu y) a u
       (λ y uy rely → rec-rel A B n tv tu rv ru lv lu ht hr hl y uy rely)
       rel

-- FACTORIZATION, fundamental lemma: the value semantics respects erasure
-- up to the relation.
ε-rel : {A B : Ty} (f : A ⇨ B) {a : ⟦ A ⟧T} {u : ⟦ strip A ⟧U}
      → ≈ε A a u → ≈ε B (⟦ f ⟧V a) (⟦ ε f ⟧VS u)
ε-rel idS rel = rel
ε-rel (g ∘S f) rel = ε-rel g (ε-rel f rel)
ε-rel (f ⊗S g) (ra , rc) = (ε-rel f ra , ε-rel g rc)
ε-rel swapS (ra , rb) = (rb , ra)
ε-rel assocS ((ra , rb) , rc) = (ra , (rb , rc))
ε-rel unassocS (ra , (rb , rc)) = ((ra , rb) , rc)
ε-rel exlS (ra , _) = ra
ε-rel exrS (_ , rb) = rb
ε-rel weakS _ = tt
ε-rel runitS rel = (rel , tt)
ε-rel lunitS rel = (tt , rel)
ε-rel inlS rel = rel
ε-rel inrS rel = rel
ε-rel (caseS l r) {inj₁ _} {inj₁ _} rel = ε-rel l rel
ε-rel (caseS l r) {inj₂ _} {inj₂ _} rel = ε-rel r rel
ε-rel (caseS l r) {inj₁ _} {inj₂ _} ()
ε-rel (caseS l r) {inj₂ _} {inj₁ _} ()
ε-rel distlS {_ , inj₁ _} {_ , inj₁ _} (ra , rb) = (ra , rb)
ε-rel distlS {_ , inj₂ _} {_ , inj₂ _} (ra , rc) = (ra , rc)
ε-rel distlS {_ , inj₁ _} {_ , inj₂ _} (ra , ())
ε-rel distlS {_ , inj₂ _} {_ , inj₁ _} (ra , ())
ε-rel nilS _ = []
ε-rel consS (rx , rxs) = rx ∷ rxs
ε-rel unconsS {[]} {[]} [] = tt
ε-rel unconsS {x ∷ xs} {u ∷ us} (r ∷ rs) = (r , rs)
ε-rel unconsS {[]} {_ ∷ _} ()
ε-rel unconsS {_ ∷ _} {[]} ()
ε-rel natOutS {zero}  refl = tt
ε-rel natOutS {suc k} refl = refl
ε-rel sucS refl = refl
ε-rel addS (refl , refl) = refl
ε-rel (constS k) _ = refl
ε-rel dupNatS refl = (refl , refl)
ε-rel (copyS _) rel = (rel , rel)
ε-rel (guardS {A} t) {a} {u} rel
  with ⟦ t ⟧V a | ⟦ ε t ⟧VS u
     | ≈ε-verdict (⟦ t ⟧V a) (⟦ ε t ⟧VS u) (ε-rel t rel)
... | inj₁ _ | .(inj₁ _) | refl = rel
... | inj₂ _ | .(inj₂ _) | refl = tt
ε-rel (curryS f) rel = λ a u relA → ε-rel f (rel , relA)
ε-rel applyS {gf , ga} {uf , ua} (relF , relA) = relF ga ua relA
ε-rel (mapCS {A} {B}) {f , xs} {uf , us} (relF , relXs) =
  map-rel A B f uf relF xs us relXs
ε-rel (iterCS {A}) {f , (n , a)} {uf , (un , ua)} (relF , (refl , relA)) =
  iter-rel A n f uf relF a ua relA
ε-rel (foldCS {A} {B}) {f , (xs , b)} {uf , (us , ub)}
  (relF , (relXs , relB)) =
  fold-rel A B f uf
    (λ b' ub' x ux rb rx → relF (b' , x) (ub' , ux) (rb , rx))
    xs us relXs b ub relB
ε-rel (whileCS {A}) {t , (s , (n , a))} {ut , (us , (un , ua))}
  (relT , (relS , (refl , relA))) =
  while-rel A n t ut s us
    (λ x u r → ≈ε-verdict (t x) (ut u) (relT x u r))
    relS a ua relA
ε-rel (promoteS _) rel = rel
ε-rel dupS rel = (rel , rel)
ε-rel (boxS f) rel = ε-rel f rel
ε-rel (boxValS f) rel = ε-rel f rel
ε-rel mergeS rel = rel
ε-rel (mapS {A} {B} f) {xs} {us} relXs =
  map-rel A B ⟦ f ⟧V ⟦ ε f ⟧VS (λ x u r → ε-rel f {x} {u} r) xs us relXs
ε-rel (iterS {A} f) {n , a} {un , ua} (refl , relA) =
  iter-rel A n ⟦ f ⟧V ⟦ ε f ⟧VS (λ x u r → ε-rel f {x} {u} r) a ua relA
ε-rel (foldS {A} {B} f) {xs , b} {us , ub} (relXs , relB) =
  fold-rel A B ⟦ f ⟧V ⟦ ε f ⟧VS
    (λ b' ub' x ux rb rx → ε-rel f {b' , x} {ub' , ux} (rb , rx))
    xs us relXs b ub relB
ε-rel (whileS {A} t s) {n , a} {un , ua} (refl , relA) =
  while-rel A n ⟦ t ⟧V ⟦ ε t ⟧VS ⟦ s ⟧V ⟦ ε s ⟧VS
    (λ x u r → ≈ε-verdict (⟦ t ⟧V x) (⟦ ε t ⟧VS u) (ε-rel t {x} {u} r))
    (λ x u r → ε-rel s {x} {u} r)
    a ua relA
ε-rel (recS {A} {B} t r l) {n , a} {un , ua} (refl , relA) =
  rec-rel A B n ⟦ t ⟧V ⟦ ε t ⟧VS ⟦ r ⟧V ⟦ ε r ⟧VS ⟦ l ⟧V ⟦ ε l ⟧VS
    (λ x u rx → ≈ε-verdict (⟦ t ⟧V x) (⟦ ε t ⟧VS u) (ε-rel t {x} {u} rx))
    (λ fv fu x u relF relX → ε-rel r {fv , x} {fu , u} (relF , relX))
    (λ x u rx → ε-rel l {x} {u} rx)
    a ua relA

-- First-order recovery: stripping IS the relation at arrow-free types.
≈ε-strip : (A : Ty) → fo A → (a : ⟦ A ⟧T) → ≈ε A a (stripV A a)
≈ε-strip unit      _          _        = tt
≈ε-strip nat       _          _        = refl
≈ε-strip (A ⊗ B)   (fa , fb)  (a , b)  = (≈ε-strip A fa a , ≈ε-strip B fb b)
≈ε-strip (A ⊕ B)   (fa , _)   (inj₁ a) = ≈ε-strip A fa a
≈ε-strip (A ⊕ B)   (_ , fb)   (inj₂ b) = ≈ε-strip B fb b
≈ε-strip (listT A) fa         []       = []
≈ε-strip (listT A) fa         (x ∷ xs) =
  ≈ε-strip A fa x ∷ ≈ε-strip (listT A) fa xs
≈ε-strip (! A)     fa         a        = ≈ε-strip A fa a

≈ε-eq : (A : Ty) → fo A → {a : ⟦ A ⟧T} {u : ⟦ strip A ⟧U}
      → ≈ε A a u → stripV A a ≡ u
≈ε-eq unit      _         {tt}     {tt}     _   = refl
≈ε-eq nat       _         rel = rel
≈ε-eq (A ⊗ B)   (fa , fb) (ra , rb) = cong₂ _,_ (≈ε-eq A fa ra) (≈ε-eq B fb rb)
≈ε-eq (A ⊕ B)   (fa , _)  {inj₁ _} {inj₁ _} r = cong inj₁ (≈ε-eq A fa r)
≈ε-eq (A ⊕ B)   (_ , fb)  {inj₂ _} {inj₂ _} r = cong inj₂ (≈ε-eq B fb r)
≈ε-eq (A ⊕ B)   _         {inj₁ _} {inj₂ _} ()
≈ε-eq (A ⊕ B)   _         {inj₂ _} {inj₁ _} ()
≈ε-eq (listT A) fa        {[]}     {[]}     [] = refl
≈ε-eq (listT A) fa        {_ ∷ _}  {_ ∷ _}  (r ∷ rs) =
  cong₂ _∷_ (≈ε-eq A fa r) (≈ε-eq (listT A) fa rs)
≈ε-eq (! A)     fa        rel = ≈ε-eq A fa rel

-- FACTORIZATION at first-order endpoints: the original propositional
-- statement, now gated by fo evidence (tt-tuples at concrete types).
ε-factor : {A B : Ty} → fo A → fo B → (f : A ⇨ B) (a : ⟦ A ⟧T)
         → stripV B (⟦ f ⟧V a) ≡ ⟦ ε f ⟧VS (stripV A a)
ε-factor {A} {B} foA foB f a = ≈ε-eq B foB (ε-rel f (≈ε-strip A foA a))

-- ────────────────────────────────────────────────────────────────────────────
-- § 2  Placement: skeletons, decorations, the least solution
-- ────────────────────────────────────────────────────────────────────────────

-- Recursion skeleton: what erasure leaves of the level structure.
-- `call k` is the parameter-offset edge (an argument used k levels below
-- its call site) — produced by the definition/call layer of real
-- programs (Telomare.Infer mirrors it); the categorical fragment below
-- emits only tip/bin/rec.
data Skel : Set where
  tip  : Skel
  bin  : Skel → Skel → Skel
  rec  : Skel → Skel
  call : ℕ → Skel → Skel

-- A decoration: one ℕ per recursion site.
data Deco : Skel → Set where
  tipD  : Deco tip
  binD  : {s₁ s₂ : Skel} → Deco s₁ → Deco s₂ → Deco (bin s₁ s₂)
  recD  : {s : Skel} → ℕ → Deco s → Deco (rec s)
  callD : {k : ℕ} {s : Skel} → Deco s → Deco (call k s)

-- Stratification at ambient depth d: a site sits at ≥ its ambient depth;
-- its contents run one level deeper; a call argument is pulled k deeper.
Solves : ℕ → {s : Skel} → Deco s → Set
Solves d tipD          = ⊤
Solves d (binD x y)    = Solves d x × Solves d y
Solves d (recD ℓ x)    = (d ≤ ℓ) × Solves (suc ℓ) x
Solves d (callD {k} x) = Solves (d + k) x

solves-anti : {d′ d : ℕ} {s : Skel} (x : Deco s)
            → d′ ≤ d → Solves d x → Solves d′ x
solves-anti tipD          h _         = tt
solves-anti (binD x y)    h (sx , sy) = (solves-anti x h sx , solves-anti y h sy)
solves-anti (recD ℓ x)    h (dℓ , sx) = (≤-trans h dℓ , sx)
solves-anti (callD {k} x) h sx        = solves-anti x (+-monoˡ-≤ k h) sx

-- Pointwise meet of two decorations of the same skeleton.
meet : {s : Skel} → Deco s → Deco s → Deco s
meet tipD        tipD        = tipD
meet (binD x y)  (binD u v)  = binD (meet x u) (meet y v)
meet (recD ℓ x)  (recD ℓ′ y) = recD (ℓ ⊓ ℓ′) (meet x y)
meet (callD x)   (callD y)   = callD (meet x y)

-- MEET-CLOSURE: the solution set is closed under pointwise ⊓ — this is
-- why the least decoration exists whenever any does (difference
-- constraints are min-closed).
solves-meet : {dx dy : ℕ} {s : Skel} (x y : Deco s)
            → Solves dx x → Solves dy y → Solves (dx ⊓ dy) (meet x y)
solves-meet tipD        tipD        _ _ = tt
solves-meet (binD x y)  (binD u v)  (sx , sy) (su , sv) =
  (solves-meet x u sx su , solves-meet y v sy sv)
solves-meet (recD ℓ x)  (recD ℓ′ y) (dℓ , sx) (dℓ′ , sy) =
  (⊓-mono-≤ dℓ dℓ′ , solves-meet x y sx sy)
solves-meet {dx} {dy} (callD {k} x) (callD y) sx sy =
  solves-anti (meet x y)
              (⊓-glb (+-monoˡ-≤ k (m⊓n≤m dx dy))
                     (+-monoˡ-≤ k (m⊓n≤n dx dy)))
              (solves-meet x y sx sy)

solves-meet-same : {d : ℕ} {s : Skel} (x y : Deco s)
                 → Solves d x → Solves d y → Solves d (meet x y)
solves-meet-same {d} x y sx sy =
  subst (λ e → Solves e (meet x y)) (⊓-idem d) (solves-meet x y sx sy)

-- The structural algorithm (the Levels.hs recipe): one walk, no search —
-- assign every site its ambient depth.
place : (d : ℕ) (s : Skel) → Deco s
place d tip        = tipD
place d (bin x y)  = binD (place d x) (place d y)
place d (rec s)    = recD d (place (suc d) s)
place d (call k s) = callD (place (d + k) s)

place-solves : (d : ℕ) (s : Skel) → Solves d (place d s)
place-solves d tip        = tt
place-solves d (bin x y)  = (place-solves d x , place-solves d y)
place-solves d (rec s)    = (≤-refl , place-solves (suc d) s)
place-solves d (call k s) = place-solves (d + k) s

-- Pointwise order on decorations.
infix 4 _⊑_
data _⊑_ : {s : Skel} → Deco s → Deco s → Set where
  tip⊑  : tipD ⊑ tipD
  bin⊑  : {s₁ s₂ : Skel} {x₁ y₁ : Deco s₁} {x₂ y₂ : Deco s₂}
        → x₁ ⊑ y₁ → x₂ ⊑ y₂ → binD x₁ x₂ ⊑ binD y₁ y₂
  rec⊑  : {s : Skel} {ℓ ℓ′ : ℕ} {x y : Deco s}
        → ℓ ≤ ℓ′ → x ⊑ y → recD ℓ x ⊑ recD ℓ′ y
  call⊑ : {k : ℕ} {s : Skel} {x y : Deco s}
        → x ⊑ y → callD {k} x ⊑ callD y

-- THE UNIVERSAL PROPERTY: the structural walk computes the LEAST
-- solution.  Every decoration that stratifies dominates it.
place-least : (d : ℕ) {s : Skel} (y : Deco s)
            → Solves d y → place d s ⊑ y
place-least d tipD        _         = tip⊑
place-least d (binD y₁ y₂) (s₁ , s₂) =
  bin⊑ (place-least d y₁ s₁) (place-least d y₂ s₂)
place-least d (recD ℓ y)  (dℓ , sy) =
  rec⊑ dℓ (place-least (suc d) y (solves-anti y (s≤s dℓ) sy))
place-least d (callD {k} y) sy = call⊑ (place-least (d + k) y sy)

-- ────────────────────────────────────────────────────────────────────────────
-- § 3  The bridge: typed core terms are solutions above the placement
-- ────────────────────────────────────────────────────────────────────────────

-- The recursion skeleton of a surface term.
skelOf : {A B : UTy} → A ⇨U B → Skel
skelOf idU          = tip
skelOf (g ∘U f)     = bin (skelOf g) (skelOf f)
skelOf (f ⊗U g)     = bin (skelOf f) (skelOf g)
skelOf dupU         = tip
skelOf swapU        = tip
skelOf assocU       = tip
skelOf unassocU     = tip
skelOf exlU         = tip
skelOf exrU         = tip
skelOf weakU        = tip
skelOf runitU       = tip
skelOf lunitU       = tip
skelOf inlU         = tip
skelOf inrU         = tip
skelOf (caseU l r)  = bin (skelOf l) (skelOf r)
skelOf distlU       = tip
skelOf nilU         = tip
skelOf consU        = tip
skelOf unconsU      = tip
skelOf natOutU      = tip
skelOf sucU         = tip
skelOf addU         = tip
skelOf (constU _)   = tip
skelOf (curryU f)   = skelOf f
skelOf applyU       = tip
skelOf mapCU        = rec tip
skelOf iterCU       = rec tip
skelOf foldCU       = rec tip
skelOf whileCU      = rec tip
skelOf (guardU t)   = skelOf t
skelOf (mapU f)     = rec (skelOf f)
skelOf (iterU f)    = rec (skelOf f)
skelOf (foldU f)    = rec (skelOf f)
skelOf (whileU t s) = rec (bin (skelOf t) (skelOf s))
skelOf (recU t r l) = rec (bin (skelOf t) (bin (skelOf r) (skelOf l)))

-- Read a core term's level structure off its box/loop nesting: the
-- decoration a typed decoration ACTUALLY carries, at ambient depth d.
-- Boxes shift the ambient depth without adding a site (their shape
-- erases), which is exactly why the fiber over one skeleton contains
-- decorations at many levels.
skelOfCore : {A B : Ty} (f : A ⇨ B) (d : ℕ) → Deco (skelOf (ε f))
skelOfCore idS          d = tipD
skelOfCore (g ∘S f)     d = binD (skelOfCore g d) (skelOfCore f d)
skelOfCore (f ⊗S g)     d = binD (skelOfCore f d) (skelOfCore g d)
skelOfCore swapS        d = tipD
skelOfCore assocS       d = tipD
skelOfCore unassocS     d = tipD
skelOfCore exlS         d = tipD
skelOfCore exrS         d = tipD
skelOfCore weakS        d = tipD
skelOfCore runitS       d = tipD
skelOfCore lunitS       d = tipD
skelOfCore inlS         d = tipD
skelOfCore inrS         d = tipD
skelOfCore (caseS l r)  d = binD (skelOfCore l d) (skelOfCore r d)
skelOfCore distlS       d = tipD
skelOfCore nilS         d = tipD
skelOfCore consS        d = tipD
skelOfCore unconsS      d = tipD
skelOfCore natOutS      d = tipD
skelOfCore sucS         d = tipD
skelOfCore addS         d = tipD
skelOfCore (constS _)   d = tipD
skelOfCore dupNatS      d = tipD
skelOfCore (copyS _)    d = tipD
skelOfCore (curryS f)   d = skelOfCore f d
skelOfCore applyS       d = tipD
skelOfCore mapCS        d = recD d tipD
skelOfCore iterCS       d = recD d tipD
skelOfCore foldCS       d = recD d tipD
skelOfCore whileCS      d = recD d tipD
skelOfCore (guardS t)   d = skelOfCore t d
skelOfCore (promoteS _) d = tipD
skelOfCore dupS         d = tipD
skelOfCore (boxS f)     d = skelOfCore f (suc d)
skelOfCore (boxValS f)  d = skelOfCore f (suc d)
skelOfCore mergeS       d = tipD
skelOfCore (mapS f)     d = recD d (skelOfCore f (suc d))
skelOfCore (iterS f)    d = recD d (skelOfCore f (suc d))
skelOfCore (foldS f)    d = recD d (skelOfCore f (suc d))
skelOfCore (whileS t s) d =
  recD d (binD (skelOfCore t (suc d)) (skelOfCore s (suc d)))
skelOfCore (recS t r l) d =
  recD d (binD (skelOfCore t (suc d))
            (binD (skelOfCore r (suc d)) (skelOfCore l (suc d))))

-- Well-typed core terms stratify: their level structure is a solution.
core-solves : {A B : Ty} (f : A ⇨ B) (d : ℕ) → Solves d (skelOfCore f d)
core-solves idS          d = tt
core-solves (g ∘S f)     d = (core-solves g d , core-solves f d)
core-solves (f ⊗S g)     d = (core-solves f d , core-solves g d)
core-solves swapS        d = tt
core-solves assocS       d = tt
core-solves unassocS     d = tt
core-solves exlS         d = tt
core-solves exrS         d = tt
core-solves weakS        d = tt
core-solves runitS       d = tt
core-solves lunitS       d = tt
core-solves inlS         d = tt
core-solves inrS         d = tt
core-solves (caseS l r)  d = (core-solves l d , core-solves r d)
core-solves distlS       d = tt
core-solves nilS         d = tt
core-solves consS        d = tt
core-solves unconsS      d = tt
core-solves natOutS      d = tt
core-solves sucS         d = tt
core-solves addS         d = tt
core-solves (constS _)   d = tt
core-solves dupNatS      d = tt
core-solves (copyS _)    d = tt
core-solves (curryS f)   d = core-solves f d
core-solves applyS       d = tt
core-solves mapCS        d = (≤-refl , tt)
core-solves iterCS       d = (≤-refl , tt)
core-solves foldCS       d = (≤-refl , tt)
core-solves whileCS      d = (≤-refl , tt)
core-solves (guardS t)   d = core-solves t d
core-solves (promoteS _) d = tt
core-solves dupS         d = tt
core-solves (boxS f)     d =
  solves-anti (skelOfCore f (suc d)) (n≤1+n d) (core-solves f (suc d))
core-solves (boxValS f)  d =
  solves-anti (skelOfCore f (suc d)) (n≤1+n d) (core-solves f (suc d))
core-solves mergeS       d = tt
core-solves (mapS f)     d = (≤-refl , core-solves f (suc d))
core-solves (iterS f)    d = (≤-refl , core-solves f (suc d))
core-solves (foldS f)    d = (≤-refl , core-solves f (suc d))
core-solves (whileS t s) d =
  (≤-refl , (core-solves t (suc d) , core-solves s (suc d)))
core-solves (recS t r l) d =
  (≤-refl , (core-solves t (suc d)
    , (core-solves r (suc d) , core-solves l (suc d))))

-- THE GALOIS-INSERTION CONTENT: the structural placement of a core
-- term's erasure is a lower bound on the term's own level structure.
-- "The least boxing" is not a heuristic; it is beneath every typing.
core-dominates : {A B : Ty} (f : A ⇨ B) (d : ℕ)
               → place d (skelOf (ε f)) ⊑ skelOfCore f d
core-dominates f d = place-least d (skelOfCore f d) (core-solves f d)

-- ────────────────────────────────────────────────────────────────────────────
-- § 4  Same-level feedback is unstratifiable
-- ────────────────────────────────────────────────────────────────────────────

-- The λn. n n shape — an iteration whose step is built by iteration at
-- the SAME level — elaborates (in the higher-order surface, M6) to the
-- level constraint ℓ ≥ ℓ + 1, which has no solution: the program is
-- unstratifiable and is routed to Tier 2 with an iteration-level notice,
-- never rejected.  In this first-order core the pattern is unwritable by
-- construction (iterS takes its step as syntax; !A is not a morphism).
sameLevelFeedback-unsat : {ℓ : ℕ} → ¬ (suc ℓ ≤ ℓ)
sameLevelFeedback-unsat = 1+n≰n
