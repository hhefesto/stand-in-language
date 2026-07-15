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
open import Data.Product         using (_×_; _,_)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Unit            using (⊤; tt)
open import Data.List            using (List; []; _∷_)
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
ε (guardS t)   = guardU (ε t)
ε dupS         = dupU          -- contraction erases to free dup
ε (boxS f)     = ε f           -- boxes erase
ε (boxValS f)  = ε f
ε mergeS       = idU
ε (mapS f)     = mapU (ε f)
ε (iterS f)    = iterU (ε f)
ε (foldS f)    = foldU (ε f)
ε (whileS t s) = whileU (ε t) (ε s)

private
  guard-strip : (A : Ty) (a : ⟦ A ⟧T) (r : ⊤ ⊎ ⊤)
              → stripV (A ⊕ unit) (guardV a r) ≡ guardV (stripV A a) r
  guard-strip A a (inj₁ tt) = refl
  guard-strip A a (inj₂ tt) = refl

  map-strip : (A B : Ty) (xs : List ⟦ A ⟧T)
              (fv : ⟦ A ⟧T → ⟦ B ⟧T)
              (fu : ⟦ strip A ⟧U → ⟦ strip B ⟧U)
            → (∀ x → stripV B (fv x) ≡ fu (stripV A x))
            → stripV (listT B) (mapV fv xs)
              ≡ mapV fu (stripV (listT A) xs)
  map-strip A B []       fv fu h = refl
  map-strip A B (x ∷ xs) fv fu h =
    cong₂ _∷_ (h x) (map-strip A B xs fv fu h)

  iter-strip : (A : Ty) (n : ℕ)
               (fv : ⟦ A ⟧T → ⟦ A ⟧T) (fu : ⟦ strip A ⟧U → ⟦ strip A ⟧U)
             → (∀ x → stripV A (fv x) ≡ fu (stripV A x))
             → ∀ a → stripV A (iterV n fv a) ≡ iterV n fu (stripV A a)
  iter-strip A zero    fv fu h a = refl
  iter-strip A (suc n) fv fu h a =
    trans (iter-strip A n fv fu h (fv a)) (cong (iterV n fu) (h a))

  fold-strip : (A B : Ty) (xs : List ⟦ A ⟧T)
               (fv : ⟦ B ⟧T × ⟦ A ⟧T → ⟦ B ⟧T)
               (fu : ⟦ strip B ⟧U × ⟦ strip A ⟧U → ⟦ strip B ⟧U)
             → (∀ b x → stripV B (fv (b , x)) ≡ fu (stripV B b , stripV A x))
             → ∀ b → stripV B (foldV xs fv b)
                     ≡ foldV (stripV (listT A) xs) fu (stripV B b)
  fold-strip A B []       fv fu h b = refl
  fold-strip A B (x ∷ xs) fv fu h b =
    trans (fold-strip A B xs fv fu h (fv (b , x)))
          (cong (foldV (stripV (listT A) xs) fu) (h b x))

  whileGo-strip : (A : Ty) (n : ℕ)
                  (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤) (tu : ⟦ strip A ⟧U → ⊤ ⊎ ⊤)
                  (sv : ⟦ A ⟧T → ⟦ A ⟧T) (su : ⟦ strip A ⟧U → ⟦ strip A ⟧U)
                → (∀ x → tv x ≡ tu (stripV A x))
                → (∀ x → stripV A (sv x) ≡ su (stripV A x))
                → ∀ a r → stripV A (whileV-go n tv sv a r)
                          ≡ whileV-go n tu su (stripV A a) r
  while-strip   : (A : Ty) (n : ℕ)
                  (tv : ⟦ A ⟧T → ⊤ ⊎ ⊤) (tu : ⟦ strip A ⟧U → ⊤ ⊎ ⊤)
                  (sv : ⟦ A ⟧T → ⟦ A ⟧T) (su : ⟦ strip A ⟧U → ⟦ strip A ⟧U)
                → (∀ x → tv x ≡ tu (stripV A x))
                → (∀ x → stripV A (sv x) ≡ su (stripV A x))
                → ∀ a → stripV A (whileV n tv sv a)
                        ≡ whileV n tu su (stripV A a)

  whileGo-strip A n tv tu sv su ht hs a (inj₁ _) = refl
  whileGo-strip A n tv tu sv su ht hs a (inj₂ _) =
    trans (while-strip A n tv tu sv su ht hs (sv a))
          (cong (whileV n tu su) (hs a))

  while-strip A zero    tv tu sv su ht hs a = refl
  while-strip A (suc n) tv tu sv su ht hs a =
    trans (whileGo-strip A n tv tu sv su ht hs a (tv a))
          (cong (whileV-go n tu su (stripV A a)) (ht a))

-- FACTORIZATION: the value semantics factors through erasure.
ε-factor : {A B : Ty} (f : A ⇨ B) (a : ⟦ A ⟧T)
         → stripV B (⟦ f ⟧V a) ≡ ⟦ ε f ⟧VS (stripV A a)
ε-factor idS a = refl
ε-factor (_∘S_ {A} {B} {C} g f) a =
  trans (ε-factor g (⟦ f ⟧V a)) (cong ⟦ ε g ⟧VS (ε-factor f a))
ε-factor (f ⊗S g) (a , c) = cong₂ _,_ (ε-factor f a) (ε-factor g c)
ε-factor swapS (a , b) = refl
ε-factor assocS ((a , b) , c) = refl
ε-factor unassocS (a , (b , c)) = refl
ε-factor exlS (a , _) = refl
ε-factor exrS (_ , b) = refl
ε-factor weakS a = refl
ε-factor runitS a = refl
ε-factor lunitS a = refl
ε-factor inlS a = refl
ε-factor inrS b = refl
ε-factor (caseS l r) (inj₁ a) = ε-factor l a
ε-factor (caseS l r) (inj₂ b) = ε-factor r b
ε-factor distlS (a , inj₁ b) = refl
ε-factor distlS (a , inj₂ c) = refl
ε-factor nilS a = refl
ε-factor consS (x , xs) = refl
ε-factor unconsS [] = refl
ε-factor unconsS (x ∷ xs) = refl
ε-factor natOutS zero = refl
ε-factor natOutS (suc n) = refl
ε-factor sucS n = refl
ε-factor addS (a , b) = refl
ε-factor (constS k) a = refl
ε-factor dupNatS n = refl
ε-factor (guardS {A} t) a =
  trans (guard-strip A a (⟦ t ⟧V a))
        (cong (guardV (stripV A a))
              (trans (sym (strip2 (⟦ t ⟧V a))) (ε-factor t a)))
ε-factor dupS a = refl
ε-factor (boxS f) a = ε-factor f a
ε-factor (boxValS f) a = ε-factor f a
ε-factor mergeS (a , b) = refl
ε-factor (mapS {A} {B} f) xs =
  map-strip A B xs ⟦ f ⟧V ⟦ ε f ⟧VS (ε-factor f)
ε-factor (iterS {A} f) (n , a) =
  iter-strip A n ⟦ f ⟧V ⟦ ε f ⟧VS (ε-factor f) a
ε-factor (foldS {A} {B} f) (xs , b) =
  fold-strip A B xs ⟦ f ⟧V ⟦ ε f ⟧VS (λ x y → ε-factor f (x , y)) b
ε-factor (whileS {A} t s) (n , a) =
  while-strip A n ⟦ t ⟧V ⟦ ε t ⟧VS ⟦ s ⟧V ⟦ ε s ⟧VS
    (λ x → trans (sym (strip2 (⟦ t ⟧V x))) (ε-factor t x))
    (ε-factor s) a

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
skelOf (guardU t)   = skelOf t
skelOf (mapU f)     = rec (skelOf f)
skelOf (iterU f)    = rec (skelOf f)
skelOf (foldU f)    = rec (skelOf f)
skelOf (whileU t s) = rec (bin (skelOf t) (skelOf s))

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
skelOfCore (guardS t)   d = skelOfCore t d
skelOfCore dupS         d = tipD
skelOfCore (boxS f)     d = skelOfCore f (suc d)
skelOfCore (boxValS f)  d = skelOfCore f (suc d)
skelOfCore mergeS       d = tipD
skelOfCore (mapS f)     d = recD d (skelOfCore f (suc d))
skelOfCore (iterS f)    d = recD d (skelOfCore f (suc d))
skelOfCore (foldS f)    d = recD d (skelOfCore f (suc d))
skelOfCore (whileS t s) d =
  recD d (binD (skelOfCore t (suc d)) (skelOfCore s (suc d)))

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
core-solves (guardS t)   d = core-solves t d
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
