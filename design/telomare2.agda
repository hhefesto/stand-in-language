-- Telomare 2 — core-category skeleton
-- Companion to design/TELOMARE2-DESIGN.md.
--
-- An AFFINE, distributive, bicartesian monoidal syntax category with an
-- Elementary-Affine-Logic exponential (contraction + promotion ONLY — no
-- dereliction, no digging) and fuel-carrying recursion, interpreted by:
--   ⟦_⟧V  value      (the specification: a plain total function)
--   ⟦_⟧C  work/tel   (Writer ℕ, +)          — with adequacy, PROVED
--   ⟦_⟧D  dup grade  (Writer ℕ, +)          — sizeT-weighted copy count;
--                                              zero on all affine code
--   ⟦_⟧SP space      ((⊔,+) peak live size)
--   ⟦_⟧K  execution  (TelM = StateT ℕ Maybe) — fuel-metered
--
-- Proof technique (precision-with-slack ⇒ adequacy) is taken verbatim from
-- the agda branch's telomare.agda §8e/§9.
--
-- Imported metatheory, CITED not proved (see design doc §6):
--  • EAL normalizes in elementary time; tower height = box depth
--    [Girard, Light Linear Logic; Danos–Joinet, LL and Elementary Time]
--  • EAL-typable terms reduce Lévy-optimally on sharing graphs with fans
--    labeled by static box depth — no oracle
--    [Asperti; Coppola–Martini]
-- Both are corollaries of stratification: absent dereliction/digging, no
-- reduction crosses a box boundary, so depth is fixed before running.

{-# OPTIONS --safe #-}
module telomare2 where

open import Data.Nat             using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Maybe           using (Maybe; just; nothing; _>>=_)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_)
open import Data.Unit            using (⊤; tt)
open import Relation.Binary.PropositionalEquality
                                 using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat.Properties  using (+-assoc; +-identityʳ)

-- ────────────────────────────────────────────────────────────────────────────
-- § 1  Semantic models (Denotational Design: models first)
-- ────────────────────────────────────────────────────────────────────────────

Tel : Set
Tel = ℕ

-- Execution: may halt when fuel runs out (never diverges).
TelM : Set → Set
TelM A = Tel → Maybe (A × Tel)

return-tel : {A : Set} → A → TelM A
return-tel a g = just (a , g)

bind-tel : {A B : Set} → TelM A → (A → TelM B) → TelM B
bind-tel m f g = m g >>= λ { (a , g') → f a g' }

step-tel : {A : Set} → TelM A → TelM A
step-tel m zero    = nothing
step-tel m (suc g) = m g

-- Grading: Writer ℕ.  Used twice, with different charging policies:
-- work (⟦_⟧C) and duplication (⟦_⟧D).
CostM : Set → Set
CostM A = ℕ × A

return-cost : {A : Set} → A → CostM A
return-cost a = (0 , a)

bind-cost : {A B : Set} → CostM A → (A → CostM B) → CostM B
bind-cost (n , a) f = let (m , b) = f a in (n + m , b)

step-cost : {A : Set} → CostM A → CostM A
step-cost (n , a) = (suc n , a)

infixr 0 _→K_ _→C_
_→K_ : Set → Set → Set
A →K B = A → TelM B
_→C_ : Set → Set → Set
A →C B = A → CostM B

-- ────────────────────────────────────────────────────────────────────────────
-- § 2  Objects
-- ────────────────────────────────────────────────────────────────────────────

data Ty : Set where
  unit  : Ty
  nat   : Ty
  _⊗_   : Ty → Ty → Ty
  _⊕_   : Ty → Ty → Ty
  listT : Ty → Ty
  !_    : Ty → Ty            -- the EAL exponential

infixl 5 _⊗_
infixl 4 _⊕_
infixr 6 !_

-- Values do not see boxes: ⟦!A⟧ = ⟦A⟧.  The modality is cost/discipline-
-- relevant, value-irrelevant (the design's TCM moment).
⟦_⟧T : Ty → Set
⟦ unit    ⟧T = ⊤
⟦ nat     ⟧T = ℕ
⟦ A ⊗ B   ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A ⊕ B   ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ listT A ⟧T = List ⟦ A ⟧T
⟦ ! A     ⟧T = ⟦ A ⟧T

-- Word model of value size (for space and the dup grade).
sizeT : (A : Ty) → ⟦ A ⟧T → ℕ
sizeT unit      _        = 1
sizeT nat       _        = 1
sizeT (A ⊗ B)   (a , b)  = sizeT A a + sizeT B b
sizeT (A ⊕ B)   (inj₁ a) = suc (sizeT A a)
sizeT (A ⊕ B)   (inj₂ b) = suc (sizeT B b)
sizeT (listT A) []       = 1
sizeT (listT A) (x ∷ xs) = suc (sizeT A x + sizeT (listT A) xs)
sizeT (! A)     a        = sizeT A a

-- ────────────────────────────────────────────────────────────────────────────
-- § 3  Morphisms: the core category
-- ────────────────────────────────────────────────────────────────────────────
--
-- Affine: weakening (weakS, exlS, exrS) is free.  There is NO fork and NO
-- dup on ordinary objects — contraction exists only at !A (dupS) and, as a
-- measured-justified exemption, at machine atoms (dupNatS: HVM2 duplicates a
-- scalar in one interaction; an atom contains no redexes so copying it
-- cannot disturb sharing).
--
-- The EAL exponential is dupS/boxS/boxValS/mergeS and NOTHING ELSE:
--   der : !A ⇨ A   and   dig : !A ⇨ !!A   deliberately DO NOT EXIST.
-- Their absence is what fixes box depth before reduction (design doc §6).

infixr 2 _⇨_
infixr 9 _∘S_

data _⇨_ : Ty → Ty → Set where
  -- category
  idS    : {A : Ty} → A ⇨ A
  _∘S_   : {A B C : Ty} → B ⇨ C → A ⇨ B → A ⇨ C
  -- affine symmetric monoidal
  _⊗S_   : {A B C D : Ty} → A ⇨ B → C ⇨ D → (A ⊗ C) ⇨ (B ⊗ D)
  swapS  : {A B : Ty} → (A ⊗ B) ⇨ (B ⊗ A)
  exlS   : {A B : Ty} → (A ⊗ B) ⇨ A          -- weakening on the right
  exrS   : {A B : Ty} → (A ⊗ B) ⇨ B          -- weakening on the left
  weakS  : {A : Ty} → A ⇨ unit               -- weakening
  runitS : {A : Ty} → A ⇨ (A ⊗ unit)         -- unit introduction
  -- coproducts + distributivity
  inlS   : {A B : Ty} → A ⇨ (A ⊕ B)
  inrS   : {A B : Ty} → B ⇨ (A ⊕ B)
  caseS  : {A B C : Ty} → A ⇨ C → B ⇨ C → (A ⊕ B) ⇨ C
  distlS : {A B C : Ty} → (A ⊗ (B ⊕ C)) ⇨ ((A ⊗ B) ⊕ (A ⊗ C))
  -- data: lists, naturals
  nilS    : {A : Ty} → unit ⇨ listT A
  consS   : {A : Ty} → (A ⊗ listT A) ⇨ listT A
  unconsS : {A : Ty} → listT A ⇨ (unit ⊕ (A ⊗ listT A))
  natOutS : nat ⇨ (unit ⊕ nat)               -- costs 1 tel (a real look)
  sucS    : nat ⇨ nat
  addS    : (nat ⊗ nat) ⇨ nat
  constS  : {A : Ty} → ℕ → A ⇨ nat
  dupNatS : nat ⇨ (nat ⊗ nat)                -- atom exemption (dup grade 1)
  -- EAL exponential — the ENTIRE duplication interface
  dupS    : {A : Ty} → ! A ⇨ (! A ⊗ ! A)     -- contraction, only at !
  boxS    : {A B : Ty} → A ⇨ B → (! A ⇨ ! B) -- promotion (functoriality)
  boxValS : {B : Ty} → unit ⇨ B → (unit ⇨ ! B)
    -- promotion with EMPTY context: only CLOSED values may be boxed at
    -- their own level.  (A general A ⇨ !A would smuggle contraction:
    -- dupS ∘ boxVal would copy an unboxed open input.)
  mergeS  : {A B : Ty} → (! A ⊗ ! B) ⇨ ! (A ⊗ B)
  -- fuel-carrying recursion: the output lives ONE LEVEL DEEPER than the
  -- orchestration (design doc §7).  Fuel is data; totality is manifest.
  iterS   : {A : Ty} → A ⇨ A → (nat ⊗ ! A) ⇨ ! A
  foldS   : {A B : Ty} → (B ⊗ A) ⇨ B → (listT A ⊗ ! B) ⇨ ! B
    -- NB the pragmatic typing: elements are consumed affinely from the
    -- orchestration level; the faithful story stratifies the list itself
    -- (design doc §14.1).

-- Box depth: the static number whose fixedness is both theorems.
-- iterS/foldS bodies run one level down, hence the suc.
depth : {A B : Ty} → A ⇨ B → ℕ
depth idS         = 0
depth (g ∘S f)    = depth g ⊔ depth f
depth (f ⊗S g)    = depth f ⊔ depth g
depth swapS       = 0
depth exlS        = 0
depth exrS        = 0
depth weakS       = 0
depth runitS      = 0
depth inlS        = 0
depth inrS        = 0
depth (caseS l r) = depth l ⊔ depth r
depth distlS      = 0
depth nilS        = 0
depth consS       = 0
depth unconsS     = 0
depth natOutS     = 0
depth sucS        = 0
depth addS        = 0
depth (constS _)  = 0
depth dupNatS     = 0
depth dupS        = 0
depth (boxS f)    = suc (depth f)
depth (boxValS f) = suc (depth f)
depth mergeS      = 0
depth (iterS f)   = suc (depth f)
depth (foldS f)   = suc (depth f)

-- towerHeight: the coarse, honest cost report ("worst case is a
-- depth-high tower in the size of the level-0 data") [cited].
towerHeight : {A B : Ty} → A ⇨ B → ℕ
towerHeight = depth

-- ────────────────────────────────────────────────────────────────────────────
-- § 4  Value denotation (the specification)
-- ────────────────────────────────────────────────────────────────────────────

private
  iterV : {A : Set} → ℕ → (A → A) → A → A
  iterV zero    f a = a
  iterV (suc n) f a = iterV n f (f a)

  foldV : {A B : Set} → List A → (B × A → B) → B → B
  foldV []       f b = b
  foldV (x ∷ xs) f b = foldV xs f (f (b , x))

⟦_⟧V : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ⟦ B ⟧T
⟦ idS       ⟧V a = a
⟦ g ∘S f    ⟧V a = ⟦ g ⟧V (⟦ f ⟧V a)
⟦ f ⊗S g    ⟧V (a , c) = (⟦ f ⟧V a , ⟦ g ⟧V c)
⟦ swapS     ⟧V (a , b) = (b , a)
⟦ exlS      ⟧V (a , _) = a
⟦ exrS      ⟧V (_ , b) = b
⟦ weakS     ⟧V _ = tt
⟦ runitS    ⟧V a = (a , tt)
⟦ inlS      ⟧V a = inj₁ a
⟦ inrS      ⟧V b = inj₂ b
⟦ caseS l r ⟧V (inj₁ a) = ⟦ l ⟧V a
⟦ caseS l r ⟧V (inj₂ b) = ⟦ r ⟧V b
⟦ distlS    ⟧V (a , inj₁ b) = inj₁ (a , b)
⟦ distlS    ⟧V (a , inj₂ c) = inj₂ (a , c)
⟦ nilS      ⟧V _ = []
⟦ consS     ⟧V (x , xs) = x ∷ xs
⟦ unconsS   ⟧V [] = inj₁ tt
⟦ unconsS   ⟧V (x ∷ xs) = inj₂ (x , xs)
⟦ natOutS   ⟧V zero = inj₁ tt
⟦ natOutS   ⟧V (suc n) = inj₂ n
⟦ sucS      ⟧V n = suc n
⟦ addS      ⟧V (a , b) = a + b
⟦ constS k  ⟧V _ = k
⟦ dupNatS   ⟧V n = (n , n)
⟦ dupS      ⟧V a = (a , a)          -- values don't see boxes
⟦ boxS f    ⟧V a = ⟦ f ⟧V a
⟦ boxValS f ⟧V a = ⟦ f ⟧V a
⟦ mergeS    ⟧V p = p
⟦ iterS f   ⟧V (n , a) = iterV n ⟦ f ⟧V a
⟦ foldS f   ⟧V (xs , b) = foldV xs ⟦ f ⟧V b

-- ────────────────────────────────────────────────────────────────────────────
-- § 5  Work (tel) denotation — Writer ℕ, charging 1 per natOut look and per
--      taken iter/fold step; boxes are free (their contents pay when run)
-- ────────────────────────────────────────────────────────────────────────────

private
  iterC-aux : {A : Set} → ℕ → (A →C A) → A →C A
  iterC-aux zero    _ a = return-cost a
  iterC-aux (suc n) f a = step-cost (bind-cost (f a) (iterC-aux n f))

  foldC-aux : {A B : Set} → List A → ((B × A) →C B) → B →C B
  foldC-aux []       _ b = return-cost b
  foldC-aux (x ∷ xs) f b = step-cost (bind-cost (f (b , x)) (foldC-aux xs f))

⟦_⟧C : {A B : Ty} → A ⇨ B → ⟦ A ⟧T →C ⟦ B ⟧T
⟦ idS       ⟧C a = return-cost a
⟦ g ∘S f    ⟧C a = bind-cost (⟦ f ⟧C a) ⟦ g ⟧C
⟦ f ⊗S g    ⟧C (a , c) =
  let (n , b) = ⟦ f ⟧C a
      (m , d) = ⟦ g ⟧C c
  in (n + m , (b , d))
⟦ swapS     ⟧C (a , b) = return-cost (b , a)
⟦ exlS      ⟧C (a , _) = return-cost a
⟦ exrS      ⟧C (_ , b) = return-cost b
⟦ weakS     ⟧C _ = return-cost tt
⟦ runitS    ⟧C a = return-cost (a , tt)
⟦ inlS      ⟧C a = return-cost (inj₁ a)
⟦ inrS      ⟧C b = return-cost (inj₂ b)
⟦ caseS l r ⟧C (inj₁ a) = ⟦ l ⟧C a
⟦ caseS l r ⟧C (inj₂ b) = ⟦ r ⟧C b
⟦ distlS    ⟧C (a , inj₁ b) = return-cost (inj₁ (a , b))
⟦ distlS    ⟧C (a , inj₂ c) = return-cost (inj₂ (a , c))
⟦ nilS      ⟧C _ = return-cost []
⟦ consS     ⟧C (x , xs) = return-cost (x ∷ xs)
⟦ unconsS   ⟧C [] = return-cost (inj₁ tt)
⟦ unconsS   ⟧C (x ∷ xs) = return-cost (inj₂ (x , xs))
⟦ natOutS   ⟧C zero = step-cost (return-cost (inj₁ tt))
⟦ natOutS   ⟧C (suc n) = step-cost (return-cost (inj₂ n))
⟦ sucS      ⟧C n = return-cost (suc n)
⟦ addS      ⟧C (a , b) = return-cost (a + b)
⟦ constS k  ⟧C _ = return-cost k
⟦ dupNatS   ⟧C n = return-cost (n , n)
⟦ dupS      ⟧C a = return-cost (a , a)
⟦ boxS f    ⟧C a = ⟦ f ⟧C a
⟦ boxValS f ⟧C a = ⟦ f ⟧C a
⟦ mergeS    ⟧C p = return-cost p
⟦ iterS f   ⟧C (n , a) = iterC-aux n ⟦ f ⟧C a
⟦ foldS f   ⟧C (xs , b) = foldC-aux xs ⟦ f ⟧C b

-- ────────────────────────────────────────────────────────────────────────────
-- § 6  Dup grade — the functor the bend-port experiments proved was missing.
--      Zero on ALL affine code; charges sizeT at dupS, 1 at dupNatS.
--      (work + 45·(work) ITRS/tel dup-free [measured] and this grade give a
--      wall-clock predictor for the interaction-net backend.)
-- ────────────────────────────────────────────────────────────────────────────

private
  iterD-aux : {A : Set} → ℕ → (A →C A) → A →C A
  iterD-aux zero    _ a = return-cost a
  iterD-aux (suc n) f a = bind-cost (f a) (iterD-aux n f)

  foldD-aux : {A B : Set} → List A → ((B × A) →C B) → B →C B
  foldD-aux []       _ b = return-cost b
  foldD-aux (x ∷ xs) f b = bind-cost (f (b , x)) (foldD-aux xs f)

⟦_⟧D : {A B : Ty} → A ⇨ B → ⟦ A ⟧T →C ⟦ B ⟧T
⟦ idS       ⟧D a = return-cost a
⟦ g ∘S f    ⟧D a = bind-cost (⟦ f ⟧D a) ⟦ g ⟧D
⟦ f ⊗S g    ⟧D (a , c) =
  let (n , b) = ⟦ f ⟧D a
      (m , d) = ⟦ g ⟧D c
  in (n + m , (b , d))
⟦ swapS     ⟧D (a , b) = return-cost (b , a)
⟦ exlS      ⟧D (a , _) = return-cost a
⟦ exrS      ⟧D (_ , b) = return-cost b
⟦ weakS     ⟧D _ = return-cost tt
⟦ runitS    ⟧D a = return-cost (a , tt)
⟦ inlS      ⟧D a = return-cost (inj₁ a)
⟦ inrS      ⟧D b = return-cost (inj₂ b)
⟦ caseS l r ⟧D (inj₁ a) = ⟦ l ⟧D a
⟦ caseS l r ⟧D (inj₂ b) = ⟦ r ⟧D b
⟦ distlS    ⟧D (a , inj₁ b) = return-cost (inj₁ (a , b))
⟦ distlS    ⟧D (a , inj₂ c) = return-cost (inj₂ (a , c))
⟦ nilS      ⟧D _ = return-cost []
⟦ consS     ⟧D (x , xs) = return-cost (x ∷ xs)
⟦ unconsS   ⟧D [] = return-cost (inj₁ tt)
⟦ unconsS   ⟧D (x ∷ xs) = return-cost (inj₂ (x , xs))
⟦ natOutS   ⟧D zero = return-cost (inj₁ tt)
⟦ natOutS   ⟧D (suc n) = return-cost (inj₂ n)
⟦ sucS      ⟧D n = return-cost (suc n)
⟦ addS      ⟧D (a , b) = return-cost (a + b)
⟦ constS k  ⟧D _ = return-cost k
⟦ dupNatS   ⟧D n = (1 , (n , n))                       -- atom copy: 1 word
⟦ dupS {A}  ⟧D a = (sizeT A a , (a , a))               -- THE charge
⟦ boxS f    ⟧D a = ⟦ f ⟧D a
⟦ boxValS f ⟧D a = ⟦ f ⟧D a
⟦ mergeS    ⟧D p = return-cost p
⟦ iterS f   ⟧D (n , a) = iterD-aux n ⟦ f ⟧D a
⟦ foldS f   ⟧D (xs , b) = foldD-aux xs ⟦ f ⟧D b

dupGrade : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ℕ
dupGrade f a = proj₁ (⟦ f ⟧D a)

-- ────────────────────────────────────────────────────────────────────────────
-- § 7  Space — (⊔,+): sequential stages reuse, parallel branches co-live
--      (port of the agda branch's ⟦_⟧SP word model)
-- ────────────────────────────────────────────────────────────────────────────

private
  -- NB types are EXPLICIT here: ⟦_⟧T is non-injective (⟦!A⟧T = ⟦A⟧T),
  -- so Agda cannot infer A/B from values.
  prim-sp : (A B : Ty) → ⟦ A ⟧T → ⟦ B ⟧T → ℕ × ⟦ B ⟧T
  prim-sp A B a b = (sizeT A a ⊔ sizeT B b , b)

  iterSP-aux : {A : Set} → (A → ℕ) → ℕ → (A → ℕ × A) → A → ℕ × A
  iterSP-aux sz zero    _ a = (sz a , a)
  iterSP-aux sz (suc n) f a =
    let (p  , b) = f a
        (pr , c) = iterSP-aux sz n f b
    in (p ⊔ pr , c)

  foldSP-aux : {A B : Set} → (B → ℕ) → List A → ((B × A) → ℕ × B) → B → ℕ × B
  foldSP-aux sz []       _ b = (sz b , b)
  foldSP-aux sz (x ∷ xs) f b =
    let (p  , b') = f (b , x)
        (pr , r)  = foldSP-aux sz xs f b'
    in (p ⊔ pr , r)

⟦_⟧SP : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ℕ × ⟦ B ⟧T
⟦_⟧SP {A} idS a = (sizeT A a , a)
⟦ g ∘S f    ⟧SP a =
  let (pf , vf) = ⟦ f ⟧SP a
      (pg , vg) = ⟦ g ⟧SP vf
  in (pf ⊔ pg , vg)
⟦ f ⊗S g    ⟧SP (a , c) =
  let (pf , b) = ⟦ f ⟧SP a
      (pg , d) = ⟦ g ⟧SP c
  in (pf + pg , (b , d))
⟦ swapS {A} {B} ⟧SP p@(a , b) = prim-sp (A ⊗ B) (B ⊗ A) p (b , a)
⟦ exlS {A} {B}  ⟧SP p@(a , _) = prim-sp (A ⊗ B) A p a
⟦ exrS {A} {B}  ⟧SP p@(_ , b) = prim-sp (A ⊗ B) B p b
⟦ weakS {A}     ⟧SP a = prim-sp A unit a tt
⟦ runitS {A}    ⟧SP a = prim-sp A (A ⊗ unit) a (a , tt)
⟦ inlS {A} {B}  ⟧SP a = prim-sp A (A ⊕ B) a (inj₁ a)
⟦ inrS {A} {B}  ⟧SP b = prim-sp B (A ⊕ B) b (inj₂ b)
⟦ caseS l r ⟧SP (inj₁ a) = ⟦ l ⟧SP a
⟦ caseS l r ⟧SP (inj₂ b) = ⟦ r ⟧SP b
⟦ distlS {A} {B} {C} ⟧SP p@(a , inj₁ b) =
  prim-sp (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C)) p (inj₁ (a , b))
⟦ distlS {A} {B} {C} ⟧SP p@(a , inj₂ c) =
  prim-sp (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C)) p (inj₂ (a , c))
⟦ nilS {A}      ⟧SP a = prim-sp unit (listT A) a []
⟦ consS {A}     ⟧SP p@(x , xs) = prim-sp (A ⊗ listT A) (listT A) p (x ∷ xs)
⟦ unconsS {A}   ⟧SP p@[] = prim-sp (listT A) (unit ⊕ (A ⊗ listT A)) p (inj₁ tt)
⟦ unconsS {A}   ⟧SP p@(x ∷ xs) =
  prim-sp (listT A) (unit ⊕ (A ⊗ listT A)) p (inj₂ (x , xs))
⟦ natOutS   ⟧SP zero = prim-sp nat (unit ⊕ nat) zero (inj₁ tt)
⟦ natOutS   ⟧SP n@(suc k) = prim-sp nat (unit ⊕ nat) n (inj₂ k)
⟦ sucS      ⟧SP n = prim-sp nat nat n (suc n)
⟦ addS      ⟧SP p@(a , b) = prim-sp (nat ⊗ nat) nat p (a + b)
⟦ constS {A} k ⟧SP a = prim-sp A nat a k
⟦ dupNatS   ⟧SP n = prim-sp nat (nat ⊗ nat) n (n , n)
⟦ dupS {A}  ⟧SP a = prim-sp (! A) (! A ⊗ ! A) a (a , a)  -- both copies live
⟦ boxS f    ⟧SP a = ⟦ f ⟧SP a
⟦ boxValS f ⟧SP a = ⟦ f ⟧SP a
⟦ mergeS {A} {B} ⟧SP p = prim-sp (! A ⊗ ! B) (! (A ⊗ B)) p p
⟦ iterS {A} f ⟧SP (n , a) = iterSP-aux (sizeT (! A)) n ⟦ f ⟧SP a
⟦ foldS {A} {B} f ⟧SP (xs , b) = foldSP-aux (sizeT (! B)) xs ⟦ f ⟧SP b

space : {A B : Ty} → A ⇨ B → ⟦ A ⟧T → ℕ
space f a = proj₁ (⟦ f ⟧SP a)

-- ────────────────────────────────────────────────────────────────────────────
-- § 8  Execution — TelM, mirroring ⟦_⟧C step for step
-- ────────────────────────────────────────────────────────────────────────────

private
  iterT-aux : {A : Set} → ℕ → (A →K A) → A →K A
  iterT-aux zero    _ a = return-tel a
  iterT-aux (suc n) f a = step-tel (bind-tel (f a) (iterT-aux n f))

  foldT-aux : {A B : Set} → List A → ((B × A) →K B) → B →K B
  foldT-aux []       _ b = return-tel b
  foldT-aux (x ∷ xs) f b = step-tel (bind-tel (f (b , x)) (foldT-aux xs f))

⟦_⟧K : {A B : Ty} → A ⇨ B → ⟦ A ⟧T →K ⟦ B ⟧T
⟦ idS       ⟧K a = return-tel a
⟦ g ∘S f    ⟧K a = bind-tel (⟦ f ⟧K a) ⟦ g ⟧K
⟦ f ⊗S g    ⟧K (a , c) = bind-tel (⟦ f ⟧K a) λ b →
                          bind-tel (⟦ g ⟧K c) λ d →
                          return-tel (b , d)
⟦ swapS     ⟧K (a , b) = return-tel (b , a)
⟦ exlS      ⟧K (a , _) = return-tel a
⟦ exrS      ⟧K (_ , b) = return-tel b
⟦ weakS     ⟧K _ = return-tel tt
⟦ runitS    ⟧K a = return-tel (a , tt)
⟦ inlS      ⟧K a = return-tel (inj₁ a)
⟦ inrS      ⟧K b = return-tel (inj₂ b)
⟦ caseS l r ⟧K (inj₁ a) = ⟦ l ⟧K a
⟦ caseS l r ⟧K (inj₂ b) = ⟦ r ⟧K b
⟦ distlS    ⟧K (a , inj₁ b) = return-tel (inj₁ (a , b))
⟦ distlS    ⟧K (a , inj₂ c) = return-tel (inj₂ (a , c))
⟦ nilS      ⟧K _ = return-tel []
⟦ consS     ⟧K (x , xs) = return-tel (x ∷ xs)
⟦ unconsS   ⟧K [] = return-tel (inj₁ tt)
⟦ unconsS   ⟧K (x ∷ xs) = return-tel (inj₂ (x , xs))
⟦ natOutS   ⟧K zero = step-tel (return-tel (inj₁ tt))
⟦ natOutS   ⟧K (suc n) = step-tel (return-tel (inj₂ n))
⟦ sucS      ⟧K n = return-tel (suc n)
⟦ addS      ⟧K (a , b) = return-tel (a + b)
⟦ constS k  ⟧K _ = return-tel k
⟦ dupNatS   ⟧K n = return-tel (n , n)
⟦ dupS      ⟧K a = return-tel (a , a)
⟦ boxS f    ⟧K a = ⟦ f ⟧K a
⟦ boxValS f ⟧K a = ⟦ f ⟧K a
⟦ mergeS    ⟧K p = return-tel p
⟦ iterS f   ⟧K (n , a) = iterT-aux n ⟦ f ⟧K a
⟦ foldS f   ⟧K (xs , b) = foldT-aux xs ⟦ f ⟧K b

-- ────────────────────────────────────────────────────────────────────────────
-- § 9  Precision ⇒ Adequacy  (the agda branch's §8e technique, verbatim)
-- ────────────────────────────────────────────────────────────────────────────

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
precise exlS        (a , _) extra = refl
precise exrS        (_ , b) extra = refl
precise weakS       _       extra = refl
precise runitS      a       extra = refl
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
precise dupS        a       extra = refl
precise (boxS f)    a extra = precise f a extra
precise (boxValS f) a extra = precise f a extra
precise mergeS      p       extra = refl
precise (iterS f)   (n , a) extra = iter-prec n a extra
  where
    iter-prec : ∀ n a extra →
      iterT-aux n ⟦ f ⟧K a (proj₁ (iterC-aux n ⟦ f ⟧C a) + extra)
      ≡ just (proj₂ (iterC-aux n ⟦ f ⟧C a) , extra)
    iter-prec zero    a extra = refl
    iter-prec (suc k) a extra =
      let cf  = proj₁ (⟦ f ⟧C a)
          vf  = proj₂ (⟦ f ⟧C a)
          cr  = proj₁ (iterC-aux k ⟦ f ⟧C vf)
          pf  = precise f a (cr + extra)
          pf' = subst (λ tel → ⟦ f ⟧K a tel ≡ just (vf , cr + extra))
                      (sym (+-assoc cf cr extra)) pf
          ih  = iter-prec k vf extra
      in trans (cong (λ mx → mx >>= λ { (v , t') → iterT-aux k ⟦ f ⟧K v t' }) pf')
               ih
precise (foldS f)   (xs , b) extra = fold-prec xs b extra
  where
    fold-prec : ∀ xs b extra →
      foldT-aux xs ⟦ f ⟧K b (proj₁ (foldC-aux xs ⟦ f ⟧C b) + extra)
      ≡ just (proj₂ (foldC-aux xs ⟦ f ⟧C b) , extra)
    fold-prec []       b extra = refl
    fold-prec (x ∷ xs) b extra =
      let cf  = proj₁ (⟦ f ⟧C (b , x))
          vf  = proj₂ (⟦ f ⟧C (b , x))
          cr  = proj₁ (foldC-aux xs ⟦ f ⟧C vf)
          pf  = precise f (b , x) (cr + extra)
          pf' = subst (λ tel → ⟦ f ⟧K (b , x) tel ≡ just (vf , cr + extra))
                      (sym (+-assoc cf cr extra)) pf
          ih  = fold-prec xs vf extra
      in trans (cong (λ mx → mx >>= λ { (v , t') → foldT-aux xs ⟦ f ⟧K v t' }) pf')
               ih

-- ADEQUACY: run with the computed budget ⇒ always finishes, with 0 left.
adequate : {A B : Ty} → (f : A ⇨ B) → ∀ a →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a)) ≡ just (proj₂ (⟦ f ⟧C a) , 0)
adequate f a =
  subst (λ tel → ⟦ f ⟧K a tel ≡ just (proj₂ (⟦ f ⟧C a) , 0))
        (+-identityʳ (proj₁ (⟦ f ⟧C a)))
        (precise f a 0)

-- ────────────────────────────────────────────────────────────────────────────
-- § 10  Worked examples — every grade computes by refl
-- ────────────────────────────────────────────────────────────────────────────

-- double n = iterate (+2) n times from a boxed 0.  n is consumed ONCE (as
-- fuel); the seed is a closed value, boxed by empty-context promotion.
-- Fully affine: dup grade 0.
double : nat ⇨ ! nat
double = iterS (sucS ∘S sucS) ∘S (idS ⊗S boxValS (constS 0)) ∘S runitS

double-val : ⟦ double ⟧V 5 ≡ 10
double-val = refl

double-cost : proj₁ (⟦ double ⟧C 5) ≡ 5          -- 1 tel per iteration
double-cost = refl

double-dup : dupGrade double 5 ≡ 0               -- affine by construction
double-dup = refl

double-depth : depth double ≡ 1                  -- result one level down
double-depth = refl

double-adequate : ⟦ double ⟧K 5 5 ≡ just (10 , 0)
double-adequate = adequate double 5

-- The atom exemption: n + n duplicates a machine scalar (free on HVM2,
-- charged 1 word by the grade).
addTwice : nat ⇨ nat
addTwice = addS ∘S dupNatS

addTwice-val : ⟦ addTwice ⟧V 5 ≡ 10
addTwice-val = refl

addTwice-dup : dupGrade addTwice 5 ≡ 1
addTwice-dup = refl

-- sumList: fold addition over a list, seed a boxed closed 0.  The list is
-- consumed affinely — dup grade 0 by construction.
sumList : listT nat ⇨ ! nat
sumList = foldS addS ∘S (idS ⊗S boxValS (constS 0)) ∘S runitS

egList : ⟦ listT nat ⟧T
egList = 1 ∷ 2 ∷ 3 ∷ []

sumList-val : ⟦ sumList ⟧V egList ≡ 6
sumList-val = refl

sumList-cost : proj₁ (⟦ sumList ⟧C egList) ≡ 3   -- 1 tel per element
sumList-cost = refl

sumList-dup : dupGrade sumList egList ≡ 0        -- affine ⇒ free on nets
sumList-dup = refl

-- Sharing a computed value: THE bend-port lesson, priced.  The sum comes
-- back boxed; dupS copies the box; with no dereliction the copies are
-- consumed one level down, via mergeS + boxS addS.  The dup charge (size of
-- the copied value: 1 word) is visible statically — not discovered at 10⁹
-- interactions.
sumTwice : listT nat ⇨ ! nat
sumTwice = boxS addS ∘S mergeS ∘S dupS ∘S sumList

sumTwice-val : ⟦ sumTwice ⟧V egList ≡ 12
sumTwice-val = refl

sumTwice-dup : dupGrade sumTwice egList ≡ 1      -- one boxed word, copied once
sumTwice-dup = refl

-- Nesting boxes stacks strata: towerHeight is the coarse cost report.
twoLevels : unit ⇨ ! ! nat
twoLevels = boxValS (boxValS (constS 7))

twoLevels-depth : towerHeight twoLevels ≡ 2
twoLevels-depth = refl

-- THE FORBIDDEN PATTERN (design doc §7): using an iteration's OUTPUT as the
-- STEP of an iteration at the same level.  In this first-order skeleton it
-- is unwritable by construction — iterS takes its step as SYNTAX, and the
-- output type ! A is not a morphism.  In the higher-order surface language
-- the same restriction surfaces as the stratification typing error:
--   "this iteration's step function is itself built by iteration at the
--    same level; hoist it or raise the level."
-- Unwrapping would need der : !A ⇨ A (dereliction) or dig : !A ⇨ !!A —
-- which this category deliberately does not contain.
