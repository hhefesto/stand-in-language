-- Telomare: Denotational Design with Auto-Computed Telomere
-- Following Conal Elliott's methodology:
--   • Denotational Design (choose the model first)
--   • Type Class Morphisms (derive structure homomorphically)
--   • Compiling to Categories (same program, two interpretations)
--
-- Core question answered here:
--   How much telomere (gas) does a program need?
--   Answer: compute it via a second categorical interpretation.

{-# OPTIONS --guardedness #-}
module telomare where

open import Data.Nat             using (ℕ; zero; suc; _+_; _⊓_; _⊔_)
open import Data.Maybe           using (Maybe; just; nothing; _>>=_)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.List            using (List; []; _∷_; length)
open import Data.Bool            using (Bool; true; false; if_then_else_)
open import Data.Unit            using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat.Properties                   using (+-assoc; +-identityʳ)
open import Function                              using (_∘_)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 1.  DENOTATIONAL DESIGN: CHOOSE THE SEMANTIC MODELS FIRST
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Following Elliott's Denotational Design principle: choose the model first,
-- derive all structure from it via Type Class Morphisms.
--
-- We choose TWO semantic domains — two "views" of the same program:
--
--   TelM A  = Tel → Maybe (A × Tel)   Execution: may fail if tel runs out
--   CostM A = ℕ × A                   Cost:      always succeeds, tracks cost
--
-- Both are monads. The SAME program structure lives in both categories.
-- Changing the category gives a different interpretation:
--   "Compiling to Categories" (Elliott, ICFP 2017)
--
-- The ADEQUACY THEOREM connects the two views:
--   If CostM computes (needed-tel, result) for input a,
--   then TelM produces just (result, 0) when given exactly needed-tel.
--
-- This lets us run programs WITHOUT specifying the tel budget manually —
-- the budget is CALCULATED from the program structure.

-- ─────────────────────────────────────────────────────────────────────────────
-- § 2.  THE EXECUTION MONAD: TelM
-- ─────────────────────────────────────────────────────────────────────────────
--
-- TelM A = Tel → Maybe (A × Tel)  (State ℕ + Failure monad)
--   • just (v , g') = produced value v, g' tel remains
--   • nothing       = telomere exhausted — program halts gracefully
--
-- Each `step-tel` consumes 1 unit of Tel, bounding recursion depth.
-- Totality: TelM computations are total functions — they always
-- return just-or-nothing, never diverge.

Tel : Set
Tel = ℕ

TelM : Set → Set
TelM A = Tel → Maybe (A × Tel)

return-tel : {A : Set} → A → TelM A
return-tel a g = just (a , g)          -- pure value: costs 0 tel

bind-tel : {A B : Set} → TelM A → (A → TelM B) → TelM B
bind-tel m f g = m g >>= λ { (a , g') → f a g' }

step-tel : {A : Set} → TelM A → TelM A
step-tel m zero    = nothing           -- tel exhausted → halt gracefully
step-tel m (suc g) = m g              -- consume 1 tel, continue

-- ─────────────────────────────────────────────────────────────────────────────
-- § 3.  THE COST MONAD: CostM   (Writer ℕ)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- CostM A = ℕ × A  (Writer monad for ℕ)
--   • The ℕ component accumulates the total tel cost
--   • The A component carries the computed result
--
-- Operations MIRROR TelM exactly — same structure, different semantics:
--   return-cost  ↔  return-tel   (0 cost,  value threaded)
--   bind-cost    ↔  bind-tel     (costs added, values composed)
--   step-cost    ↔  step-tel     (cost += 1, NOT subtracted from budget)
--
-- KEY: CostM never fails. It ALWAYS produces a result.
-- This is the "static analysis" dual of TelM's "dynamic execution".

CostM : Set → Set
CostM A = ℕ × A

return-cost : {A : Set} → A → CostM A
return-cost a = (0 , a)               -- pure value: 0 cost

bind-cost : {A B : Set} → CostM A → (A → CostM B) → CostM B
bind-cost (n , a) f =
  let (m , b) = f a
  in  (n + m , b)                    -- costs add up

step-cost : {A : Set} → CostM A → CostM A
step-cost (n , a) = (suc n , a)      -- +1 to cost

-- ─────────────────────────────────────────────────────────────────────────────
-- § 4.  THE TWO KLEISLI CATEGORIES
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Both TelM and CostM give rise to Kleisli categories:
--
--   A →K B  =  A → TelM B    (execution: may fail)
--   A →C B  =  A → CostM B   (cost analysis: always succeeds)
--
-- Same program structure, two interpretations — "Compiling to Categories".

infixr 0 _→K_ _→C_

_→K_ : Set → Set → Set
A →K B = A → TelM B

_→C_ : Set → Set → Set
A →C B = A → CostM B

-- Category structure for →K
idK : {A : Set} → A →K A
idK = return-tel

_∘K_ : {A B C : Set} → (B →K C) → (A →K B) → (A →K C)
(g ∘K f) a = bind-tel (f a) g

-- Category structure for →C
idC : {A : Set} → A →C A
idC = return-cost

_∘C_ : {A B C : Set} → (B →C C) → (A →C B) → (A →C C)
(g ∘C f) a = bind-cost (f a) g

-- Cartesian structure for →K (fork both morphisms, thread tel sequentially)
forkK : {A B C : Set} → (A →K B) → (A →K C) → A →K (B × C)
forkK f g a = bind-tel (f a) λ b →
              bind-tel (g a) λ c →
              return-tel (b , c)

-- Cartesian structure for →C (costs add; both applied to same input)
-- Using let-binding so proj₁ (forkC f g a) = n + m definitionally
-- (bind-cost of return-cost would give n + (m + 0), breaking precision proofs)
forkC : {A B C : Set} → (A →C B) → (A →C C) → A →C (B × C)
forkC f g a =
  let (n , vf) = f a
      (m , vg) = g a
  in (n + m , (vf , vg))

-- ─────────────────────────────────────────────────────────────────────────────
-- § 4.5  TYPE OBJECTS
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Placed here so later syntax/fibonacci sections can define object-level types
-- (like FibStateTy) as Ty expressions.
-- The typed syntax category _⇨S_ is defined later in §8.

data Ty : Set where
  unit : Ty
  nat  : Ty
  bool : Ty
  _⊗_  : Ty → Ty → Ty
  _⊕_  : Ty → Ty → Ty   -- coproduct (sum): enables branching
  listT : Ty → Ty       -- recursive type: lists (needs more than sums!)

infixl 5 _⊗_
infixl 4 _⊕_

⟦_⟧T : Ty → Set
⟦ unit  ⟧T = ⊤
⟦ nat   ⟧T = ℕ
⟦ bool  ⟧T = Bool
⟦ A ⊗ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A ⊕ B ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ listT A ⟧T = List ⟦ A ⟧T

-- ─────────────────────────────────────────────────────────────────────────────
-- § 5.  RECURSION PRIMITIVE FOR EXECUTION (TelM)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- fixT: every recursive unfolding costs 1 tel (via step-tel).
-- Totality: fixT-aux recurses structurally on an explicit fuel argument
-- that equals the initial tel. Recursion depth ≤ initial tel.
--
-- No fixT needed for CostM! CostM is always total — we use direct
-- structural recursion instead. This is the key asymmetry:
--   TelM needs a fuel trick to terminate in Agda
--   CostM terminates by structural recursion on the input

private
  fixT-aux : {S R : Set} → Tel → ((S →K R) → S →K R) → S →K R
  fixT-aux zero    _    _ _ = nothing
  fixT-aux (suc f) body s   = step-tel (body (fixT-aux f body) s)

fixT : {S R : Set} → ((S →K R) → S →K R) → S →K R
fixT body s g = fixT-aux g body s g
-- fuel = tel: each unfolding costs 1 step AND 1 fuel, giving tight bound.

private
  -- pred on ⟦ nat ⟧T; used as denotation of predS in §8.
  predℕ : ⟦ nat ⟧T → ⟦ nat ⟧T
  predℕ zero    = zero
  predℕ (suc k) = k



-- ─────────────────────────────────────────────────────────────────────────────
-- § 6.  PROGRAMS: BUNDLING COST AND EXECUTION
-- ─────────────────────────────────────────────────────────────────────────────
--
-- A Program A B bundles:
--   • cost-exec : A →C B   — cost interpretation (always succeeds)
--   • exec      : A →K B   — execution interpretation (may fail)
--   • adequate  : proof that they are consistent
--
-- The adequate field is the machine-checked TCM (Type Class Morphism)
-- condition (Elliott, ICFP 2009): the two interpretations commute.
--
-- Given a Program, we can run it WITHOUT specifying the tel budget.
-- The budget is AUTOMATICALLY computed from the cost interpretation.

record Program (A B : Set) : Set where
  field
    cost-exec : A →C B
    exec      : A →K B
    adequate  : ∀ a → exec a (proj₁ (cost-exec a)) ≡ just (proj₂ (cost-exec a) , 0)

-- fibProgram is defined after fibS in §10, using fromSyntax.

-- ─────────────────────────────────────────────────────────────────────────────
-- § 7.  AUTO-RUNNING PROGRAMS
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Given any Program, we can run it with an automatically computed tel budget.
-- By the adequacy theorem, this ALWAYS succeeds — never halts for lack of tel.

data Result (A : Set) : Set where
  halted   : Result A
  finished : A → ℕ → Result A

run : {A : Set} → TelM A → Tel → Result A
run c g with c g
... | nothing      = halted
... | just (v , r) = finished v r

-- Run a Program with auto-computed tel budget
runAuto : {A B : Set} → Program A B → A → Result B
runAuto prog a = run (Program.exec prog a) (proj₁ (Program.cost-exec prog a))

-- By Program.adequate, runAuto always returns finished — never halted.

-- ─────────────────────────────────────────────────────────────────────────────
-- § 8.  TYPED SYNTAX CATEGORY
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Inspired by telomare-backwards.agda (Conal Elliott's denotational design):
--   • Ty : type-level objects
--   • A ⇨S B : typed programs-as-syntax (categorical arrows)
--   • ⟦_⟧K : execution denotation  (A ⇨S B → ⟦A⟧T →K ⟦B⟧T)
--   • ⟦_⟧C : cost denotation       (A ⇨S B → ⟦A⟧T →C ⟦B⟧T)
--
-- KEY addition over telomare-backwards.agda:
--   Two denotations, not one.  fromSyntax packages both together with a
--   machine-checked adequacy proof — runFromSyntax then ALWAYS succeeds,
--   with the tel budget computed automatically from the syntax.

-- §8a. Type objects — see §4.5 for Ty, ⟦_⟧T.
--       Ty has constructors: unit, nat, bool, _⊗_
--       ⟦_⟧T : Ty → Set   (unit→⊤, nat→ℕ, bool→Bool, A⊗B→⟦A⟧T×⟦B⟧T)

-- §8b. Morphisms (typed programs as categorical arrows)
data _⇨S_ : Ty → Ty → Set where
  idS   : {A : Ty}     → A ⇨S A
  _∘S_  : {A B C : Ty} → B ⇨S C → A ⇨S B → A ⇨S C
  !S    : {A : Ty}     → A ⇨S unit
  forkS : {A B C : Ty} → A ⇨S B → A ⇨S C → A ⇨S (B ⊗ C)
  exlS  : {A B : Ty}   → (A ⊗ B) ⇨S A
  exrS  : {A B : Ty}   → (A ⊗ B) ⇨S B
  -- Cocartesian structure: injections + case eliminator (data-dependent branching).
  inlS  : {A B : Ty}   → A ⇨S (A ⊕ B)
  inrS  : {A B : Ty}   → B ⇨S (A ⊕ B)
  caseS : {A B C : Ty} → A ⇨S C → B ⇨S C → (A ⊕ B) ⇨S C
  -- List structure: build (nil/cons) and destruct (uncons → 1 ⊕ head×tail).
  nilS    : {A : Ty} → unit ⇨S listT A
  consS   : {A : Ty} → (A ⊗ listT A) ⇨S listT A
  unconsS : {A : Ty} → listT A ⇨S (unit ⊕ (A ⊗ listT A))
  addS   :                 (nat ⊗ nat) ⇨S nat      -- addition: ⟦A⟧T×⟦B⟧T→ℕ
  predS  :                 nat ⇨S nat               -- predecessor: pred n
  minS   :                 (nat ⊗ nat) ⇨S nat       -- minimum (compare); costs 1 tel
  maxS   :                 (nat ⊗ nat) ⇨S nat       -- maximum (compare); costs 1 tel
  constS : {A : Ty} → ℕ → A ⇨S nat                -- constant natural: ignores input
  iterS  : {A : Ty} → A ⇨S A → (nat ⊗ A) ⇨S A    -- bounded iteration: apply f n times
  fixS   : {A B : Ty}
        → (bodyK : ((⟦ A ⟧T →K ⟦ B ⟧T) → ⟦ A ⟧T →K ⟦ B ⟧T)
                 )
        → (costF : ⟦ A ⟧T →C ⟦ B ⟧T)
        → (precF : ∀ (a : ⟦ A ⟧T) (extra : ℕ) →
            fixT bodyK a (proj₁ (costF a) + extra)
            ≡ just (proj₂ (costF a) , extra))
        → A ⇨S B

infixr 2 _⇨S_
infixr 9 _∘S_

-- Bounded iteration helpers for iterS.
-- iterT-aux n f a: apply f n times in TelM, consuming 1 tel per step.
-- iterC-aux n f a: count n steps in CostM, always succeeding.
private
  iterT-aux : {A : Set} → ℕ → (A →K A) → A →K A
  iterT-aux zero    _ a = return-tel a
  iterT-aux (suc n) f a = step-tel (bind-tel (f a) (iterT-aux n f))

  iterC-aux : {A : Set} → ℕ → (A →C A) → A →C A
  iterC-aux zero    _ a = return-cost a
  iterC-aux (suc n) f a = step-cost (bind-cost (f a) (iterC-aux n f))

-- §8c. Execution denotation: A ⇨S B → ⟦A⟧T →K ⟦B⟧T
⟦_⟧K : {A B : Ty} → A ⇨S B → ⟦ A ⟧T →K ⟦ B ⟧T
⟦ idS       ⟧K = idK
⟦ g ∘S f    ⟧K = ⟦ g ⟧K ∘K ⟦ f ⟧K
⟦ !S        ⟧K _ = return-tel tt
⟦ forkS f g ⟧K = forkK ⟦ f ⟧K ⟦ g ⟧K
⟦ exlS      ⟧K (a , _) = return-tel a
⟦ exrS      ⟧K (_ , b) = return-tel b
⟦ inlS      ⟧K a = return-tel (inj₁ a)
⟦ inrS      ⟧K b = return-tel (inj₂ b)
⟦ caseS l r ⟧K (inj₁ a) = ⟦ l ⟧K a       -- branch on the data: take left
⟦ caseS l r ⟧K (inj₂ b) = ⟦ r ⟧K b       -- take right
⟦ nilS      ⟧K _ = return-tel []
⟦ consS     ⟧K (x , xs) = return-tel (x ∷ xs)
⟦ unconsS   ⟧K [] = return-tel (inj₁ tt)
⟦ unconsS   ⟧K (x ∷ xs) = return-tel (inj₂ (x , xs))
⟦ addS        ⟧K (a , b) = return-tel (a + b)
⟦ predS       ⟧K n       = return-tel (predℕ n)
⟦ minS        ⟧K (a , b) = step-tel (return-tel (a ⊓ b))
⟦ maxS        ⟧K (a , b) = step-tel (return-tel (a ⊔ b))
⟦ constS k    ⟧K _       = return-tel k
⟦ iterS f     ⟧K (n , a) = iterT-aux n ⟦ f ⟧K a
⟦ fixS bodyK _ _ ⟧K = fixT bodyK

-- §8d. Cost denotation: A ⇨S B → ⟦A⟧T →C ⟦B⟧T
⟦_⟧C : {A B : Ty} → A ⇨S B → ⟦ A ⟧T →C ⟦ B ⟧T
⟦ idS       ⟧C = idC
⟦ g ∘S f    ⟧C = ⟦ g ⟧C ∘C ⟦ f ⟧C
⟦ !S        ⟧C _ = return-cost tt
⟦ forkS f g ⟧C = forkC ⟦ f ⟧C ⟦ g ⟧C
⟦ exlS      ⟧C (a , _) = return-cost a
⟦ exrS      ⟧C (_ , b) = return-cost b
⟦ inlS      ⟧C a = return-cost (inj₁ a)
⟦ inrS      ⟧C b = return-cost (inj₂ b)
⟦ caseS l r ⟧C (inj₁ a) = ⟦ l ⟧C a       -- cost = cost of the TAKEN branch
⟦ caseS l r ⟧C (inj₂ b) = ⟦ r ⟧C b
⟦ nilS      ⟧C _ = return-cost []
⟦ consS     ⟧C (x , xs) = return-cost (x ∷ xs)
⟦ unconsS   ⟧C [] = return-cost (inj₁ tt)
⟦ unconsS   ⟧C (x ∷ xs) = return-cost (inj₂ (x , xs))
⟦ addS        ⟧C (a , b) = return-cost (a + b)
⟦ predS       ⟧C n       = return-cost (predℕ n)
⟦ minS        ⟧C (a , b) = step-cost (return-cost (a ⊓ b))
⟦ maxS        ⟧C (a , b) = step-cost (return-cost (a ⊔ b))
⟦ constS k    ⟧C _       = return-cost k
⟦ iterS f     ⟧C (n , a) = iterC-aux n ⟦ f ⟧C a
⟦ fixS _ costF _ ⟧C = costF

-- §8e. Precision: the key property connecting ⟦_⟧K and ⟦_⟧C
--
-- Precise f: running ⟦f⟧K with (computed-cost + extra) leaves exactly
--            extra tel remaining for any extra ∈ ℕ.
--
-- Adequacy is the special case extra = 0.
-- Precision is needed to prove adequacy for composed programs by induction:
-- when f costs n and g costs m, and we give g∘f a budget of (n+m)+extra,
-- we need f to leave exactly m+extra for g.

Precise : {A B : Ty} → A ⇨S B → Set
Precise {A} {B} f = ∀ (a : ⟦ A ⟧T) (extra : ℕ) →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a) + extra) ≡ just (proj₂ (⟦ f ⟧C a) , extra)

precise : {A B : Ty} → (f : A ⇨S B) → Precise f
-- idS / !S / exlS / exrS / addS / predS: cost = 0, (0 + extra) = extra → refl
precise idS         a         extra = refl
precise !S          _         extra = refl
precise exlS        (a , _)   extra = refl
precise exrS        (_ , b)   extra = refl
precise addS        (a , b)   extra = refl
precise predS       n         extra = refl
-- minS / maxS: cost = 1 (step-cost); (suc 0 + extra) = suc extra, step-tel fires → refl
precise minS        (a , b)   extra = refl
precise maxS        (a , b)   extra = refl
-- inlS / inrS: cost 0 (return), (0 + extra) = extra → refl
precise inlS        a         extra = refl
precise inrS        b         extra = refl
-- caseS l r: cost = taken branch's cost; precision follows by branch-split,
-- reusing the precision of the chosen branch.  (Cost is now DATA-DEPENDENT, but
-- still exact & guaranteed per input — the whole point.)
precise (caseS l r) (inj₁ a)  extra = precise l a extra
precise (caseS l r) (inj₂ b)  extra = precise r b extra
-- list constructors: cost 0, (0 + extra) = extra → refl
precise nilS        _         extra = refl
precise consS       (x , xs)  extra = refl
precise unconsS     []        extra = refl
precise unconsS     (x ∷ xs)  extra = refl
-- constS k: cost = 0, result = k; (0 + extra) = extra definitionally → refl
precise (constS _)  _         extra = refl
-- iterS f: n steps each costing ⟦f⟧C; proved by induction on n (helper below)
precise (iterS f)   (n , a)   extra = iter-prec n a extra
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
-- fixS: precision proof is packaged in the constructor.
precise (fixS _ _ precF) a    extra = precF a extra
-- g ∘S f: costs add (n for f, m for g); use +-assoc to align the tel budget
precise (g ∘S f)    a         extra =
  let n   = proj₁ (⟦ f ⟧C a)
      vf  = proj₂ (⟦ f ⟧C a)
      m   = proj₁ (⟦ g ⟧C vf)
      -- Precision of f at slack (m + extra):
      --   ⟦f⟧K a (n + (m + extra)) ≡ just (vf , m + extra)
      pf  = precise f a (m + extra)
      -- Rewrite n + (m + extra) → (n + m) + extra  [sym of +-assoc]
      pf' = subst (λ tel → ⟦ f ⟧K a tel ≡ just (vf , m + extra))
                  (sym (+-assoc n m extra)) pf
      -- Precision of g at slack extra:
      --   ⟦g⟧K vf (m + extra) ≡ just (vg , extra)
      pg  = precise g vf extra
  in trans (cong (λ mx → mx >>= λ { (v , t') → ⟦ g ⟧K v t' }) pf') pg
-- forkS f g: run f then g on the same input; costs add
-- Uses the same +-assoc trick to show f leaves exactly m+extra for g
precise (forkS f g) a         extra =
  let n   = proj₁ (⟦ f ⟧C a)
      vf  = proj₂ (⟦ f ⟧C a)
      m   = proj₁ (⟦ g ⟧C a)
      vg  = proj₂ (⟦ g ⟧C a)
      pf  = precise f a (m + extra)
      pf' = subst (λ tel → ⟦ f ⟧K a tel ≡ just (vf , m + extra))
                  (sym (+-assoc n m extra)) pf
      pg  = precise g a extra
  in trans
       (cong (λ mx → mx >>= λ { (b , t') →
           ⟦ g ⟧K a t' >>= λ { (c , t'') → just ((b , c) , t'') } }) pf')
       (cong (λ mx → mx >>= λ { (c , t'') → just ((vf , c) , t'') }) pg)

-- §8f. Branching demo: cost is now DATA-DEPENDENT yet still exact + guaranteed.
--   branchExample : (nat ⊕ (nat ⊗ nat)) ⇨S nat
--     left  (inj₁ n)     ↦ n          via idS   — cost 0
--     right (inj₂ (a,b)) ↦ min a b    via minS  — cost 1
-- The cost the functor reports depends on which branch the input selects; for
-- each input it is exact, and `precise` (above) guarantees execution succeeds.
branchExample : (nat ⊕ (nat ⊗ nat)) ⇨S nat
branchExample = caseS idS minS

branchExample-left  : ⟦ branchExample ⟧C (inj₁ 5)       ≡ (0 , 5)
branchExample-left  = refl
branchExample-right : ⟦ branchExample ⟧C (inj₂ (3 , 7)) ≡ (1 , 3)
branchExample-right = refl

-- §8g. PARALLEL COST: a (work , span) interpretation — a THIRD functor out of the
-- syntax, in Conal's "same program, another interpretation" style.
--   work = total operations  = the sequential tel cost (so the §8e execution
--          guarantee carries over to the work component);
--   span = critical-path depth = parallel time.
-- Only forkS exposes parallelism: it ADDS work but takes the MAX of the two spans.
-- Everything else (∘S, iterS, caseS, primitives) is sequential along its path.
WS : Set → Set
WS A = (ℕ × ℕ) × A                            -- ((work , span) , value)

return-ws : {A : Set} → A → WS A
return-ws a = ((0 , 0) , a)

bind-ws : {A B : Set} → WS A → (A → WS B) → WS B
bind-ws ((w , s) , a) f =
  let ((w' , s') , b) = f a
  in  ((w + w' , s + s') , b)                 -- sequential: work AND span add

step-ws : {A : Set} → WS A → WS A
step-ws ((w , s) , a) = ((suc w , suc s) , a) -- one op: +1 work, +1 span

_→WS_ : Set → Set → Set
A →WS B = A → WS B

idWS : {A : Set} → A →WS A
idWS = return-ws

_∘WS_ : {A B C : Set} → (B →WS C) → (A →WS B) → A →WS C
(g ∘WS f) a = bind-ws (f a) g

forkWS : {A B C : Set} → (A →WS B) → (A →WS C) → A →WS (B × C)
forkWS f g a =
  let ((wf , sf) , vf) = f a
      ((wg , sg) , vg) = g a
  in  ((wf + wg , sf ⊔ sg) , (vf , vg))       -- PARALLEL: work adds, span = max

private
  iterWS-aux : {A : Set} → ℕ → (A →WS A) → A →WS A
  iterWS-aux zero    _ a = return-ws a
  iterWS-aux (suc n) f a = step-ws (bind-ws (f a) (iterWS-aux n f))

⟦_⟧WS : {A B : Ty} → A ⇨S B → ⟦ A ⟧T →WS ⟦ B ⟧T
⟦ idS       ⟧WS = idWS
⟦ g ∘S f    ⟧WS = ⟦ g ⟧WS ∘WS ⟦ f ⟧WS
⟦ !S        ⟧WS _ = return-ws tt
⟦ forkS f g ⟧WS = forkWS ⟦ f ⟧WS ⟦ g ⟧WS
⟦ exlS      ⟧WS (a , _) = return-ws a
⟦ exrS      ⟧WS (_ , b) = return-ws b
⟦ inlS      ⟧WS a = return-ws (inj₁ a)
⟦ inrS      ⟧WS b = return-ws (inj₂ b)
⟦ caseS l r ⟧WS (inj₁ a) = ⟦ l ⟧WS a
⟦ caseS l r ⟧WS (inj₂ b) = ⟦ r ⟧WS b
⟦ nilS      ⟧WS _ = return-ws []
⟦ consS     ⟧WS (x , xs) = return-ws (x ∷ xs)
⟦ unconsS   ⟧WS [] = return-ws (inj₁ tt)
⟦ unconsS   ⟧WS (x ∷ xs) = return-ws (inj₂ (x , xs))
⟦ addS      ⟧WS (a , b) = return-ws (a + b)
⟦ predS     ⟧WS n       = return-ws (predℕ n)
⟦ minS      ⟧WS (a , b) = step-ws (return-ws (a ⊓ b))
⟦ maxS      ⟧WS (a , b) = step-ws (return-ws (a ⊔ b))
⟦ constS k  ⟧WS _       = return-ws k
⟦ iterS f   ⟧WS (n , a) = iterWS-aux n ⟦ f ⟧WS a
-- fixS: no span info is bundled, so conservatively span ≔ work (assume the
-- recursion is sequential — a sound upper bound on parallel depth).
⟦ fixS _ costF _ ⟧WS a = let (c , v) = costF a in ((c , c) , v)

-- Extract work / span of a program at an input.
work span : {A B : Ty} → A ⇨S B → ⟦ A ⟧T → ℕ
work f a = proj₁ (proj₁ (⟦ f ⟧WS a))
span f a = proj₂ (proj₁ (⟦ f ⟧WS a))

-- ─────────────────────────────────────────────────────────────────────────────
-- § 9.  SYNTAX ADEQUACY AND BRIDGE
-- ─────────────────────────────────────────────────────────────────────────────

-- §9a. Adequacy for all syntax (from precision at extra = 0)
--
-- Running ⟦f⟧K with the CostM-computed budget always succeeds.
-- Derived from precision by setting extra = 0 and using +-identityʳ.
⟦⟧-adequate : {A B : Ty} → (f : A ⇨S B) → ∀ a →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a)) ≡ just (proj₂ (⟦ f ⟧C a) , 0)
⟦⟧-adequate f a =
  subst (λ tel → ⟦ f ⟧K a tel ≡ just (proj₂ (⟦ f ⟧C a) , 0))
        (+-identityʳ (proj₁ (⟦ f ⟧C a)))
        (precise f a 0)

-- §9b. Bridge: syntax → Program → runAuto
fromSyntax : {A B : Ty} → A ⇨S B → Program ⟦ A ⟧T ⟦ B ⟧T
fromSyntax f = record
  { cost-exec = ⟦ f ⟧C
  ; exec      = ⟦ f ⟧K
  ; adequate  = ⟦⟧-adequate f
  }

-- Run any typed program with automatically computed tel budget.
-- By ⟦⟧-adequate, this ALWAYS returns finished — never halted.
runFromSyntax : {A B : Ty} → A ⇨S B → ⟦ A ⟧T → Result ⟦ B ⟧T
runFromSyntax f = runAuto (fromSyntax f)

-- ─────────────────────────────────────────────────────────────────────────────
-- § 10.  FIBONACCI PURELY IN _⇨S_ SYNTAX
-- ─────────────────────────────────────────────────────────────────────────────

-- §10a. Pure-syntax fibonacci via iterS
--
-- Following Conal Elliott's Compiling to Categories:
--   same syntax, two interpretations (cost + execution).

-- Fibonacci state type in Ty syntax:
--   FibStateTy = nat ⊗ (nat ⊗ nat)  ≅  ℕ × ℕ × ℕ
FibStateTy : Ty
FibStateTy = nat ⊗ (nat ⊗ nat)

FibState : Set
FibState = ⟦ FibStateTy ⟧T
--
-- State: accumulator (a, b) with (a₀, b₀) = (0, 1).
-- Each step: (a, b) ↦ (b, a+b).
-- After n steps starting from (0, 1): (fib(n), fib(n+1)).
-- Extract the first component to get fib(n).
--
-- fibS is assembled purely from _⇨S_ constructors:
--   constS, iterS, forkS, exlS, exrS, addS, idS, ∘S
-- No host-language functions, no escape hatches.

-- Fibonacci accumulator step: (a, b) ↦ (b, a+b)
fibAccStepS : (nat ⊗ nat) ⇨S (nat ⊗ nat)
fibAccStepS = forkS exrS (addS ∘S forkS exlS exrS)

-- Initial accumulator from n: n ↦ (n, (0, 1))
-- (n is both the input and the iteration count for iterS)
fibInitS : nat ⇨S FibStateTy
fibInitS = forkS idS (forkS (constS 0) (constS 1))

-- Fibonacci: build initial state, iterate n times, extract result
--   STEP 1 (syntax):  fibS : nat ⇨S nat
--   STEP 2 (cost):    ⟦ fibS ⟧C n = (n , fib(n))   via iterC-aux
--   STEP 3 (execute): ⟦ fibS ⟧K n n = just(fib(n), 0)  via iterT-aux
fibS : nat ⇨S nat
fibS = exlS ∘S iterS fibAccStepS ∘S fibInitS

-- Bundle fibS into a Program using fromSyntax (adequacy from §8e).
-- This replaces the old host-level fibProgram (with manual fib/fibCost fields).
fibProgram : Program ℕ ℕ
fibProgram = fromSyntax fibS

-- Auto-run examples using fibProgram (budget computed from ⟦fibS⟧C).
fib-auto-0  : Result ℕ ;  fib-auto-0  = runAuto fibProgram 0
fib-auto-1  : Result ℕ ;  fib-auto-1  = runAuto fibProgram 1
fib-auto-2  : Result ℕ ;  fib-auto-2  = runAuto fibProgram 2
fib-auto-3  : Result ℕ ;  fib-auto-3  = runAuto fibProgram 3
fib-auto-4  : Result ℕ ;  fib-auto-4  = runAuto fibProgram 4
fib-auto-5  : Result ℕ ;  fib-auto-5  = runAuto fibProgram 5
fib-auto-6  : Result ℕ ;  fib-auto-6  = runAuto fibProgram 6
fib-auto-7  : Result ℕ ;  fib-auto-7  = runAuto fibProgram 7
fib-auto-8  : Result ℕ ;  fib-auto-8  = runAuto fibProgram 8
fib-auto-9  : Result ℕ ;  fib-auto-9  = runAuto fibProgram 9
fib-auto-10 : Result ℕ ;  fib-auto-10 = runAuto fibProgram 10

fib-auto-10-fromSyntax : fib-auto-10 ≡ runFromSyntax fibS 10
fib-auto-10-fromSyntax = refl

-- §10b. Fibonacci sequence expressed and evaluated via Ty typed syntax
--
-- The complete pipeline, made explicit as named Agda definitions:
--
--   STEP 1: Express the program in the _⇨S_ typed syntax category.
--           fibS : nat ⇨S nat
--           fibS = exlS ∘S iterS fibAccStepS ∘S fibInitS
--           (pure syntax — only _⇨S_ constructors, no host-language escape hatches)
--
--   STEP 2: Interpret into CostM via ⟦_⟧C.
--           fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- tel budget = n (one per iteration)
--           fibS-val  n = proj₂ (⟦ fibS ⟧C n)   -- fib(n), no execution yet
--
--   STEP 3: Interpret into TelM via ⟦_⟧K and run with the cost from Step 2.
--           fibS-run n = runFromSyntax fibS n
--           By ⟦⟧-adequate fibS n, this ALWAYS returns finished fib(n) 0.
--
-- Steps 2 and 3 are connected by the machine-checked adequacy theorem:
--   ⟦ fibS ⟧K n (fibS-cost n) ≡ just (fibS-val n , 0)

-- STEP 2: compute the tel budget via the CostM interpretation
fibS-cost : ℕ → ℕ
fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- = n

-- STEP 2 (also): the value, computed purely by CostM (no tel, no execution)
fibS-val : ℕ → ℕ
fibS-val n = proj₂ (⟦ fibS ⟧C n)    -- = fib(n)

-- STEP 3: run with the auto-computed budget
fibS-run : ℕ → Result ℕ
fibS-run = runFromSyntax fibS

-- Concrete checks at n = 10 (normalization by refl).
fibS-cost-10 : ⟦ fibS ⟧C 10 ≡ (10 , 55)
fibS-cost-10 = refl

fibS-exec-10 : ⟦ fibS ⟧K 10 10 ≡ just (55 , 0)
fibS-exec-10 = refl

fibS-adequate-10 :
  ⟦ fibS ⟧K 10 (proj₁ (⟦ fibS ⟧C 10)) ≡ just (proj₂ (⟦ fibS ⟧C 10) , 0)
fibS-adequate-10 = ⟦⟧-adequate fibS 10

-- The fibonacci sequence (fib(0) … fib(10)) via Ty typed syntax.
-- Each entry: budget from fibS-cost, result from fibS-run.
fibS-0  : Result ℕ ; fibS-0  = fibS-run 0
fibS-1  : Result ℕ ; fibS-1  = fibS-run 1
fibS-2  : Result ℕ ; fibS-2  = fibS-run 2
fibS-3  : Result ℕ ; fibS-3  = fibS-run 3
fibS-4  : Result ℕ ; fibS-4  = fibS-run 4
fibS-5  : Result ℕ ; fibS-5  = fibS-run 5
fibS-6  : Result ℕ ; fibS-6  = fibS-run 6
fibS-7  : Result ℕ ; fibS-7  = fibS-run 7
fibS-8  : Result ℕ ; fibS-8  = fibS-run 8
fibS-9  : Result ℕ ; fibS-9  = fibS-run 9
fibS-10 : Result ℕ ; fibS-10 = fibS-run 10

-- Composed programs: cost is derived from composition structure automatically.

-- fib ∘ fib: compute fib(fib(n))
-- Cost = n + fib(n), derived automatically by ⟦ fibS ∘S fibS ⟧C
doubleFibS : nat ⇨S nat
doubleFibS = fibS ∘S fibS

-- Fork: compute (fib(n), fib(n)) — runs fib twice, total cost = 2*n
fibPairS : nat ⇨S (nat ⊗ nat)
fibPairS = forkS fibS fibS

-- ─────────────────────────────────────────────────────────────────────────────
-- § 10b. MERGE SORT AS A SORTING NETWORK IN _⇨S_
-- ─────────────────────────────────────────────────────────────────────────────
--
-- _⇨S_ has no lists/recursion/branching, so a recursive list merge sort is not
-- expressible.  But a FIXED-SIZE merge sort is: a sorting network of
-- compare-and-swap blocks.  The compare-and-swap is exactly
--
--     casS = forkS minS maxS : (nat ⊗ nat) ⇨S (nat ⊗ nat)
--           (x , y)  ↦  (min x y , max x y)
--
-- and an 8-input network wires 19 of them "sort the two halves, then merge"
-- (Batcher's odd-even mergesort).  Every morphism below is built purely from
-- _⇨S_ constructors, so it is automatically `precise` (precision is
-- compositional — see §8e).  With minS/maxS each costing 1 tel, the whole
-- network costs 38 = 19 × 2, independent of the input.

-- The compare-and-swap (the heart of the merge): (x,y) ↦ (min x y, max x y).
casS : (nat ⊗ nat) ⇨S (nat ⊗ nat)
casS = forkS minS maxS

-- Eight wires.  With `infixl 5 _⊗_` this is the left-nested 8-tuple
-- ((((((nat⊗nat)⊗nat)⊗nat)⊗nat)⊗nat)⊗nat)⊗nat ; position 0 is the innermost-left.
V8 : Ty
V8 = nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat

private
  -- Projections of the 8 wires (position k, 0-indexed from the left).
  π0 π1 π2 π3 π4 π5 π6 π7 : V8 ⇨S nat
  π0 = exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
  π1 = exrS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
  π2 = exrS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
  π3 = exrS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
  π4 = exrS ∘S exlS ∘S exlS ∘S exlS
  π5 = exrS ∘S exlS ∘S exlS
  π6 = exrS ∘S exlS
  π7 = exrS

  -- One half of a compare-and-swap on two chosen wires:
  --   lo f g = min of the two wires ;  hi f g = max of the two wires.
  lo hi : (V8 ⇨S nat) → (V8 ⇨S nat) → (V8 ⇨S nat)
  lo f g = minS ∘S forkS f g
  hi f g = maxS ∘S forkS f g

  -- Reassemble eight wires into a V8 (left-nested fork tree).
  mk8 : (V8 ⇨S nat) → (V8 ⇨S nat) → (V8 ⇨S nat) → (V8 ⇨S nat)
      → (V8 ⇨S nat) → (V8 ⇨S nat) → (V8 ⇨S nat) → (V8 ⇨S nat) → (V8 ⇨S V8)
  mk8 w0 w1 w2 w3 w4 w5 w6 w7 =
    forkS (forkS (forkS (forkS (forkS (forkS (forkS w0 w1) w2) w3) w4) w5) w6) w7

  -- The six stages of Batcher odd-even mergesort on 8 wires.
  -- Comparator (i,j): position i ← min, position j ← max; other positions pass.
  L1 L2 L3 L4 L5 L6 : V8 ⇨S V8
  -- sort the two halves [0..3] and [4..7]:
  L1 = mk8 (lo π0 π1) (hi π0 π1) (lo π2 π3) (hi π2 π3)
           (lo π4 π5) (hi π4 π5) (lo π6 π7) (hi π6 π7)            -- (0,1)(2,3)(4,5)(6,7)
  L2 = mk8 (lo π0 π2) (lo π1 π3) (hi π0 π2) (hi π1 π3)
           (lo π4 π6) (lo π5 π7) (hi π4 π6) (hi π5 π7)            -- (0,2)(1,3)(4,6)(5,7)
  L3 = mk8 π0 (lo π1 π2) (hi π1 π2) π3
           π4 (lo π5 π6) (hi π5 π6) π7                            -- (1,2)(5,6)
  -- merge the two sorted halves:
  L4 = mk8 (lo π0 π4) (lo π1 π5) (lo π2 π6) (lo π3 π7)
           (hi π0 π4) (hi π1 π5) (hi π2 π6) (hi π3 π7)            -- (0,4)(1,5)(2,6)(3,7)
  L5 = mk8 π0 π1 (lo π2 π4) (lo π3 π5)
           (hi π2 π4) (hi π3 π5) π6 π7                            -- (2,4)(3,5)
  L6 = mk8 π0 (lo π1 π2) (hi π1 π2) (lo π3 π4)
           (hi π3 π4) (lo π5 π6) (hi π5 π6) π7                    -- (1,2)(3,4)(5,6)

-- The full 8-input merge-sort network.
mergeSortS : V8 ⇨S V8
mergeSortS = L6 ∘S L5 ∘S L4 ∘S L3 ∘S L2 ∘S L1

-- Machine-checked: sorting [7,6,5,4,3,2,1,0] gives [0,1,2,3,4,5,6,7],
-- and the cost functor reports 38 (= 19 comparators × 2 min/max), by refl.
mergeSort-test :
  ⟦ mergeSortS ⟧C ((((((( 7 , 6 ) , 5 ) , 4 ) , 3 ) , 2 ) , 1 ) , 0)
  ≡ (38 , ((((((( 0 , 1 ) , 2 ) , 3 ) , 4 ) , 5 ) , 6 ) , 7))
mergeSort-test = refl

-- §10c. PARALLEL COST (work , span), all machine-checked by refl.
--   fibS 10     : sequential iterS, no fork      → span = work = 10
--   fibPairS 10 : forkS fibS fibS (parallel)     → work 20 but span 10
--   mergeSortS  : 6 stages of independent CAS     → work 38 but span 6
-- The work component equals the §8d cost (sequential tel) — guarantee preserved;
-- the span component is the parallel depth Bend/HVM could realize.
fibS-WS : ⟦ fibS ⟧WS 10 ≡ ((10 , 10) , 55)
fibS-WS = refl

fibPair-WS : ⟦ fibPairS ⟧WS 10 ≡ ((20 , 10) , (55 , 55))
fibPair-WS = refl

mergeSort-WS :
  ⟦ mergeSortS ⟧WS ((((((( 7 , 6 ) , 5 ) , 4 ) , 3 ) , 2 ) , 1 ) , 0)
  ≡ ((38 , 6) , ((((((( 0 , 1 ) , 2 ) , 3 ) , 4 ) , 5 ) , 6 ) , 7))
mergeSort-WS = refl

-- work = sequential tel cost (the execution guarantee), span < work ⇒ parallelism.
mergeSort-work-is-cost :
  work mergeSortS ((((((( 7 , 6 ) , 5 ) , 4 ) , 3 ) , 2 ) , 1 ) , 0)
  ≡ proj₁ (⟦ mergeSortS ⟧C ((((((( 7 , 6 ) , 5 ) , 4 ) , 3 ) , 2 ) , 1 ) , 0))
mergeSort-work-is-cost = refl

-- §10d. GENERAL RECURSION OVER LISTS, WITH A PROVED EXACT COST.
-- With the recursive `listT` type, a genuinely recursive list program is now
-- expressible — and `fixS` *forces* you to supply a cost function AND prove it.
-- `lengthS` is the first such program: length of a list, computed by recursion,
-- with the machine-checked guarantee that it costs exactly (length + 1) tel.
-- This is the mechanism a general merge sort would use (see the note below).
lengthS : {A : Ty} → listT A ⇨S nat
lengthS {A} = fixS bodyK costF precF
  where
    bodyK : (⟦ listT A ⟧T →K ℕ) → ⟦ listT A ⟧T →K ℕ
    bodyK rec []       = return-tel 0
    bodyK rec (x ∷ xs) = bind-tel (rec xs) (λ n → return-tel (suc n))

    costF : ⟦ listT A ⟧T →C ℕ
    costF xs = (suc (length xs) , length xs)   -- cost = len+1, value = len

    precF : ∀ xs extra →
      fixT bodyK xs (proj₁ (costF xs) + extra) ≡ just (proj₂ (costF xs) , extra)
    precF []       extra = refl
    precF (x ∷ xs) extra =
      cong (λ m → m >>= λ { (n , t) → just (suc n , t) }) (precF xs extra)

-- Machine-checked: length [10,20,30] = 3, at exact cost 4 (= 3 + 1).
lengthS-test : ⟦ lengthS ⟧C (10 ∷ 20 ∷ 30 ∷ []) ≡ (4 , 3)
lengthS-test = refl

-- NOTE on general merge sort.  It is now *expressible*: lists exist (`listT`),
-- the merge step is `unconsS` + `caseS` + `minS`/`maxS` (data-dependent branching),
-- and the divide-and-conquer recursion goes through `fixS` (fuel = tel bounds the
-- recursion depth).  `fixS` still *forces* a cost guarantee — it will not
-- type-check without a `precF` proof, exactly as `lengthS` above demonstrates.
-- The remaining work is that `precF` for merge sort: an exact-tel-cost proof of a
-- well-founded recursion, which is a substantial separate formalization (a
-- comparison sort's cost is data-dependent, so the proof tracks the actual
-- comparisons rather than a closed-form constant).  `lengthS` proves the pattern
-- end-to-end; merge sort is the same pattern at scale.

-- ─────────────────────────────────────────────────────────────────────────────
-- § 11.  MAIN: DEMONSTRATE AUTO-COMPUTED TELOMARE
-- ─────────────────────────────────────────────────────────────────────────────

open import IO            using (IO; putStrLn; Main; _>>_)
open import Data.Nat.Show using (show)
open import Data.String   using (String; _++_)

private
  -- Show a Result ℕ value
  showResult : Result ℕ → String
  showResult halted         = "halted"
  showResult (finished v _) = show v

  -- Show a Result (ℕ × ℕ) value
  showResultPair : Result (ℕ × ℕ) → String
  showResultPair halted               = "halted"
  showResultPair (finished (a , b) _) = "(" ++ show a ++ ", " ++ show b ++ ")"

  -- One row of the fibonacci-via-Ty-syntax table.
  -- Explicitly shows each stage of the pipeline:
  --   n  |  ⟦fibS⟧C n (cost)  |  ⟦fibS⟧C n (val)  |  runFromSyntax fibS n
  showFibSRow : ℕ → String
  showFibSRow n =
    let cost = fibS-cost n           -- STEP 2: tel budget from CostM
        val  = fibS-val  n           -- STEP 2: value from CostM (no execution yet)
        res  = fibS-run  n           -- STEP 3: TelM run with that exact budget
    in "  fib(" ++ show n ++ ")"
       ++ "  cost=⟦fibS⟧C " ++ show n ++ "=" ++ show cost
       ++ "  val=⟦fibS⟧C " ++ show n ++ "=" ++ show val
       ++ "  run=" ++ showResult res

  -- One row for a nat ⇨S nat composed syntax program
  showComposedRow : nat ⇨S nat → String → ℕ → String
  showComposedRow prog name n =
    let cost = proj₁ (⟦ prog ⟧C n)
        res  = runFromSyntax prog n
    in "  (" ++ name ++ ")(" ++ show n ++ ")"
       ++ "  auto-cost=" ++ show cost
       ++ "  result=" ++ showResult res

  showPairRow : ℕ → String
  showPairRow n =
    let cost = proj₁ (⟦ fibPairS ⟧C n)
        res  = runFromSyntax fibPairS n
    in "  (forkS fibS fibS)(" ++ show n ++ ")"
       ++ "  auto-cost=" ++ show cost
       ++ "  result=" ++ showResultPair res

main : Main
main = IO.run do
  -- ── HEADER ──────────────────────────────────────────────────────────────
  putStrLn "================================================================"
  putStrLn "  Fibonacci sequence expressed in the Ty typed syntax (_⇨S_)"
  putStrLn "================================================================"
  putStrLn ""
  putStrLn "  Program:  fibS : nat ⇨S nat"
  putStrLn "    = exlS ∘S iterS fibAccStepS ∘S fibInitS"
  putStrLn "  (pure syntax: only _⇨S_ constructors, no escape hatches)"
  putStrLn ""
  putStrLn "  Pipeline for each n:"
  putStrLn "    STEP 1  fibS : nat ⇨S nat          -- program in Ty syntax"
  putStrLn "    STEP 2  ⟦fibS⟧C n = (cost, val)   -- CostM: compute budget"
  putStrLn "    STEP 3  ⟦fibS⟧K n cost = just(val,0) -- TelM: run it"
  putStrLn "            (= runFromSyntax fibS n)"
  putStrLn ""
  -- ── FIBONACCI SEQUENCE TABLE ────────────────────────────────────────────
  putStrLn "  n  │ ⟦fibS⟧C→cost │ ⟦fibS⟧C→val │ runFromSyntax fibS n"
  putStrLn "  ───┼──────────────┼─────────────┼──────────────────────"
  putStrLn (showFibSRow 0)
  putStrLn (showFibSRow 1)
  putStrLn (showFibSRow 2)
  putStrLn (showFibSRow 3)
  putStrLn (showFibSRow 4)
  putStrLn (showFibSRow 5)
  putStrLn (showFibSRow 6)
  putStrLn (showFibSRow 7)
  putStrLn (showFibSRow 8)
  putStrLn (showFibSRow 9)
  putStrLn (showFibSRow 10)
  putStrLn ""
  putStrLn "  Note: cost = n (one tel per iterS step)."
  putStrLn "        val  = fib(n) computed by CostM — no tel spent."
  putStrLn "        run  = TelM with exactly that budget: always finished."
  putStrLn "        Proof: ⟦⟧-adequate fibS (type-checked by Agda)."
  putStrLn ""
  -- ── COMPOSED SYNTAX PROGRAMS ────────────────────────────────────────────
  putStrLn "================================================================"
  putStrLn "  Composed _⇨S_ programs — cost derived from structure"
  putStrLn "================================================================"
  putStrLn ""
  putStrLn "  doubleFibS = fibS ∘S fibS : nat ⇨S nat"
  putStrLn "  Cost = ⟦fibS∘SfibS⟧C n = n + fib(n), auto-computed"
  putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 0)
  putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 3)
  putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 5)
  putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 7)
  putStrLn ""
  putStrLn "  fibPairS = forkS fibS fibS : nat ⇨S (nat ⊗ nat)"
  putStrLn "  Cost = 2*n, auto-computed from fork structure"
  putStrLn (showPairRow 0)
  putStrLn (showPairRow 5)
  putStrLn (showPairRow 10)
  putStrLn ""
  putStrLn "================================================================"
  putStrLn "  Merge sort as a sorting network in _⇨S_ (8 inputs)"
  putStrLn "================================================================"
  putStrLn ""
  putStrLn "  mergeSortS : V8 ⇨S V8"
  putStrLn "    = L6 ∘S L5 ∘S L4 ∘S L3 ∘S L2 ∘S L1   (Batcher odd-even mergesort)"
  putStrLn "    19 compare-and-swaps (casS = forkS minS maxS); each min/max costs 1 tel"
  putStrLn "  ⟦mergeSortS⟧C [7,6,5,4,3,2,1,0] = (38, [0,1,2,3,4,5,6,7])"
  putStrLn "    cost 38 = 19 comparators × 2; sorted result — both refl-verified (mergeSort-test)"
  putStrLn ""
  putStrLn "================================================================"
  putStrLn "  All tel budgets computed from _⇨S_ syntax. No manual input."
  putStrLn "  Correctness: precise + ⟦⟧-adequate (Agda-verified)."
  putStrLn "================================================================"
