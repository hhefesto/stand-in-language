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

open import Data.Nat             using (ℕ; zero; suc; _+_)
open import Data.Maybe           using (Maybe; just; nothing; _>>=_)
open import Data.Product         using (_×_; _,_; proj₁; proj₂)
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
-- Placed here (before §6) so that §6 (Fibonacci) can define FibStateTy : Ty,
-- making FibState = ⟦ FibStateTy ⟧T an explicit Ty expression.
-- The typed syntax category _⇨S_ is defined later in §12.

data Ty : Set where
  unit : Ty
  nat  : Ty
  bool : Ty
  _⊗_  : Ty → Ty → Ty

infixl 5 _⊗_

⟦_⟧T : Ty → Set
⟦ unit  ⟧T = ⊤
⟦ nat   ⟧T = ℕ
⟦ bool  ⟧T = Bool
⟦ A ⊗ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T

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

-- ─────────────────────────────────────────────────────────────────────────────
-- § 6.  FIBONACCI IN BOTH CATEGORIES
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Fibonacci is the canonical example demonstrating "Compiling to Categories".
--
-- State: (counter, fib_k, fib_{k+1})    Initial state: (n, 0, 1)
-- After n recursive steps → (0, fib(n), fib(n+1))
--
-- THE STRUCTURAL IDENTITY:
-- The fibonacci body has the SAME structure in both categories.
-- The only difference is WHICH monad operations are used:
--
--   Execution (→K):            Cost analysis (→C):
--   ─────────────────          ─────────────────────
--   base: return-tel a         base: step-cost (return-cost a)
--   step: step-tel via fixT    step: step-cost (fibCostFn s')
--
-- In →K, step-tel is hidden inside fixT-aux.
-- In →C, step-cost is explicit — each level adds 1.
-- Result: both track the same count, proving they are consistent.

-- FibStateTy expresses the state type in the Ty syntax (§4.5).
-- FibState is computed by the type denotation ⟦_⟧T.
-- In §12, fibStepS : FibStateTy ⇨S FibStateTy and
--         fibExtractS : FibStateTy ⇨S nat are the categorical morphisms
-- corresponding to the helpers below.
FibStateTy : Ty
FibStateTy = nat ⊗ (nat ⊗ nat)

FibState : Set
FibState = ⟦ FibStateTy ⟧T   -- = ⟦ nat ⟧T × (⟦ nat ⟧T × ⟦ nat ⟧T) = ℕ × ℕ × ℕ

private
  isNonZero : ⟦ nat ⟧T → Bool
  isNonZero zero    = false
  isNonZero (suc _) = true

  -- pred on ⟦ nat ⟧T; used in fibStep below and as denotation of predS in §12.
  predℕ : ⟦ nat ⟧T → ⟦ nat ⟧T
  predℕ zero    = zero
  predℕ (suc k) = k

  -- State transition: (cnt, a, b) → (pred cnt, b, a+b)
  -- This is the Agda-level counterpart of fibStepS : FibStateTy ⇨S FibStateTy (§12).
  -- ⟦ fibStepS ⟧K s = return-tel (fibStep s)   (definitionally, zero cost)
  fibStep : FibState → FibState
  fibStep (cnt , a , b) = (predℕ cnt , b , a + b)

  -- Result extraction: (_, a, _) → a
  -- This is the Agda-level counterpart of fibExtractS : FibStateTy ⇨S nat (§12).
  -- fibExtractS = exlS ∘S exrS, so ⟦ fibExtractS ⟧K (_, a, _) = return-tel a
  fibExtract : FibState → ⟦ nat ⟧T
  fibExtract (_ , a , _) = a

-- §6a.  Fibonacci in →K (execution, may fail if tel runs out)
--
-- The fixT body uses fibStep and fibExtract — both are denotations of
-- _⇨S_ morphisms (fibStepS, fibExtractS) defined in §12.
-- Each unfolding costs 1 tel (via step-tel inside fixT-aux).

private
  fibExecBody : (FibState →K ⟦ nat ⟧T) → FibState →K ⟦ nat ⟧T
  fibExecBody recur s =
    bind-tel (return-tel (isNonZero (proj₁ s))) λ nonzero →
    if nonzero
    then recur (fibStep s)
    else return-tel (fibExtract s)

fib : ⟦ nat ⟧T →K ⟦ nat ⟧T
fib n = fixT fibExecBody (n , 0 , 1)

-- §6b.  Fibonacci in →C (cost analysis, always succeeds)
--
-- Direct structural recursion on the counter — no fuel trick needed!
-- Returns (cost, result):
--   • cost = number of tel units fib(n) needs  = n + 1
--   • result = fib(n) (the actual fibonacci value)
--
-- Note the structural identity with fibExecBody:
--   base (cnt=0): step-cost (return-cost a)     mirrors  return-tel a + 1 step-tel
--   step (cnt>0): step-cost (fibCostFn s')      mirrors  recur s'    + 1 step-tel
-- The step-tel is buried in fixT-aux for →K; explicit step-cost here.
--
-- Implementation note: we take (counter, a, b) as separate ℕ arguments so
-- that Agda sees structural recursion on the first argument (the counter).
-- Tupling them into FibState would obscure this for the termination checker.

private
  fibCostAux : ⟦ nat ⟧T → ⟦ nat ⟧T → ⟦ nat ⟧T → CostM ⟦ nat ⟧T
  fibCostAux zero    a _ = step-cost (return-cost a)            -- base: cost 1, result a
  fibCostAux (suc k) a b = step-cost (fibCostAux k b (a + b))  -- 1 + cost of rest

fibCostFn : FibState →C ⟦ nat ⟧T
fibCostFn (n , a , b) = fibCostAux n a b

-- The cost and result of fib(n):
fibCost : ⟦ nat ⟧T →C ⟦ nat ⟧T
fibCost n = fibCostAux n 0 1

-- Quick facts (by computation):
--   proj₁ (fibCost 0)  = 1   proj₂ (fibCost 0)  = 0
--   proj₁ (fibCost 1)  = 2   proj₂ (fibCost 1)  = 1
--   proj₁ (fibCost 5)  = 6   proj₂ (fibCost 5)  = 5
--   proj₁ (fibCost 10) = 11  proj₂ (fibCost 10) = 55
-- Cost(n) = n + 1; Result = fib(n).

-- ─────────────────────────────────────────────────────────────────────────────
-- § 7.  THE ADEQUACY THEOREM
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The core theorem connecting TelM (execution) and CostM (cost analysis):
--
--   ∀ n → fib n (proj₁ (fibCost n)) ≡ just (proj₂ (fibCost n) , 0)
--
-- Reading: running fib(n) with EXACTLY the cost-computed tel budget
-- always succeeds and produces the cost-computed result with 0 tel remaining.
--
-- Proof: by induction on n, both sides reduce definitionally.
-- The key step: the suc case reduces to the inductive hypothesis
-- because fixT-aux, step-tel, bind-tel, and if-then-else all reduce
-- definitionally in Agda's type theory.
--
-- This is the payoff of the denotational design:
-- The TWO interpretations (TelM and CostM) are PROVABLY CONSISTENT.

private
  -- Lemma: adequacy for arbitrary starting state with counter n, acc a, b
  -- Uses fibCostAux directly (structurally clear: recurse on n).
  fib-adequate-aux : ∀ (n a b : ℕ) →
    fixT-aux (proj₁ (fibCostAux n a b))
             fibExecBody
             (n , a , b)
             (proj₁ (fibCostAux n a b))
    ≡ just (proj₂ (fibCostAux n a b) , 0)
  -- Base: fibCostAux 0 a b = (1, a). Both sides reduce to just (a, 0). ✓
  fib-adequate-aux zero    a b = refl
  -- Step: fibCostAux (suc k) a b = step-cost (fibCostAux k b (a+b)).
  -- The goal reduces definitionally to the IH fib-adequate-aux k b (a+b). ✓
  fib-adequate-aux (suc k) a b = fib-adequate-aux k b (a + b)

-- Main adequacy theorem for fib:
fib-adequate : ∀ n →
  fib n (proj₁ (fibCost n)) ≡ just (proj₂ (fibCost n) , 0)
fib-adequate n = fib-adequate-aux n 0 1

-- ─────────────────────────────────────────────────────────────────────────────
-- § 7.5  PRECISION: A STRONGER PROPERTY NEEDED FOR COMPOSITION
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Adequacy says: exec a cost ≡ just (val, 0).
-- But for composition (g ∘ f), we need more:
-- When f costs n and g costs m, and we give (g ∘ f) a budget of n+m+extra,
-- then f must consume exactly n and leave m+extra for g.
--
-- This "precision" property is:
--   exec a (cost + extra) ≡ just (val, extra)   for any extra ℕ
--
-- Adequacy is the special case extra = 0.
-- Precision is proved by exactly the same induction as adequacy.

private
  fib-precise-aux : ∀ (n a b extra : ℕ) →
    fixT-aux (proj₁ (fibCostAux n a b) + extra) fibExecBody (n , a , b)
             (proj₁ (fibCostAux n a b) + extra)
    ≡ just (proj₂ (fibCostAux n a b) , extra)
  fib-precise-aux zero    a b extra = refl   -- (1+extra), reduces to just(a,extra) ✓
  fib-precise-aux (suc k) a b extra = fib-precise-aux k b (a + b) extra

-- Precision for fib: running with cost+extra leaves exactly extra
fib-precise : ∀ n extra →
  fib n (proj₁ (fibCost n) + extra) ≡ just (proj₂ (fibCost n) , extra)
fib-precise n extra = fib-precise-aux n 0 1 extra

-- ─────────────────────────────────────────────────────────────────────────────
-- § 8.  PROGRAMS: BUNDLING COST AND EXECUTION
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

-- The fibonacci Program: cost + execution + adequacy, all bundled.
fibProgram : Program ℕ ℕ
fibProgram = record
  { cost-exec = fibCost
  ; exec      = fib
  ; adequate  = fib-adequate
  }

-- ─────────────────────────────────────────────────────────────────────────────
-- § 9.  AUTO-RUNNING PROGRAMS
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

-- By fib-adequate (and Program.adequate in general), runAuto always
-- returns finished — never halted. The tel budget is exactly right.

-- ─────────────────────────────────────────────────────────────────────────────
-- § 10.  FIBONACCI EXAMPLES WITH AUTO-COMPUTED TELOMERE
-- ─────────────────────────────────────────────────────────────────────────────
--
-- No manual tel specification needed!
-- Each example computes its own cost and runs with exactly that budget.
--
-- By fib-adequate:   runAuto fibProgram n ≡ finished (proj₂ (fibCost n)) 0
-- i.e.:              runAuto fibProgram n ≡ finished fib(n) 0   always

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

-- ─────────────────────────────────────────────────────────────────────────────
-- § 12.  TYPED SYNTAX CATEGORY
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

-- §12a. Type objects — see §4.5 for Ty, ⟦_⟧T (moved there so §6 can use them).
--       Ty has constructors: unit, nat, bool, _⊗_
--       ⟦_⟧T : Ty → Set   (unit→⊤, nat→ℕ, bool→Bool, A⊗B→⟦A⟧T×⟦B⟧T)

-- §12b. Morphisms (typed programs as categorical arrows)
data _⇨S_ : Ty → Ty → Set where
  idS   : {A : Ty}     → A ⇨S A
  _∘S_  : {A B C : Ty} → B ⇨S C → A ⇨S B → A ⇨S C
  !S    : {A : Ty}     → A ⇨S unit
  forkS : {A B C : Ty} → A ⇨S B → A ⇨S C → A ⇨S (B ⊗ C)
  exlS  : {A B : Ty}   → (A ⊗ B) ⇨S A
  exrS  : {A B : Ty}   → (A ⊗ B) ⇨S B
  addS  :                 (nat ⊗ nat) ⇨S nat      -- addition: ⟦A⟧T×⟦B⟧T→ℕ
  predS :                 nat ⇨S nat               -- predecessor: pred n
  fibS  :                 nat ⇨S nat

infixr 2 _⇨S_
infixr 9 _∘S_

-- §12c. Execution denotation: A ⇨S B → ⟦A⟧T →K ⟦B⟧T
⟦_⟧K : {A B : Ty} → A ⇨S B → ⟦ A ⟧T →K ⟦ B ⟧T
⟦ idS       ⟧K = idK
⟦ g ∘S f    ⟧K = ⟦ g ⟧K ∘K ⟦ f ⟧K
⟦ !S        ⟧K _ = return-tel tt
⟦ forkS f g ⟧K = forkK ⟦ f ⟧K ⟦ g ⟧K
⟦ exlS      ⟧K (a , _) = return-tel a
⟦ exrS      ⟧K (_ , b) = return-tel b
⟦ addS      ⟧K (a , b) = return-tel (a + b)
⟦ predS     ⟧K n       = return-tel (predℕ n)
⟦ fibS      ⟧K = fib

-- §12d. Cost denotation: A ⇨S B → ⟦A⟧T →C ⟦B⟧T
⟦_⟧C : {A B : Ty} → A ⇨S B → ⟦ A ⟧T →C ⟦ B ⟧T
⟦ idS       ⟧C = idC
⟦ g ∘S f    ⟧C = ⟦ g ⟧C ∘C ⟦ f ⟧C
⟦ !S        ⟧C _ = return-cost tt
⟦ forkS f g ⟧C = forkC ⟦ f ⟧C ⟦ g ⟧C
⟦ exlS      ⟧C (a , _) = return-cost a
⟦ exrS      ⟧C (_ , b) = return-cost b
⟦ addS      ⟧C (a , b) = return-cost (a + b)
⟦ predS     ⟧C n       = return-cost (predℕ n)
⟦ fibS      ⟧C = fibCost

-- §12e. Precision: the key property connecting ⟦_⟧K and ⟦_⟧C
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
-- fibS: exactly the fib-precise lemma proved in §7.5
precise fibS        n         extra = fib-precise n extra
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

-- §12f. Adequacy for all syntax (from precision at extra = 0)
--
-- Running ⟦f⟧K with the CostM-computed budget always succeeds.
-- Derived from precision by setting extra = 0 and using +-identityʳ.
⟦⟧-adequate : {A B : Ty} → (f : A ⇨S B) → ∀ a →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a)) ≡ just (proj₂ (⟦ f ⟧C a) , 0)
⟦⟧-adequate f a =
  subst (λ tel → ⟦ f ⟧K a tel ≡ just (proj₂ (⟦ f ⟧C a) , 0))
        (+-identityʳ (proj₁ (⟦ f ⟧C a)))
        (precise f a 0)

-- §12g. Bridge: syntax → Program → runAuto
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

-- §12h. Fibonacci sequence expressed and evaluated via Ty typed syntax
--
-- The complete pipeline, made explicit as named Agda definitions:
--
--   STEP 1: Express the program in the _⇨S_ typed syntax category.
--           fibS : nat ⇨S nat
--           (already defined above as a constructor of _⇨S_)
--
--   STEP 2: Interpret into CostM via ⟦_⟧C.
--           fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- tel budget needed
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
fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- = n + 1

-- STEP 2 (also): the value, computed purely by CostM (no tel, no execution)
fibS-val : ℕ → ℕ
fibS-val n = proj₂ (⟦ fibS ⟧C n)    -- = fib(n)

-- STEP 3: run with the auto-computed budget
fibS-run : ℕ → Result ℕ
fibS-run = runFromSyntax fibS

-- The fibonacci sequence (fib(0) … fib(10)) via Ty typed syntax.
-- Each entry: budget from fibS-cost, result from fibS-run.
-- Note: identical results to the §10 examples, but derived from _⇨S_ syntax.
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
-- Cost = (n+1) + (fib(n)+1), derived by ⟦ fibS ∘S fibS ⟧C
doubleFibS : nat ⇨S nat
doubleFibS = fibS ∘S fibS

-- Fork: compute (fib(n), fib(n)) — runs fib twice, total cost = 2*(n+1)
fibPairS : nat ⇨S (nat ⊗ nat)
fibPairS = forkS fibS fibS

-- §12i. Fibonacci step and extract as _⇨S_ morphisms
--
-- The fib state (cnt, a, b) : ⟦ FibStateTy ⟧T = ⟦ nat ⊗ (nat ⊗ nat) ⟧T
-- is processed by two categorical morphisms:
--
--   fibStepS    : FibStateTy ⇨S FibStateTy
--     (cnt, a, b) ↦ (pred cnt, b, a+b)
--     built from addS, predS, exlS, exrS, forkS  — all zero-cost primitives
--     ⟦ fibStepS ⟧K s = return-tel (fibStep s)   (definitionally)
--
--   fibExtractS : FibStateTy ⇨S nat
--     (_, a, _) ↦ a   (= exlS ∘S exrS)
--     ⟦ fibExtractS ⟧K s = return-tel (fibExtract s)  (definitionally)
--
-- These show explicitly that fib's internal operations are Ty morphisms.

-- State transition: (cnt, a, b) → (pred cnt, b, a+b)
-- forkS picks pred(cnt) and the pair (b, a+b):
--   first  component: predS ∘S exlS           — pred of counter
--   second component: forkS (exrS ∘S exrS)    — b (second of second)
--                          (addS ∘S forkS (exlS ∘S exrS) (exrS ∘S exrS))
--                                              — a+b (first⊕second of second)
fibStepS : FibStateTy ⇨S FibStateTy
fibStepS = forkS (predS ∘S exlS)
                 (forkS (exrS ∘S exrS)
                        (addS ∘S forkS (exlS ∘S exrS) (exrS ∘S exrS)))

-- Result extraction: (_, a, _) → a  (first component of the second pair)
fibExtractS : FibStateTy ⇨S nat
fibExtractS = exlS ∘S exrS

-- ─────────────────────────────────────────────────────────────────────────────
-- § 11.  MAIN: DEMONSTRATE AUTO-COMPUTED TELOMERE
-- ─────────────────────────────────────────────────────────────────────────────

open import IO            using (IO; putStrLn; Main)
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
main = IO.run
  (-- ── HEADER ──────────────────────────────────────────────────────────────
   putStrLn "================================================================" IO.>>
   putStrLn "  Fibonacci sequence expressed in the Ty typed syntax (_⇨S_)"   IO.>>
   putStrLn "================================================================" IO.>>
   putStrLn ""                                                                 IO.>>
   putStrLn "  Program:  fibS : nat ⇨S nat"                                   IO.>>
   putStrLn "  (nat and _⇨S_ come from the Ty typed syntax category, §12)"   IO.>>
   putStrLn ""                                                                 IO.>>
   putStrLn "  Pipeline for each n:"                                           IO.>>
   putStrLn "    STEP 1  fibS : nat ⇨S nat          -- program in Ty syntax"  IO.>>
   putStrLn "    STEP 2  ⟦fibS⟧C n = (cost, val)   -- CostM: compute budget"  IO.>>
   putStrLn "    STEP 3  ⟦fibS⟧K n cost = just(val,0) -- TelM: run it"        IO.>>
   putStrLn "            (= runFromSyntax fibS n)"                             IO.>>
   putStrLn ""                                                                 IO.>>
   -- ── FIBONACCI SEQUENCE TABLE ────────────────────────────────────────────
   putStrLn "  n  │ ⟦fibS⟧C→cost │ ⟦fibS⟧C→val │ runFromSyntax fibS n" IO.>>
   putStrLn "  ───┼──────────────┼─────────────┼──────────────────────" IO.>>
   putStrLn (showFibSRow 0)  IO.>>
   putStrLn (showFibSRow 1)  IO.>>
   putStrLn (showFibSRow 2)  IO.>>
   putStrLn (showFibSRow 3)  IO.>>
   putStrLn (showFibSRow 4)  IO.>>
   putStrLn (showFibSRow 5)  IO.>>
   putStrLn (showFibSRow 6)  IO.>>
   putStrLn (showFibSRow 7)  IO.>>
   putStrLn (showFibSRow 8)  IO.>>
   putStrLn (showFibSRow 9)  IO.>>
   putStrLn (showFibSRow 10) IO.>>
   putStrLn ""               IO.>>
   putStrLn "  Note: cost = n+1 (one tel per recursive step)."         IO.>>
   putStrLn "        val  = fib(n) computed by CostM — no tel spent."  IO.>>
   putStrLn "        run  = TelM with exactly that budget: always finished." IO.>>
   putStrLn "        Proof: ⟦⟧-adequate fibS (type-checked by Agda)."  IO.>>
   putStrLn ""                                                                 IO.>>
   -- ── COMPOSED SYNTAX PROGRAMS ────────────────────────────────────────────
   putStrLn "================================================================" IO.>>
   putStrLn "  Composed _⇨S_ programs — cost derived from structure"          IO.>>
   putStrLn "================================================================" IO.>>
   putStrLn ""                                                                 IO.>>
   putStrLn "  doubleFibS = fibS ∘S fibS : nat ⇨S nat"                       IO.>>
   putStrLn "  Cost = ⟦fibS∘SfibS⟧C n = (n+1) + (fib(n)+1), auto-computed"  IO.>>
   putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 0)  IO.>>
   putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 3)  IO.>>
   putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 5)  IO.>>
   putStrLn (showComposedRow doubleFibS "fibS ∘S fibS" 7)  IO.>>
   putStrLn ""                                                                 IO.>>
   putStrLn "  fibPairS = forkS fibS fibS : nat ⇨S (nat ⊗ nat)"              IO.>>
   putStrLn "  Cost = 2*(n+1), auto-computed from fork structure"             IO.>>
   putStrLn (showPairRow 0)  IO.>>
   putStrLn (showPairRow 5)  IO.>>
   putStrLn (showPairRow 10) IO.>>
   putStrLn ""                                                                 IO.>>
   putStrLn "================================================================" IO.>>
   putStrLn "  All tel budgets computed from _⇨S_ syntax. No manual input."  IO.>>
   putStrLn "  Correctness: precise + ⟦⟧-adequate (Agda-verified)."          IO.>>
   putStrLn "================================================================")
