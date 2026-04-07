# Telomare — Agda Denotational Design with Auto-Computed Telomere

`telomare.agda` answers one question:

> **How much telomere (gas) does a program need?**
> Answer: compute it via a second categorical interpretation, then run.

The result is a system where no caller ever specifies a tel budget manually.
Every program carries a machine-checked proof that its auto-computed budget
is exactly sufficient.

## Quick start

```bash
nix develop          # enter the devShell (Agda + stdlib in PATH)
agda telomare.agda   # type-check (all 12 sections, all proofs)
agda --compile telomare.agda && ./telomare   # compile and run
```

---

## The Central Idea: Two Interpretations, One Syntax

Following Conal Elliott's **Compiling to Categories** (ICFP 2017):
the same program structure is interpreted in two different categories,
producing two different semantics.

```
A ⇨S B  (typed syntax)
  │
  ├─── ⟦_⟧K ───▶  ⟦A⟧T →K ⟦B⟧T   (execution:  may fail, consumes tel)
  │
  └─── ⟦_⟧C ───▶  ⟦A⟧T →C ⟦B⟧T   (cost:       always succeeds, counts tel)
```

The **adequacy theorem** connects the two:
if `⟦f⟧C a = (cost, val)` then `⟦f⟧K a cost = just (val, 0)`.

This lets `runFromSyntax` run any program without a manual budget.

---

## Fibonacci via `Ty` typed syntax: the complete pipeline

The centrepiece is running fibonacci expressed in the `Ty`/`_⇨S_` typed
syntax with an automatically computed telomere budget.

### STEP 1 — Express the program in `_⇨S_`

```agda
fibS : nat ⇨S nat
```

`nat` is a constructor of the `Ty` data type. `_⇨S_` is the typed syntax
category. `fibS` is fibonacci as a **first-class program value** — no
execution, no budget, just syntax.

### STEP 2 — Compute the budget via `⟦_⟧C` (CostM interpretation)

```agda
fibS-cost : ℕ → ℕ
fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- = n + 1

fibS-val : ℕ → ℕ
fibS-val n = proj₂ (⟦ fibS ⟧C n)    -- = fib(n)
```

`⟦ fibS ⟧C n` uses the **CostM interpretation** (`CostM A = ℕ × A`).
It always succeeds — no tel is spent, no execution happens.
It returns `(n+1, fib(n))`: the required budget and the expected result.

### STEP 3 — Run with that exact budget via `⟦_⟧K` (TelM interpretation)

```agda
fibS-run : ℕ → Result ℕ
fibS-run = runFromSyntax fibS
-- = λ n → run (⟦ fibS ⟧K n) (fibS-cost n)
```

`⟦ fibS ⟧K n` uses the **TelM interpretation** (`TelM A = Tel → Maybe (A × Tel)`).
`runFromSyntax` feeds it exactly the budget from STEP 2.
By the machine-checked theorem `⟦⟧-adequate fibS`, this **always** returns
`finished fib(n) 0` — never `halted`.

### The full fibonacci sequence, from syntax to result

```
================================================================
  Fibonacci sequence expressed in the Ty typed syntax (_⇨S_)
================================================================

  Program:  fibS : nat ⇨S nat
  (nat and _⇨S_ come from the Ty typed syntax category, §12)

  Pipeline for each n:
    STEP 1  fibS : nat ⇨S nat             -- program in Ty syntax
    STEP 2  ⟦fibS⟧C n = (cost, val)      -- CostM: compute budget
    STEP 3  ⟦fibS⟧K n cost = just(val,0) -- TelM: run it
            (= runFromSyntax fibS n)

  n  │ ⟦fibS⟧C→cost │ ⟦fibS⟧C→val │ runFromSyntax fibS n
  ───┼──────────────┼─────────────┼──────────────────────
  fib(0)   cost=⟦fibS⟧C 0=1   val=⟦fibS⟧C 0=0   run=0
  fib(1)   cost=⟦fibS⟧C 1=2   val=⟦fibS⟧C 1=1   run=1
  fib(2)   cost=⟦fibS⟧C 2=3   val=⟦fibS⟧C 2=1   run=1
  fib(3)   cost=⟦fibS⟧C 3=4   val=⟦fibS⟧C 3=2   run=2
  fib(4)   cost=⟦fibS⟧C 4=5   val=⟦fibS⟧C 4=3   run=3
  fib(5)   cost=⟦fibS⟧C 5=6   val=⟦fibS⟧C 5=5   run=5
  fib(6)   cost=⟦fibS⟧C 6=7   val=⟦fibS⟧C 6=8   run=8
  fib(7)   cost=⟦fibS⟧C 7=8   val=⟦fibS⟧C 7=13  run=13
  fib(8)   cost=⟦fibS⟧C 8=9   val=⟦fibS⟧C 8=21  run=21
  fib(9)   cost=⟦fibS⟧C 9=10  val=⟦fibS⟧C 9=34  run=34
  fib(10)  cost=⟦fibS⟧C 10=11 val=⟦fibS⟧C 10=55 run=55

  Note: cost = n+1 (one tel per recursive step).
        val  = fib(n) computed by CostM — no tel spent.
        run  = TelM with exactly that budget: always finished.
        Proof: ⟦⟧-adequate fibS (type-checked by Agda).
```

Column meanings:
- **`⟦fibS⟧C→cost`** — the tel budget, computed by the CostM interpretation of `fibS`
- **`⟦fibS⟧C→val`** — the expected result, also from CostM (no execution involved)
- **`runFromSyntax fibS n`** — TelM run with that budget; always matches the CostM value

### Composed programs: cost derived from `_⇨S_` structure

```
================================================================
  Composed _⇨S_ programs — cost derived from structure
================================================================

  doubleFibS = fibS ∘S fibS : nat ⇨S nat
  Cost = ⟦fibS∘SfibS⟧C n = (n+1) + (fib(n)+1), auto-computed
  (fibS ∘S fibS)(0)  auto-cost=2   result=0
  (fibS ∘S fibS)(3)  auto-cost=7   result=1    -- fib(fib(3))=fib(2)=1
  (fibS ∘S fibS)(5)  auto-cost=12  result=5    -- fib(fib(5))=fib(5)=5
  (fibS ∘S fibS)(7)  auto-cost=22  result=233  -- fib(fib(7))=fib(13)=233

  fibPairS = forkS fibS fibS : nat ⇨S (nat ⊗ nat)
  Cost = 2*(n+1), auto-computed from fork structure
  (forkS fibS fibS)(0)   auto-cost=2   result=(0, 0)
  (forkS fibS fibS)(5)   auto-cost=12  result=(5, 5)
  (forkS fibS fibS)(10)  auto-cost=22  result=(55, 55)
```

The cost of `fibS ∘S fibS` is not hand-calculated — it is derived
automatically from the costs of the two `fibS` subprograms by the
`∘C` composition in the CostM interpretation.

---

## Section-by-section walkthrough

### § 1 — Denotational Design: choosing the models first

Before any code, the file states the two semantic domains:

| Domain | Type | Meaning |
|---|---|---|
| **TelM** | `Tel → Maybe (A × Tel)` | Execution: consume tel, may fail |
| **CostM** | `ℕ × A` | Cost analysis: count tel, always succeeds |

This is Elliott's **Denotational Design** principle: fix the mathematical
model first, derive all operations from it.

`TelM` is `StateT ℕ Maybe` — the standard state+failure monad.
`CostM` is `Writer ℕ` — the standard writer monad for a monoid.
Both are well-studied mathematical objects, so their laws are known in advance.

---

### § 2 — The Execution Monad: TelM

```agda
Tel   : Set
Tel   = ℕ

TelM  : Set → Set
TelM A = Tel → Maybe (A × Tel)
```

Three operations, derived from the homomorphism equations:

| Operation | Definition | Meaning |
|---|---|---|
| `return-tel a g` | `just (a , g)` | Pure value; 0 tel consumed |
| `bind-tel m f g` | `m g >>= λ (a, g') → f a g'` | Thread tel through sequencing |
| `step-tel m zero` | `nothing` | Tel exhausted — graceful halt |
| `step-tel m (suc g)` | `m g` | Consume 1 tel, continue |

`step-tel` is the **telomere drain**: every recursive unfolding costs exactly 1.
Programs are **total functions** — they always return `just` or `nothing`,
they never diverge.

---

### § 3 — The Cost Monad: CostM

```agda
CostM : Set → Set
CostM A = ℕ × A
```

`CostM` mirrors `TelM` operation-for-operation, with different semantics:

| TelM | CostM | Change |
|---|---|---|
| `return-tel a g = just (a, g)` | `return-cost a = (0, a)` | 0 cost |
| `bind-tel m f g = m g >>= …` | `bind-cost (n,a) f = let (m,b) = f a in (n+m, b)` | costs add |
| `step-tel m (suc g) = m g` | `step-cost (n, a) = (suc n, a)` | cost += 1 |

**Key difference:** `step-cost` adds to the counter; it does not subtract from a
budget. `CostM` never fails. This is the "static analysis" dual of `TelM`'s
"dynamic execution".

---

### § 4 — The Two Kleisli Categories

The two monads each give a **Kleisli category** of programs:

```agda
_→K_ : Set → Set → Set
A →K B = A → TelM B       -- execution morphisms (may fail)

_→C_ : Set → Set → Set
A →C B = A → CostM B      -- cost morphisms (always succeed)
```

Both have the same categorical structure:

| Structure | →K | →C |
|---|---|---|
| Identity | `idK = return-tel` | `idC = return-cost` |
| Composition | `(g ∘K f) a = bind-tel (f a) g` | `(g ∘C f) a = bind-cost (f a) g` |
| Fork | `forkK f g a = bind-tel (f a) λ b → bind-tel (g a) λ c → return-tel (b,c)` | `forkC f g a = let (n,vf) = f a; (m,vg) = g a in (n+m, (vf,vg))` |

`forkC` uses a `let`-binding (not `bind-cost` of `return-cost`) so that
`proj₁ (forkC f g a) = n + m` **definitionally** — this is necessary for the
precision proofs to go through by `refl`.

---

### § 5 — Recursion Primitive: fixT

`CostM` needs no recursion primitive — cost functions are structurally recursive.
`TelM` does, because Agda's termination checker cannot see that an unfold of a
self-referential function terminates.

The **fuel pattern** solves this:

```agda
private
  fixT-aux : {S R : Set} → Tel → ((S →K R) → S →K R) → S →K R
  fixT-aux zero    _    _ _ = nothing          -- fuel exhausted → halt
  fixT-aux (suc f) body s   = step-tel (body (fixT-aux f body) s)

fixT : {S R : Set} → ((S →K R) → S →K R) → S →K R
fixT body s g = fixT-aux g body s g
```

- `fixT-aux` recurses structurally on its first argument (the fuel).
- The fuel equals the tel, so each unfolding consumes 1 fuel AND 1 tel.
- Result: recursion depth ≤ initial tel, automatically.

---

### § 4.5 — Type Objects

```agda
data Ty : Set where
  unit : Ty
  nat  : Ty
  bool : Ty
  _⊗_  : Ty → Ty → Ty

⟦_⟧T : Ty → Set
⟦ unit  ⟧T = ⊤
⟦ nat   ⟧T = ℕ
⟦ bool  ⟧T = Bool
⟦ A ⊗ B ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
```

`Ty` is placed before §6 so that §6 can use `FibStateTy : Ty` to express the
fibonacci state type in the type syntax. The typed syntax category `_⇨S_`
remains in §12.

---

### § 6 — Fibonacci in Both Categories

Fibonacci is encoded as iterative accumulation:

**State type in `Ty` syntax:**

```agda
FibStateTy : Ty
FibStateTy = nat ⊗ (nat ⊗ nat)

FibState : Set
FibState = ⟦ FibStateTy ⟧T   -- = ℕ × ℕ × ℕ
```

`FibState` is not written as a raw `ℕ × ℕ × ℕ` — it is **computed** from
`FibStateTy` by the type denotation `⟦_⟧T`. The state type is an expression
of type `Ty`.

**State:** `(counter, fib_k, fib_{k+1})` — initial state `(n, 0, 1)`.  
After `n` steps the counter reaches 0 and `fib_k = fib(n)`.

The two operations on states are defined as Agda helper functions, and
correspond to `_⇨S_` morphisms in §12i:

```agda
-- State transition: (cnt, a, b) → (pred cnt, b, a+b)
-- Corresponds to fibStepS : FibStateTy ⇨S FibStateTy (§12i)
fibStep : FibState → FibState
fibStep (cnt , a , b) = (predℕ cnt , b , a + b)

-- Result extraction: (_, a, _) → a
-- Corresponds to fibExtractS : FibStateTy ⇨S nat (§12i)
fibExtract : FibState → ⟦ nat ⟧T
fibExtract (_ , a , _) = a
```

#### § 6a — Execution (→K)

```agda
private
  fibExecBody : (FibState →K ⟦ nat ⟧T) → FibState →K ⟦ nat ⟧T
  fibExecBody recur s =
    bind-tel (return-tel (isNonZero (proj₁ s))) λ nonzero →
    if nonzero
    then recur (fibStep s)
    else return-tel (fibExtract s)

fib : ⟦ nat ⟧T →K ⟦ nat ⟧T
fib n = fixT fibExecBody (n , 0 , 1)
```

`fibStep` and `fibExtract` are the two key operations — both correspond to
zero-cost `_⇨S_` morphisms (`fibStepS`, `fibExtractS`).
Each unfolding goes through `fixT-aux`, which calls `step-tel`, consuming 1 tel.

#### § 6b — Cost analysis (→C)

```agda
private
  fibCostAux : ⟦ nat ⟧T → ⟦ nat ⟧T → ⟦ nat ⟧T → CostM ⟦ nat ⟧T
  fibCostAux zero    a _ = step-cost (return-cost a)          -- 1 step, result a
  fibCostAux (suc k) a b = step-cost (fibCostAux k b (a + b)) -- 1 + cost of rest

fibCost : ⟦ nat ⟧T →C ⟦ nat ⟧T
fibCost n = fibCostAux n 0 1
```

`fibCostAux` is structurally recursive on the first argument — no fuel trick
needed. It adds 1 (`step-cost`) per level, so `proj₁ (fibCost n) = n + 1`.

**The structural identity:** `fibExecBody` and `fibCostAux` have the same shape.
The only difference is which monad operations are used — `step-tel`/`bind-tel`
vs `step-cost`/`bind-cost`. This is "Compiling to Categories" in action.

---

### § 7 — The Adequacy Theorem

```agda
fib-adequate : ∀ n →
  fib n (proj₁ (fibCost n)) ≡ just (proj₂ (fibCost n) , 0)
```

Reading: run `fib(n)` with the budget from `fibCost` and you get the result
from `fibCost`, with 0 tel remaining.

**Proof:** by induction on `n`. Both sides reduce definitionally — `refl` at
the base case, inductive hypothesis at the step. This works because `fixT-aux`,
`step-tel`, `bind-tel`, and `if-then-else` all reduce definitionally.

---

### § 7.5 — Precision: a Stronger Property for Composition

Adequacy says `exec a cost ≡ just (val, 0)`.
But to prove adequacy for **composed** programs by induction we need more:

```agda
fib-precise : ∀ n extra →
  fib n (proj₁ (fibCost n) + extra) ≡ just (proj₂ (fibCost n) , extra)
```

Reading: run with budget `cost + extra` and exactly `extra` tel remains.
Adequacy is the special case `extra = 0`.

**Why this is needed:** when `f` costs `n` and `g` costs `m`, and we run
`g ∘ f` with budget `(n+m)+extra`, we need `f` to leave exactly `m+extra`
for `g`. Without `extra` in the statement the IH is too weak.

**Proof:** same induction as adequacy — `refl` at `zero`, IH at `suc k`.

---

### § 8 — Programs: Bundling Cost + Execution

```agda
record Program (A B : Set) : Set where
  field
    cost-exec : A →C B
    exec      : A →K B
    adequate  : ∀ a → exec a (proj₁ (cost-exec a)) ≡ just (proj₂ (cost-exec a) , 0)
```

A `Program A B` bundles the two interpretations with a machine-checked proof
that they are consistent. The `adequate` field is the **TCM condition** made
explicit.

```agda
fibProgram : Program ℕ ℕ
fibProgram = record { cost-exec = fibCost ; exec = fib ; adequate = fib-adequate }
```

---

### § 9 — Auto-running Programs

```agda
runAuto : {A B : Set} → Program A B → A → Result B
runAuto prog a = run (Program.exec prog a) (proj₁ (Program.cost-exec prog a))
```

`runAuto` computes the budget from `cost-exec`, then passes it to `exec`.
By `Program.adequate`, the result is always `finished` — never `halted`.

---

### § 10 — Fibonacci Examples with Auto-Computed Telomere

```agda
fib-auto-0  = runAuto fibProgram 0   -- finished 0  0
fib-auto-5  = runAuto fibProgram 5   -- finished 5  0
fib-auto-10 = runAuto fibProgram 10  -- finished 55 0
```

These use `fibProgram` directly (§8). The §12 typed syntax examples below
derive the same results but through the `_⇨S_` layer.

---

### § 12 — Typed Syntax Category

This section adds the `Ty`/`_⇨S_` typed syntax and the full three-step pipeline
described at the top of this document.

#### § 12a. Types — see §4.5

`Ty` and `⟦_⟧T` are defined in §4.5 (before §6). §12 begins with the morphisms.
`Ty` constructors: `unit`, `nat`, `bool`, `_⊗_`.
`⟦_⟧T` maps: `unit→⊤`, `nat→ℕ`, `bool→Bool`, `A⊗B→⟦A⟧T×⟦B⟧T`.

#### § 12b. Morphisms

```agda
data _⇨S_ : Ty → Ty → Set where
  idS   : A ⇨S A
  _∘S_  : B ⇨S C → A ⇨S B → A ⇨S C
  !S    : A ⇨S unit
  forkS : A ⇨S B → A ⇨S C → A ⇨S (B ⊗ C)
  exlS  : (A ⊗ B) ⇨S A
  exrS  : (A ⊗ B) ⇨S B
  addS  : (nat ⊗ nat) ⇨S nat   -- addition, zero cost
  predS : nat ⇨S nat            -- predecessor, zero cost
  fibS  : nat ⇨S nat            -- Fibonacci as a first-class typed morphism
```

`fibS` is the key: **Fibonacci as a value in the typed syntax**, with type
`nat ⇨S nat`.  `addS` and `predS` are the arithmetic primitives needed to
build `fibStepS` (§12i) — the state-transition morphism underlying `fibS`.

#### § 12c–d. Dual Denotations

```agda
⟦_⟧K : A ⇨S B → ⟦A⟧T →K ⟦B⟧T    -- execution
⟦_⟧C : A ⇨S B → ⟦A⟧T →C ⟦B⟧T    -- cost
```

Each constructor maps homomorphically into both categories:

| Syntax | `⟦_⟧K` (execution) | `⟦_⟧C` (cost) |
|---|---|---|
| `idS` | `idK` | `idC` |
| `g ∘S f` | `⟦g⟧K ∘K ⟦f⟧K` | `⟦g⟧C ∘C ⟦f⟧C` |
| `!S` | `λ _ → return-tel tt` | `λ _ → return-cost tt` |
| `forkS f g` | `forkK ⟦f⟧K ⟦g⟧K` | `forkC ⟦f⟧C ⟦g⟧C` |
| `exlS` | `λ (a,_) → return-tel a` | `λ (a,_) → return-cost a` |
| `exrS` | `λ (_,b) → return-tel b` | `λ (_,b) → return-cost b` |
| `addS` | `λ (a,b) → return-tel (a+b)` | `λ (a,b) → return-cost (a+b)` |
| `predS` | `λ n → return-tel (predℕ n)` | `λ n → return-cost (predℕ n)` |
| `fibS` | `fib` | `fibCost` |

The composition row is why composed costs are automatic: `⟦ g ∘S f ⟧C = ⟦g⟧C ∘C ⟦f⟧C`
means `proj₁ (⟦ g ∘S f ⟧C a) = proj₁ (⟦f⟧C a) + proj₁ (⟦g⟧C (proj₂ (⟦f⟧C a)))` —
the costs of `f` and `g` are added, with no manual arithmetic.

#### § 12e. Precision for All Syntax

```agda
Precise : A ⇨S B → Set
Precise f = ∀ a extra →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a) + extra) ≡ just (proj₂ (⟦ f ⟧C a) , extra)

precise : (f : A ⇨S B) → Precise f
```

Proved by induction on `_⇨S_` constructors. The interesting cases:

**`fibS`:** delegates to `fib-precise`.

**`g ∘S f`:** costs add as `n + m`. Budget is `(n+m)+extra`; `f` must leave `m+extra` for `g`.
1. `precise f a (m + extra)` gives `⟦f⟧K a (n + (m+extra)) ≡ just (vf, m+extra)`.
2. `subst (sym (+-assoc n m extra))` rewrites the tel argument from `n+(m+extra)` to `(n+m)+extra`.
3. `cong (λ mx → mx >>= …)` propagates the equality through `bind-tel`.
4. `precise g vf extra` finishes.

**`forkS f g`:** same `+-assoc` trick for `f`'s budget, then two `cong` steps
through the nested `>>=` of `forkK`.

**`idS`, `!S`, `exlS`, `exrS`, `addS`, `predS`:** `refl` — cost is 0, so `0 + extra = extra` definitionally.

#### § 12f–g. Adequacy and Bridge

```agda
⟦⟧-adequate : (f : A ⇨S B) → ∀ a →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a)) ≡ just (proj₂ (⟦ f ⟧C a) , 0)
⟦⟧-adequate f a =
  subst (λ tel → ⟦ f ⟧K a tel ≡ …) (+-identityʳ (proj₁ (⟦ f ⟧C a))) (precise f a 0)

fromSyntax    : A ⇨S B → Program ⟦A⟧T ⟦B⟧T
runFromSyntax : A ⇨S B → ⟦A⟧T → Result ⟦B⟧T
```

`fromSyntax f` packages `⟦f⟧C`, `⟦f⟧K`, and `⟦⟧-adequate f` into a `Program`.
`runFromSyntax` calls `runAuto` on that — the budget is derived entirely from
the syntax.

#### § 12h. Fibonacci sequence via Ty syntax (the three-step pipeline in Agda)

```agda
-- STEP 2: tel budget from CostM interpretation
fibS-cost : ℕ → ℕ
fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- = n + 1

-- STEP 2: expected value from CostM (no execution involved)
fibS-val : ℕ → ℕ
fibS-val n = proj₂ (⟦ fibS ⟧C n)    -- = fib(n)

-- STEP 3: TelM run with the CostM budget
fibS-run : ℕ → Result ℕ
fibS-run = runFromSyntax fibS

-- The full sequence:
fibS-0  : Result ℕ ; fibS-0  = fibS-run 0   -- finished 0  0
fibS-1  : Result ℕ ; fibS-1  = fibS-run 1   -- finished 1  0
-- ...
fibS-10 : Result ℕ ; fibS-10 = fibS-run 10  -- finished 55 0

-- Composed program: fib(fib(n)), cost derived from composition
doubleFibS : nat ⇨S nat
doubleFibS = fibS ∘S fibS

-- Fork: (fib(n), fib(n)), cost = 2*(n+1)
fibPairS : nat ⇨S (nat ⊗ nat)
fibPairS = forkS fibS fibS
```

#### § 12i. Fibonacci step and extract as `_⇨S_` morphisms

The internal operations of `fib` are themselves `_⇨S_` morphisms, built
entirely from `addS`, `predS`, `exlS`, `exrS`, `forkS`:

```agda
-- State transition: (cnt, a, b) → (pred cnt, b, a+b)
fibStepS : FibStateTy ⇨S FibStateTy
fibStepS = forkS (predS ∘S exlS)
                 (forkS (exrS ∘S exrS)
                        (addS ∘S forkS (exlS ∘S exrS) (exrS ∘S exrS)))

-- Result extraction: (_, a, _) → a
fibExtractS : FibStateTy ⇨S nat
fibExtractS = exlS ∘S exrS
```

`fibStepS` and `fibExtractS` connect back to §6:
- `⟦ fibStepS ⟧K s = return-tel (fibStep s)` definitionally
- `⟦ fibExtractS ⟧K s = return-tel (fibExtract s)` definitionally

This completes the picture: every operation inside `fib` is expressible as a
`_⇨S_` morphism over `Ty` types. `fib` itself wraps these in `fixT` for
the recursion, which cannot be a simple morphism.

---

## Proof architecture

```
fib-precise-aux   ← structural induction on ℕ (base: refl, step: IH)
     │
     └── fib-precise : ∀ n extra → fib n (cost+extra) ≡ just (val, extra)
              │
              └── precise : (f : A ⇨S B) → Precise f   ← induction on _⇨S_
                       │
                       └── ⟦⟧-adequate : ⟦f⟧K a cost ≡ just (val, 0)
                                │
                                └── Program.adequate   (field in Program record)
                                         │
                                         └── runAuto always returns finished
                                                  │
                                                  └── runFromSyntax fibS-run fibS-0 … fibS-10
```

Every arrow is a propositional equality proof in Agda's type theory.
The root `fib-precise-aux` proof is two lines; every higher level adds at most
one `subst` + `trans` + `cong`.

---

## Key design decisions

| Decision | Why |
|---|---|
| `CostM = ℕ × A` (Writer) not `TelM` | Cost analysis must always succeed; `nothing` would make composition unsound |
| `forkC` via `let` not `bind-cost` | `bind-cost` of `return-cost` gives cost `n + (m + 0)`, not definitionally `n + m`; precision proofs need the latter |
| Precision instead of adequacy alone | Adequacy `exec cost ≡ just (val, 0)` is not composable; precision `exec (cost+extra) ≡ just (val, extra)` is |
| `fixT-aux` fuel = tel | Ties fuel depletion to tel depletion; the bound is tight, not conservative |
| `fibCostAux` as a separate function | Agda's termination checker cannot see `(k, b, a+b)` as structurally smaller than `(suc k, a, b)` in a tuple; a separate `ℕ` argument makes the recursion obvious |

---

## Relation to `telomare-backwards.agda`

`telomare-backwards.agda` (see `Agda-README-tel-backwards.md`) is an earlier
denotational design that uses [Felix](https://github.com/conal/felix) to
machine-check the functor laws. It has **one** denotation `⟦_⟧ : A ⇨S B → ⟦A⟧T →K ⟦B⟧T`
into the execution category only.

`telomare.agda` adds:
- A **second** denotation `⟦_⟧C` into the cost category
- The **adequacy** and **precision** theorems connecting them
- `fibS-cost`, `fibS-val`, `fibS-run` — the explicit three-step pipeline
- `Program`, `runAuto`, `runFromSyntax` — the user-facing interface
- No Felix dependency (simpler build, same core ideas)

The two files are complementary: `telomare-backwards.agda` shows how to hook
into Felix's categorical infrastructure; `telomare.agda` shows how to make the
tel budget self-computing with a machine-checked correctness proof.

---

## File structure (`telomare.agda`)

| Section | Content |
|---|---|
| §1 | Denotational design overview (comments) |
| §2 | `TelM` — execution monad (`return-tel`, `bind-tel`, `step-tel`) |
| §3 | `CostM` — cost monad (`return-cost`, `bind-cost`, `step-cost`) |
| §4 | `_→K_`, `_→C_`, `idK/C`, `∘K/C`, `forkK/C` |
| §4.5 | `Ty` (with `bool`), `⟦_⟧T` — type objects and denotation |
| §5 | `fixT-aux`, `fixT` — recursion primitive (fuel pattern) |
| §6 | `FibStateTy : Ty`, `FibState = ⟦FibStateTy⟧T`, `fibStep`, `fibExtract`, `fib` (→K), `fibCost`/`fibCostAux` (→C) |
| §7 | `fib-adequate` — adequacy theorem |
| §7.5 | `fib-precise` — precision theorem (stronger, needed for composition) |
| §8 | `Program` record, `fibProgram` |
| §9 | `Result`, `run`, `runAuto` |
| §10 | `fib-auto-*` — fibonacci sequence via `fibProgram` |
| §12 | `_⇨S_` (with `addS`, `predS`), `⟦_⟧K`, `⟦_⟧C`, `Precise`, `precise`, `⟦⟧-adequate`, `fromSyntax`, `runFromSyntax`, `fibS-cost/val/run`, `fibS-0..10`, `doubleFibS`, `fibPairS`, `fibStepS`, `fibExtractS` |
| §11 | `main` — IO output showing the full pipeline |

---

## Key references

- Conal Elliott, *Denotational Design with Type Class Morphisms*, Haskell Symposium 2009
- Conal Elliott, *Compiling to Categories*, ICFP 2017
- Conal Elliott, *Timely Computation* — motivation for the telomere/gas model
