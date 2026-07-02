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
agda telomare.agda   # type-check (all sections, all proofs)
agda --compile telomare.agda && ./telomare   # compile and run
```

---

## The Central Idea: Many Interpretations, One Syntax

Following Conal Elliott's **Compiling to Categories** (ICFP 2017):
the same program structure is interpreted in several different categories,
each producing a different semantics. telomare now has **three**:

```
A ⇨S B  (typed syntax)
  │
  ├─── ⟦_⟧K  ───▶  ⟦A⟧T →K ⟦B⟧T    (execution:    may fail, consumes tel)
  │
  ├─── ⟦_⟧C  ───▶  ⟦A⟧T →C ⟦B⟧T    (cost:         always succeeds, counts tel)
  │
  └─── ⟦_⟧WS ───▶  ⟦A⟧T → (work,span)×⟦B⟧T   (parallel cost: forkS takes max)
```

The **adequacy theorem** connects the first two:
if `⟦f⟧C a = (cost, val)` then `⟦f⟧K a cost = just (val, 0)`.
This lets `runFromSyntax` run any program without a manual budget.

The third interpretation (`⟦_⟧WS`, §8g) computes **work** (= the sequential tel
cost) and **span** (= parallel critical-path depth) — the cost a parallel runtime
like HVM2 could realize. (See `PARALLEL.md` and `ctc/HVM-BACKEND.md`.)

The syntax is now **bicartesian with lists**: beyond products it has coproducts
(`_⊕_`, `caseS`) for data-dependent branching and a recursive list type
(`listT`), so genuinely recursive programs (e.g. `lengthS`, and in principle a
list merge sort) are expressible — each still carrying a machine-checked cost.

---

## Fibonacci via `Ty` typed syntax: the complete pipeline

The centrepiece is running fibonacci expressed purely in the `Ty`/`_⇨S_`
typed syntax with an automatically computed telomere budget.
`fibS` is assembled from `_⇨S_` constructors only — no host-language
functions, no escape hatches.

### STEP 1 — Express the program in `_⇨S_` (pure syntax)

```agda
-- State object in Ty syntax
FibStateTy : Ty
FibStateTy = nat ⊗ (nat ⊗ nat)

FibState : Set
FibState = ⟦ FibStateTy ⟧T

-- Accumulator step: (a, b) ↦ (b, a+b)
fibAccStepS : (nat ⊗ nat) ⇨S (nat ⊗ nat)
fibAccStepS = forkS exrS (addS ∘S forkS exlS exrS)

-- Initial accumulator from n: n ↦ (n, (0, 1))
fibInitS : nat ⇨S FibStateTy
fibInitS = forkS idS (forkS (constS 0) (constS 1))

-- Fibonacci: iterate fibAccStepS n times on (0,1), extract first
fibS : nat ⇨S nat
fibS = exlS ∘S iterS fibAccStepS ∘S fibInitS
```

`nat`, `_⊗_` are constructors of `Ty`. `_⇨S_` is the typed syntax category.
`fibS` is fibonacci as a **first-class program value** whose every head
symbol is a `_⇨S_` constructor: `exlS`, `∘S`, `iterS`, `forkS`, `exrS`,
`addS`, `constS`, `idS`. No host-level Agda functions involved.

`iterS : (A ⇨S A) → (nat ⊗ A) ⇨S A` is the new bounded-iteration
primitive — it applies a step morphism exactly `n` times, consuming
1 tel per iteration. The counter `n` IS the budget; totality is manifest.

### STEP 2 — Compute the budget via `⟦_⟧C` (CostM interpretation)

```agda
fibS-cost : ℕ → ℕ
fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- = n

fibS-val : ℕ → ℕ
fibS-val n = proj₂ (⟦ fibS ⟧C n)    -- = fib(n)
```

`⟦ fibS ⟧C n` uses the **CostM interpretation** (`CostM A = ℕ × A`).
It always succeeds — no tel is spent, no execution happens.
It returns `(n, fib(n))`: the required budget and the expected result.
Cost = n because `iterS` makes exactly n iterations.

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
    = exlS ∘S iterS fibAccStepS ∘S fibInitS
  (pure syntax: only _⇨S_ constructors, no escape hatches)

  Pipeline for each n:
    STEP 1  fibS : nat ⇨S nat             -- program in Ty syntax
    STEP 2  ⟦fibS⟧C n = (cost, val)      -- CostM: compute budget
    STEP 3  ⟦fibS⟧K n cost = just(val,0) -- TelM: run it
            (= runFromSyntax fibS n)

  n  │ ⟦fibS⟧C→cost │ ⟦fibS⟧C→val │ runFromSyntax fibS n
  ───┼──────────────┼─────────────┼──────────────────────
  fib(0)   cost=⟦fibS⟧C 0=0  val=⟦fibS⟧C 0=0   run=0
  fib(1)   cost=⟦fibS⟧C 1=1  val=⟦fibS⟧C 1=1   run=1
  fib(2)   cost=⟦fibS⟧C 2=2  val=⟦fibS⟧C 2=1   run=1
  fib(3)   cost=⟦fibS⟧C 3=3  val=⟦fibS⟧C 3=2   run=2
  fib(4)   cost=⟦fibS⟧C 4=4  val=⟦fibS⟧C 4=3   run=3
  fib(5)   cost=⟦fibS⟧C 5=5  val=⟦fibS⟧C 5=5   run=5
  fib(6)   cost=⟦fibS⟧C 6=6  val=⟦fibS⟧C 6=8   run=8
  fib(7)   cost=⟦fibS⟧C 7=7  val=⟦fibS⟧C 7=13  run=13
  fib(8)   cost=⟦fibS⟧C 8=8  val=⟦fibS⟧C 8=21  run=21
  fib(9)   cost=⟦fibS⟧C 9=9  val=⟦fibS⟧C 9=34  run=34
  fib(10)  cost=⟦fibS⟧C 10=10 val=⟦fibS⟧C 10=55 run=55

  Note: cost = n (one tel per iterS step).
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
  Cost = ⟦fibS∘SfibS⟧C n = n + fib(n), auto-computed
  (fibS ∘S fibS)(0)  auto-cost=0   result=0
  (fibS ∘S fibS)(3)  auto-cost=5   result=1    -- fib(fib(3))=fib(2)=1
  (fibS ∘S fibS)(5)  auto-cost=10  result=5    -- fib(fib(5))=fib(5)=5
  (fibS ∘S fibS)(7)  auto-cost=20  result=233  -- fib(fib(7))=fib(13)=233

  fibPairS = forkS fibS fibS : nat ⇨S (nat ⊗ nat)
  Cost = 2*n, auto-computed from fork structure
  (forkS fibS fibS)(0)   auto-cost=0   result=(0, 0)
  (forkS fibS fibS)(5)   auto-cost=10  result=(5, 5)
  (forkS fibS fibS)(10)  auto-cost=20  result=(55, 55)
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
  unit  : Ty
  nat   : Ty
  bool  : Ty
  _⊗_   : Ty → Ty → Ty   -- product
  _⊕_   : Ty → Ty → Ty   -- coproduct (sum): enables branching
  listT : Ty → Ty        -- recursive list type

⟦_⟧T : Ty → Set
⟦ unit   ⟧T = ⊤
⟦ nat    ⟧T = ℕ
⟦ bool   ⟧T = Bool
⟦ A ⊗ B  ⟧T = ⟦ A ⟧T × ⟦ B ⟧T
⟦ A ⊕ B  ⟧T = ⟦ A ⟧T ⊎ ⟦ B ⟧T
⟦ listT A ⟧T = List ⟦ A ⟧T
```

`Ty` is placed before §8/§10 so typed syntax and fibonacci state objects can be
expressed as `Ty` terms. The typed syntax category `_⇨S_` appears in §8.

`_⊕_` makes the category **cocartesian** (data-dependent branching via `caseS`).
`listT` is a **recursive type** — note that sums alone are *not* enough for lists;
the recursive `listT` is what makes genuinely recursive programs expressible.

---

### § 6 — Programs: Bundling Cost + Execution

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

`fibProgram` is constructed in §10a via `fromSyntax fibS` — the adequacy proof
is derived automatically from the generic `⟦⟧-adequate` theorem applied to `fibS`.

---

### § 7 — Auto-running Programs

```agda
runAuto : {A B : Set} → Program A B → A → Result B
runAuto prog a = run (Program.exec prog a) (proj₁ (Program.cost-exec prog a))
```

`runAuto` computes the budget from `cost-exec`, then passes it to `exec`.
By `Program.adequate`, the result is always `finished` — never `halted`.

---

### § 8 — Typed Syntax Category

This section adds the `Ty`/`_⇨S_` typed syntax and the full three-step pipeline
described at the top of this document.

#### § 8a. Types — see §4.5

`Ty` and `⟦_⟧T` are defined in §4.5. §8 begins with the morphisms.
`Ty` constructors: `unit`, `nat`, `bool`, `_⊗_`.
`⟦_⟧T` maps: `unit→⊤`, `nat→ℕ`, `bool→Bool`, `A⊗B→⟦A⟧T×⟦B⟧T`.

#### § 8b. Morphisms

```agda
data _⇨S_ : Ty → Ty → Set where
  idS    : A ⇨S A
  _∘S_   : B ⇨S C → A ⇨S B → A ⇨S C
  !S     : A ⇨S unit
  forkS  : A ⇨S B → A ⇨S C → A ⇨S (B ⊗ C)
  exlS   : (A ⊗ B) ⇨S A
  exrS   : (A ⊗ B) ⇨S B
  inlS    : A ⇨S (A ⊕ B)                  -- sum injections + case eliminator
  inrS    : B ⇨S (A ⊕ B)
  caseS   : A ⇨S C → B ⇨S C → (A ⊕ B) ⇨S C
  nilS    : unit ⇨S listT A               -- list build + destruct (uncons)
  consS   : (A ⊗ listT A) ⇨S listT A
  unconsS : listT A ⇨S (unit ⊕ (A ⊗ listT A))
  addS   : (nat ⊗ nat) ⇨S nat      -- addition, zero cost
  predS  : nat ⇨S nat               -- predecessor, zero cost
  minS   : (nat ⊗ nat) ⇨S nat       -- minimum (compare), costs 1 tel
  maxS   : (nat ⊗ nat) ⇨S nat       -- maximum (compare), costs 1 tel
  constS : ℕ → A ⇨S nat            -- constant natural, zero cost
  iterS  : A ⇨S A → (nat ⊗ A) ⇨S A -- iterate n times, 1 tel per step
  whileS : (A ⇨S (unit ⊕ unit)) → (A ⇨S A) → (nat ⊗ A) ⇨S A
                                     -- {x,y,z} tail form: fuel-bounded guarded
                                     -- loop, ON-DEMAND metering (see below)
  fixS   : (bodyK : ((⟦A⟧T →K ⟦B⟧T) → ⟦A⟧T →K ⟦B⟧T))
        → (costF : ⟦A⟧T →C ⟦B⟧T)
        → (precF : ∀ a extra →
            fixT bodyK a (proj₁ (costF a) + extra) ≡ just (proj₂ (costF a) , extra))
        → A ⇨S B
```

`constS k` ignores its input and returns the literal `k` at zero cost.
`minS`/`maxS` are the comparator primitives (each **costs 1 tel**); the
compare-and-swap `casS = forkS minS maxS` is the heart of the sorting network.
`inlS`/`inrS`/`caseS` add **data-dependent branching** (cost = the taken branch's
cost — exact, but no longer input-independent). `nilS`/`consS`/`unconsS` build and
destruct **lists**, so recursive list programs (via `fixS`) are now expressible.
`iterS f` applies `f` exactly `n` times, 1 tel per step — the counter IS the
budget. `fixS` carries general recursion with a *proved* cost (see `lengthS`, §10d).

#### § 8c–d. Dual Denotations

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
| `inlS` / `inrS` | `return-tel ∘ inj₁` / `inj₂` | `return-cost ∘ inj₁` / `inj₂` |
| `caseS l r` | `λ{inj₁ a→⟦l⟧K a; inj₂ b→⟦r⟧K b}` | cost of the **taken** branch |
| `nilS`/`consS`/`unconsS` | build `[]` / `_∷_` / match (cost 0) | same (cost 0) |
| `addS` | `λ (a,b) → return-tel (a+b)` | `λ (a,b) → return-cost (a+b)` |
| `predS` | `λ n → return-tel (predℕ n)` | `λ n → return-cost (predℕ n)` |
| `minS` / `maxS` | `step-tel (return-tel (a⊓b))` / `⊔` | `step-cost (return-cost (a⊓b))` / `⊔` |
| `constS k` | `λ _ → return-tel k` | `λ _ → return-cost k` |
| `iterS f` | `λ (n,a) → iterT-aux n ⟦f⟧K a` | `λ (n,a) → iterC-aux n ⟦f⟧C a` |
| `fixS bodyK costF _` | `fixT bodyK` | `costF` |

`iterT-aux`/`iterC-aux` are dual helpers that recurse structurally on the
explicit counter `n`, mirroring each other with `step-tel`/`step-cost`.

The composition row is why composed costs are automatic: `⟦ g ∘S f ⟧C = ⟦g⟧C ∘C ⟦f⟧C`
means `proj₁ (⟦ g ∘S f ⟧C a) = proj₁ (⟦f⟧C a) + proj₁ (⟦g⟧C (proj₂ (⟦f⟧C a)))` —
the costs of `f` and `g` are added, with no manual arithmetic.

#### § 8e. Precision for All Syntax

```agda
Precise : A ⇨S B → Set
Precise f = ∀ a extra →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a) + extra) ≡ just (proj₂ (⟦ f ⟧C a) , extra)

precise : (f : A ⇨S B) → Precise f
```

Proved by induction on `_⇨S_` constructors. The interesting cases:

**`constS k`:** cost = 0, `0 + extra = extra` definitionally → `refl`.

**`iterS f`:** inner induction on `n`.
- Base `n = 0`: `iterT-aux 0 _ a = return-tel a`; cost = 0 → `refl`.
- Step `n = suc k`: 1 `step-tel` consumed, then by precision of `f` at `(cr + extra)`
  (where `cr` = remaining iterations' cost) and IH on `k`. Uses `+-assoc` to align tel budget.
  Same proof shape as the `∘S` case.

**`fixS bodyK costF precF`:** precision is provided directly by `precF`.

**`g ∘S f`:** costs add as `n + m`. Budget is `(n+m)+extra`; `f` must leave `m+extra` for `g`.
1. `precise f a (m + extra)` gives `⟦f⟧K a (n + (m+extra)) ≡ just (vf, m+extra)`.
2. `subst (sym (+-assoc n m extra))` rewrites the tel argument from `n+(m+extra)` to `(n+m)+extra`.
3. `cong (λ mx → mx >>= …)` propagates the equality through `bind-tel`.
4. `precise g vf extra` finishes.

**`forkS f g`:** same `+-assoc` trick for `f`'s budget, then two `cong` steps
through the nested `>>=` of `forkK`.

**`idS`, `!S`, `exlS`, `exrS`, `addS`, `predS`:** `refl` — cost is 0, so `0 + extra = extra` definitionally.

**`minS`, `maxS`:** cost 1 (via `step-cost`); `suc 0 + extra = suc extra` makes
`step-tel` fire → `refl`.

**`inlS`, `inrS`, `nilS`, `consS`, `unconsS`:** cost 0 → `refl`.

**`caseS l r`:** proved by **branch-split** — `precise (caseS l r) (inj₁ a) = precise l a`,
`(inj₂ b) = precise r b`. Cost is now **data-dependent** (it depends on which branch
the input selects) yet still **exact and guaranteed** per input — the precision
theorem is unchanged; only input-independence is given up.

#### § 8f. Branching demo — data-dependent cost

```agda
branchExample : (nat ⊕ (nat ⊗ nat)) ⇨S nat
branchExample = caseS idS minS
-- ⟦ branchExample ⟧C (inj₁ 5)       ≡ (0 , 5)   -- left branch: idS, cost 0
-- ⟦ branchExample ⟧C (inj₂ (3 , 7)) ≡ (1 , 3)   -- right branch: minS, cost 1
```

Both equalities hold by `refl`: the cost the functor reports depends on the input.

#### § 8g. Parallel cost — a third interpretation `⟦_⟧WS`

A `(work , span)` functor, in the same "same syntax, another interpretation"
style:

```agda
WS A = (ℕ × ℕ) × A           -- ((work , span) , value)
⟦_⟧WS : A ⇨S B → ⟦A⟧T → WS ⟦B⟧T
```

- **work** = total operations = the sequential `tel` cost (so the §8e guarantee
  carries to the work component);
- **span** = critical-path depth = parallel time.

Only `forkS` exposes parallelism: it **adds work** but takes the **max** of the two
branch spans; everything else (`∘S`, `iterS`, `caseS`, primitives) is sequential.
Machine-checked examples (all `refl`):

| program | work | span | note |
|---|---|---|---|
| `fibS 10` | 10 | 10 | sequential `iterS` → span = work |
| `fibPairS 10` (`forkS fibS fibS`) | 20 | **10** | the two fibs run in parallel |
| `mergeSortS` (8-input) | 38 | **6** | 6 layers of independent compare-and-swaps |

and `mergeSort-work-is-cost : work mergeSortS xs ≡ proj₁ (⟦ mergeSortS ⟧C xs)`.

#### § 8h. Space — a fourth functor, and the resource-algebra square

The resource functors form a **2×2 family** of (sequential, parallel) monoids on
ℕ — the discrete cousin of Timely Computation's interval-semiring insight (*the
algebra is the design*):

| | parallel `+` | parallel `⊔` |
|---|---|---|
| **sequential `+`** | work `⟦_⟧C` | span `⟦_⟧WS` |
| **sequential `⊔`** | **space `⟦_⟧SP`** | (footprint — not instantiated) |

**Space is span's dual**: sequential stages *reuse* memory (`⊔` over `∘S`),
parallel branches are *simultaneously live* (`+` across `forkS`). `⟦_⟧SP`
measures peak live size under a word model `sizeT` (unit/nat/bool = 1; `⊗` sums;
`⊕` adds a tag; lists sum with spine). Machine-checked duality (`refl`):

```agda
fibPair-space : space fibPairS 10 ≡ space fibS 10 + space fibS 10
--  span of fibPairS = MAX of branches (10); space = SUM (both live)
```

`fixS` is measured coarsely (`in ⊔ out` — an opaque body's interior is
unmeasurable; one more argument for reified recursion). The space model is a
documented abstraction: no adequacy square yet (that needs a memory-instrumented
`⟦_⟧K`), in the spirit of Timely Computation's "planned improvements".

#### § 8i. `whileS` — `{x,y,z}` reified, derive-then-refine

Telomare's limited-recursion surface form `{x, y, z}` (test, body, base) in its
tail form is **derivable** from the existing vocabulary (Conal's small-shared-
vocabulary discipline — see `tictactoe.agda`):

```agda
guardS t b = caseS (b ∘S exlS) exlS ∘S distlS ∘S forkS idS t   -- one guarded step
whileD t b = iterS (guardS t b)                                 -- bounded guarded loop
```

`whileD` inherits all four interpretations and `precise` *for free*, but bills
**reserved capacity**: `iterS` ticks once per fuel unit even after the test goes
false. The **primitive `whileS`** is the *refined cost extraction* — same value,
**on-demand metering** (each check pays the test's own cost; a taken step pays
1 tel + the body; when the test goes false the metering stops):

```agda
drainS = whileS nonZeroS predS
drainS-test : ⟦ drainS ⟧C (10 , 3) ≡ (7 , 0)   -- 3×(test 1 + tick 1) + final test 1
-- the whileD equivalent bills 20 = 10 fuel ticks × (tick 1 + test 1)
```

Its precision proof (`while-prec`/`cont-prec`, mutual fuel induction with a
case-split on the test value) extends the machine-checked guarantee. Agreement
(the denotational-design law relating the two): both compute the same value —
checked by `refl` on the tic-tac-toe games (`agree-*` in `tictactoe.agda`).
Billing reading: `whileD` = pay for reserved capacity; `whileS` = pay for use.

### § 9 — Syntax Adequacy and Bridge

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

### § 10 — Fibonacci purely in `_⇨S_` syntax

#### § 10a. Pure-syntax fibonacci via `iterS`

`fibS` is assembled entirely from `_⇨S_` constructors — no host-level
Agda functions, no escape hatches:

```agda
-- State object in Ty syntax
FibStateTy : Ty
FibStateTy = nat ⊗ (nat ⊗ nat)

FibState : Set
FibState = ⟦ FibStateTy ⟧T

-- Accumulator step: (a, b) ↦ (b, a+b)
fibAccStepS : (nat ⊗ nat) ⇨S (nat ⊗ nat)
fibAccStepS = forkS exrS (addS ∘S forkS exlS exrS)

-- Initial accumulator from n: n ↦ (n, (0, 1))
fibInitS : nat ⇨S FibStateTy
fibInitS = forkS idS (forkS (constS 0) (constS 1))

-- Fibonacci
fibS : nat ⇨S nat
fibS = exlS ∘S iterS fibAccStepS ∘S fibInitS

-- Bundle using fromSyntax: adequacy derived from generic ⟦⟧-adequate
fibProgram : Program ℕ ℕ
fibProgram = fromSyntax fibS
```

Every head symbol of `fibS` is a `_⇨S_` constructor: `exlS`, `∘S`, `iterS`,
`forkS`, `exrS`, `addS`, `constS`, `idS`. Reading `fibS` is reading syntax.

#### § 10b. Fibonacci sequence via Ty syntax (the three-step pipeline in Agda)

```agda
-- STEP 2: tel budget from CostM interpretation
fibS-cost : ℕ → ℕ
fibS-cost n = proj₁ (⟦ fibS ⟧C n)   -- = n

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

-- Fork: (fib(n), fib(n)), cost = 2*n
fibPairS : nat ⇨S (nat ⊗ nat)
fibPairS = forkS fibS fibS
```

#### § 10b–c. Merge sort as a sorting network, with proved cost

A recursive list merge sort is now expressible (`_⇨S_` has lists + branching +
`fixS` — see §10d), but a **fixed-size** merge sort is simpler and entirely
*oblivious*: a **sorting network** of compare-and-swaps (`casS = forkS minS maxS`),
which is also what the combinational ConCat circuit backend can render.
`mergeSortS` is the 8-input Batcher odd-even mergesort
(19 comparators in 6 layers); built purely from `_⇨S_` constructors, it is
automatically `precise`:

```agda
casS : (nat ⊗ nat) ⇨S (nat ⊗ nat)
casS = forkS minS maxS

mergeSortS : V8 ⇨S V8                       -- V8 = a left-nested 8-tuple of nat
mergeSortS = L6 ∘S L5 ∘S L4 ∘S L3 ∘S L2 ∘S L1

-- machine-checked: sorts AND costs exactly 38 (= 19 comparators × 2 min/max)
mergeSort-test :
  ⟦ mergeSortS ⟧C [7,6,5,4,3,2,1,0] ≡ (38 , [0,1,2,3,4,5,6,7])
mergeSort-test = refl
```

(The ConCat backends render/run this — `ctc/DIAGRAMS.md` shows the 4-input network
as an SVG; `ctc/HVM-BACKEND.md` runs the full 8-input network on HVM2.)

#### § 10d. General recursion over lists, with a proved exact cost

With `listT`, a genuinely recursive list program is expressible, and `fixS` *forces*
a cost function + proof. `lengthS` is the first such program — list length by
recursion, with the machine-checked guarantee that it costs exactly `length + 1`:

```agda
lengthS : listT A ⇨S nat
lengthS = fixS bodyK costF precF        -- costF xs = (suc (length xs) , length xs)
  -- precF: [] case = refl; cons case = one `cong` over the IH

lengthS-test : ⟦ lengthS ⟧C (10 ∷ 20 ∷ 30 ∷ []) ≡ (4 , 3)   -- value 3, cost 4
lengthS-test = refl
```

This is the mechanism a general (recursive, list-based) merge sort would use: its
exact-cost `precF` is a larger formalization, but the pattern is proved end-to-end
by `lengthS`.

---

## Proof architecture

```
precise (iterS f) ← inner induction on n
  iter-prec zero    a extra = refl
  iter-prec (suc k) a extra:
     precise f a (cr + extra) + +-assoc + cong + iter-prec k vf extra
          │
          └── precise : (f : A ⇨S B) → Precise f   ← induction on _⇨S_
                   │
                   └── ⟦⟧-adequate : ⟦f⟧K a cost ≡ just (val, 0)
                            │
                            └── Program.adequate   (field in Program record)
                                     │
                                     └── runAuto always returns finished
                                              │
                                              └── runFromSyntax = fibS-run, fibS-0 … fibS-10
```

Every arrow is a propositional equality proof in Agda's type theory.
The `iter-prec` induction has the same `subst`+`trans`+`cong` structure as
the `∘S` case; the root base case is `refl`.

---

## Key design decisions

| Decision | Why |
|---|---|
| `CostM = ℕ × A` (Writer) not `TelM` | Cost analysis must always succeed; `nothing` would make composition unsound |
| `forkC` via `let` not `bind-cost` | `bind-cost` of `return-cost` gives cost `n + (m + 0)`, not definitionally `n + m`; precision proofs need the latter |
| Precision instead of adequacy alone | Adequacy `exec cost ≡ just (val, 0)` is not composable; precision `exec (cost+extra) ≡ just (val, extra)` is |
| `fixT-aux` fuel = tel | Ties fuel depletion to tel depletion; the bound is tight, not conservative |
| `iterS` over `(nat ⊗ A)` | The loop bound is explicit in syntax, so totality and per-step cost accounting are structural and proof-friendly |

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

## Relation to *Compiling to Categories* and TCM

`telomare.agda` is the same core idea as *Compiling to Categories* (C2C), but
spelled out directly in Agda instead of using a compiler plugin.

In C2C, there are two conceptual steps:

1. **Change vocabulary:** rewrite lambda-calculus/program terms into categorical
   combinators.
2. **Change interpretation:** keep the same combinator structure, but interpret
   it in another category via homomorphic mappings.

In `telomare.agda`, those two steps appear as:

- **Step 1 (explicit syntax):** `_⇨S_` is already the categorical program syntax.
  There is no `ccc` plugin pass because the syntax category is first-class in
  Agda.
- **Step 2 (dual denotations):** `⟦_⟧K` and `⟦_⟧C` interpret the same syntax in two
  categories (`→K` for execution, `→C` for cost).

This mapping is direct:

| C2C / TCM notion | `telomare.agda` realization |
|---|---|
| Typed program syntax | `_⇨S_` |
| Target category #1 | `→K` (TelM execution) |
| Target category #2 | `→C` (CostM analysis) |
| Homomorphic interpretation | clauses of `⟦_⟧K` and `⟦_⟧C` |
| Compositional correctness condition | `Precise` / `precise` |
| Commuting-square-style adequacy | `⟦⟧-adequate`, `Program.adequate` |
| User-facing execution after reinterpretation | `runFromSyntax` |

So the cost result is not an external estimate: it is another categorical
interpretation of the same syntax tree. Adequacy and precision then prove these
two interpretations agree exactly on results and remaining tel.

---

## Conceptual lineage

This file sits in the same denotational-design lineage as several Elliott papers:

- **Type Class Morphisms (2009):** instance meaning must follow semantic meaning
  via homomorphism.
- **Compiling to Categories (2017):** keep program structure, vary category to
  get new semantics.
- **Simple Essence of AD (2018):** same structure, reinterpret into derivative
  categories.
- **Language Derivatives (2021):** dual symbolic/automatic differentiation of
  language semantics.
- **Timely Computation (2023):** commuting diagrams for compositional circuit
  correctness and timing.

`telomare.agda` applies that pattern to gas/telomere: compute budget by one
interpretation (`CostM`), run by another (`TelM`), and connect them by machine-
checked adequacy/precision proofs.

---

## File structure (`telomare.agda`)

| Section | Content |
|---|---|
| §1 | Denotational design overview (comments) |
| §2 | `TelM` — execution monad (`return-tel`, `bind-tel`, `step-tel`) |
| §3 | `CostM` — cost monad (`return-cost`, `bind-cost`, `step-cost`) |
| §4 | `_→K_`, `_→C_`, `idK/C`, `∘K/C`, `forkK/C` |
| §4.5 | `Ty` (`bool`, `_⊕_`, `listT`), `⟦_⟧T` — type objects and denotation |
| §5 | `fixT-aux`, `fixT` — recursion primitive (fuel pattern) |
| §6 | `Program` record |
| §7 | `Result`, `run`, `runAuto` |
| §8 | `_⇨S_` (`addS`/`predS`/`minS`/`maxS`, `inlS`/`inrS`/`caseS`, `nilS`/`consS`/`unconsS`, `natOutS`/`distlS`, `constS`/`iterS`/`whileS`/`fixS`), `⟦_⟧K`, `⟦_⟧C`, `Precise`, `precise` (incl. `while-prec`); §8f `branchExample`; §8g `⟦_⟧WS` (work/span); §8h `sizeT`/`⟦_⟧SP` (space); §8i `whileS` vs derived `whileD` |
| §9 | `⟦⟧-adequate`, `fromSyntax`, `runFromSyntax` |
| §10 | pure-syntax `fibS`, `fibProgram`, `fibS-cost/val/run`, `doubleFibS`, `fibPairS`; §10b–c `casS`/`mergeSortS` (+`mergeSort-test`, work/span examples); §10d `lengthS` (+`lengthS-test`) |
| §11 | `main` — IO output showing the full pipeline |

---

## Beyond Agda: ConCat diagrams, parallel cost, and an HVM2 backend

The same `_⇨S_` design is taken further outside Agda (ConCat operates on Haskell,
so the morphisms are faithful **Haskell ports**; `telomare.agda` stays the
machine-checked spec):

- **`ctc/DIAGRAMS.md`** — the morphisms compiled through Conal Elliott's ConCat
  into the **circuit** category and rendered as SVG wiring diagrams
  (`nix run .#telomare-ctc-svg`): the Fibonacci step/term, the cost functor
  (`fib-cost`), `forkS`/`_∘S_`, and the merge-sort network.
- **`ctc/HVM-BACKEND.md`** — a **new ConCat backend** (`ctc/src/HVM.hs`) whose
  CCC-class instances emit **HVM2/Bend** code, so `toCcc f :: HVM a b` is a runnable
  HVM2 program (`nix run .#ctc-to-hvm`). The 8-input `mergeSortS` runs here even
  though it overflowed the circuit backend.
- **`PARALLEL.md`** — the `(work, span)` functor (§8g) and the stated refinement
  relating telomare's proved cost to HVM2's actual cost; `bend/merge_sort.bend`
  runs the network on HVM2 (`nix run .#bend-sort`).

## Key references

- Conal Elliott, *Denotational Design with Type Class Morphisms*, Haskell Symposium 2009
- Conal Elliott, *Compiling to Categories*, ICFP 2017
- Conal Elliott, *The Simple Essence of Automatic Differentiation*, ICFP 2018
- Conal Elliott, *Symbolic and Automatic Differentiation of Languages*, ICFP 2021
- Conal Elliott, *Timely Computation* — motivation for the telomere/gas model
