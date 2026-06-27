# The telomare `_⇨S_` design as circuit diagrams

This directory turns the **telomare denotational design** (from `telomare.agda`)
into **SVG wiring diagrams** by running a Haskell port of it through **Conal
Elliott's Compile-to-Categories (ConCat)**. This document explains what the
diagrams mean and the two ideas that meet in them.

> Generate them with `nix run .#telomare-ctc-svg` from the repo root. The SVGs
> (and the GraphViz `.dot` sources) are written into `./out/`.

---

## TL;DR — what each SVG shows

Each diagram is a **dataflow / circuit picture of one morphism**: boxes are
primitive operations, wires carry values left-to-right from the input port(s)
(`In`) to the output port(s) (`Out`). A *fork* (one value used twice) shows up as
a wire that splits; a *projection* (`exl`/`exr`) shows up as a wire that drops a
component of a pair.

| SVG | telomare `_⇨S_` morphism | meaning |
|-----|--------------------------|---------|
| `fib-acc-step.svg` | `fibAccStepS = forkS exrS (addS ∘S forkS exlS exrS)` | one Fibonacci step `(a,b) ↦ (b, a+b)` |
| `fib-init.svg` | `fibInitS = forkS idS (forkS (constS 0) (constS 1))` | seed the loop: `n ↦ (n,(0,1))` |
| `add.svg` | `addS` | the addition primitive `(a,b) ↦ a+b` |
| `fib-unrolled-8.svg` | `exlS ∘S iterS fibAccStepS` (unrolled to depth 8) | eight chained step blocks: `exl ∘ fibAccStep⁸` |
| `fib-10.svg` | `exlS ∘S iterS fibAccStepS` (unrolled to depth 10) | the **10th Fibonacci term** as a computation: ten chained step blocks `exl ∘ fibAccStep¹⁰`; feeding the seed `(0,1)` yields `fib(10) = 55` |
| `fib-10-value.svg` | same, with the `(0,1)` seed baked in | the **10th term as a value**: the closed computation constant-folds to a single `55.0` node |
| `fib-cost.svg` | the **cost functor** `⟦_⟧C` drawn: `((a,b),c) ↦ ((b,a+b), c+1)` unrolled 10× → `(value, cost)` | the value cascade **with a parallel `+1` cost-counter chain**; `((0,1),0) ↦ (55, 10) = ⟦fibS⟧C 10` |
| `fib-pair.svg` | `fibPairS = forkS fibS fibS` | the **fork** combinator: one fib pipeline, result fanned to both outputs `(55,55)` (sharing) |
| `double-fib.svg` | `doubleFibS = fibS ∘S fibS` | the **composition** combinator: two 10-step pipelines chained (20 stages) → `fib(20)=6765` |
| `pow2-iter.svg` | `iterS (x ↦ x+x)` | `iterS` is **not fib-specific**: a scalar-state body (doubling) → `2¹⁰=1024` |
| `merge-sort.svg` | `casS = forkS minS maxS`, wired into a merge-sort **sorting network** | a 4-input merge sort (sort two pairs, then merge): five compare-and-swaps as `min`/`max` gates; `[3,1,4,2] ↦ [1,2,3,4]`. (telomare's `mergeSortS` is the **8-input** version — see below.) |

The point: **the diagram is not a separate drawing of the code — it _is_ the
code, reinterpreted.** The same expression that computes Fibonacci is, under a
different categorical interpretation, a circuit.

---

## Idea 1 — Conal Elliott's *Compile to Categories*

(See `~/Documents/conal-elliott/compiling-to-categories.pdf`, ICFP 2017, and the
ConCat library at `github:compiling-to-categories/concat`.)

**The Curry–Howard–Lambek correspondence** says that the simply-typed lambda
calculus is the internal language of **cartesian closed categories (CCCs)**.
Every well-typed function therefore has a meaning purely in terms of a handful of
categorical combinators:

```haskell
class Category k where
  id  :: a `k` a
  (.) :: (b `k` c) -> (a `k` b) -> (a `k` c)

class Category k => Cartesian k where      -- products
  exl :: (a, b) `k` a                      -- project left
  exr :: (a, b) `k` b                      -- project right
  (&&&) :: (a `k` c) -> (a `k` d) -> (a `k` (c, d))   -- fork
```

Conal's insight: a **GHC plugin** (`-fplugin=ConCat.Plugin`) can mechanically
rewrite an ordinary Haskell function into these combinators at compile time —
the pseudo-operation `toCcc f` triggers the rewrite. Because the combinators are
just a *type class*, the **same function** can then be interpreted in **any**
category that implements them:

- `(->)` — ordinary evaluation
- `GD`/`Dual` — automatic differentiation (the "simple essence of AD")
- `Syn` — a pretty-printable syntax tree of the combinator term
- **`(:>)` — `ConCat.Circuit`: a graph of primitive gates → DOT → SVG** ← used here
- `ConCat.Graphics.GLSL` — a GPU fragment shader
- (the original 2017 target) Verilog / hardware

You write the function once; you pick the interpretation by choosing the target
type. There is **no separate diagram DSL** and no risk of the picture drifting
from the code — the picture is a *functor image* of the code, and the functor
laws (`F id = id`, `F (g ∘ f) = F g ∘ F f`) guarantee it is faithful.

In this project the chosen interpretation is the **circuit category `(:>)`**:

```haskell
fibAccStepCirc :: (Int :* Int) :> (Int :* Int)
fibAccStepCirc = toCcc fibAccStep          -- ordinary fn → circuit
... = writeDot name attrs (mkGraph fibAccStepCirc)   -- circuit → DOT → SVG
```

ConCat's scalar `R` (= `Double`) plays the role of telomare's object `nat`, and
the pair type `(:*)` plays the role of the product `_⊗_`. (`R` rather than `Int`
because ConCat's numeric categories are exercised on `Double`; `Int` arithmetic
trips the plugin's post-transformation lint. The *wiring* a diagram shows is
identical either way — only the carried scalar type differs.)

---

## Idea 2 — the telomare Agda design (`telomare.agda`)

`telomare.agda` is itself a *denotational design in Conal's style*. Its center is
a **typed syntax category** `_⇨S_`: a small, first-order, **cartesian** category
whose objects are telomare types and whose morphisms are programs.

```agda
data Ty : Set where
  unit : Ty ;  nat : Ty ;  bool : Ty ;  _⊗_ : Ty → Ty → Ty   -- product

data _⇨S_ : Ty → Ty → Set where
  idS    : A ⇨S A
  _∘S_   : B ⇨S C → A ⇨S B → A ⇨S C          -- composition
  forkS  : A ⇨S B → A ⇨S C → A ⇨S (B ⊗ C)    -- fork (the &&& above)
  exlS   : (A ⊗ B) ⇨S A                       -- project left
  exrS   : (A ⊗ B) ⇨S B                       -- project right
  addS   : (nat ⊗ nat) ⇨S nat                 -- addition primitive
  constS : ℕ → A ⇨S nat                        -- constant (zero cost)
  iterS  : A ⇨S A → (nat ⊗ A) ⇨S A            -- bounded iteration
  ...
```

These constructors are **exactly the CCC combinators** (`idS`/`_∘S_` = Category;
`forkS`/`exlS`/`exrS` = Cartesian) plus telomare primitives. So `_⇨S_` is a
hand-written categorical syntax, and ConCat's `(:>)` is another category — the
diagrams are what you get by sending one into the other.

### Why telomare has *two* meanings for each morphism

The Agda gives every `_⇨S_` morphism **two homomorphic denotations**:

- `⟦_⟧K` — **execution** in a Kleisli category over `TelM A = Tel → Maybe (A × Tel)`.
  Running consumes a fuel budget (`Tel`); it may fail if it runs out.
- `⟦_⟧C` — **cost** in `CostM A = ℕ × A`, a writer monad that *statically* counts
  the budget a morphism needs and always succeeds.

Both are **functors out of `_⇨S_`** (this is the Type-Class-Morphism / functor
discipline — `telomare-backwards.agda` machine-checks the `CategoryH` laws using
Conal's Felix Agda library). The payoff is the **precision theorem**:

```agda
precise : (f : A ⇨S B) → ∀ a extra →
  ⟦ f ⟧K a (proj₁ (⟦ f ⟧C a) + extra) ≡ just (proj₂ (⟦ f ⟧C a) , extra)
```

i.e. *running a program with exactly its computed cost (plus any slack) succeeds
and leaves exactly the slack untouched* — costs add compositionally because
`⟦_⟧C` is a functor (`⟦ g ∘S f ⟧C = ⟦g⟧C ∘C ⟦f⟧C`).

### The Fibonacci showcase

Built **purely** from `_⇨S_` constructors (no host-language escape hatches):

```agda
fibAccStepS = forkS exrS (addS ∘S forkS exlS exrS)    -- (a,b) ↦ (b, a+b)
fibInitS    = forkS idS (forkS (constS 0) (constS 1))  -- n ↦ (n,(0,1))
fibS        = exlS ∘S iterS fibAccStepS ∘S fibInitS    -- n ↦ fib n
```

with, by the functor `⟦_⟧C`, automatically-derived costs such as
`⟦ fibS ⟧C 10 ≡ (10 , 55)` (10 iterations, value 55) — proved by `refl`.

---

## Where the two ideas meet (this project)

ConCat compiles **GHC Core**, not Agda, so there is no direct Agda→ConCat path.
`src/Main.hs` is therefore a **faithful Haskell port** of the Fibonacci `_⇨S_`
morphisms — each Haskell function is named after, and commented with, its Agda
constructor term:

```haskell
-- Agda fibAccStepS = forkS exrS (addS ∘S forkS exlS exrS)
fibAccStep :: Int :* Int -> Int :* Int
fibAccStep (a, b) = (b, a + b)
```

ConCat's plugin then re-expresses each as a circuit and emits its diagram.

### Reading the diagrams

- **`fib-acc-step.svg`** — `(a,b) ↦ (b, a+b)`. The input pair fans out: `b`
  becomes the new left output (`exr`), while `a` and `b` both feed an **adder**
  (`addS`) whose result is the new right output. This is precisely
  `forkS exrS (addS ∘S forkS exlS exrS)` drawn as wires + one `+` gate.

- **`fib-init.svg`** — `n ↦ (n,(0,1))`. The input `n` passes through (`idS`) and
  two **constant** nodes (`constS 0`, `constS 1`) inject the seed accumulator.

- **`add.svg`** — the lone `addS` primitive: two inputs into one `+` gate. The
  atom every Fibonacci step is built around.

- **`fib-unrolled-8.svg`** — the heart of `fibS`. `iterS` runs `fibAccStep` a
  *runtime* number of times, but a circuit is **combinational** (no unbounded
  loops), so the loop is **unrolled to a fixed depth of 8**: you see **eight
  `fib-acc-step` blocks chained in series**, then a final `exl` taking the first
  component. Reading left to right literally traces the Fibonacci recurrence
  advancing eight steps. (The real `fibInitS` constants `(0,1)` would fold away
  into a constant circuit, so the diagram instead takes the initial accumulator
  pair `(a,b)` as its input, keeping the dataflow visible.)

> **Why unrolling is the honest representation.** In telomare the loop bound *is*
> the fuel: `iterS`'s counter is the `Tel` budget, and the cost functor reads
> `⟦ iterS f ⟧C` as "one tick per step." A combinational circuit has no counter,
> so a circuit can only depict a *fixed* number of steps — exactly what the
> static cost of `fibS n` would be for a chosen `n` (here `n = 8`). The diagram is
> thus a picture of "Fibonacci, cost 8."

- **`fib-10.svg`** — the **10th Fibonacci term**, same construction as the depth-8
  diagram but **unrolled to depth 10**: `exl ∘ fibAccStep¹⁰`, **ten chained
  `fib-acc-step` blocks**. In telomare, `fibS 10 = exl (fibAccStep¹⁰ (0,1)) = 55`
  (0-indexed: 0,1,1,2,3,5,8,13,21,34,**55**). The diagram takes the accumulator
  pair `(a,b)` as input — feed the seed `(0,1)` and follow the ten `+` stages
  left-to-right to reach `55` (the program prints
  `check: exl (fibAccStep^10 (0,1)) = 55.0` to confirm).

- **`fib-10-value.svg`** — the **same 10th term as a value**. Here the `(0,1)` seed
  is baked in (`fib10Value : () → fib(10)`), so there is no real input; GHC `-O2`
  and the ConCat plugin constant-fold the entire ten-stage computation to a
  **single `55.0` node** (its `Syn` form is literally `const 55.0`). Where
  `fib-10.svg` shows *how* the 10th term is computed, this shows *what it is*.

### The cost calculation, and the combinators

These four show the *other* half of the telomare design — the **cost functor** and
the categorical **combinators** (`forkS`, `_∘S_`) at the program level.

- **`fib-cost.svg`** — the **cost calculation, drawn.** telomare gives `_⇨S_` two
  functorial meanings: execution `⟦_⟧K` (the value) and **cost** `⟦_⟧C`, a writer
  monad `ℕ × A` that charges one `tel` tick per `iterS` step — so
  `⟦ fibS ⟧C 10 = (10, 55)`. To *draw* it, the step carries a counter alongside
  the value: `((a,b),c) ↦ ((b,a+b), c+1)`. The diagram then has **two rows**: the
  top is the value cascade (the fib adders), the bottom is a **`+1` cost-counter
  chain** fed by a `1.0` constant; both reach `Out` as `(value, cost)`. Feeding
  the seed `((0,1),0)` gives `(55, 10)` — value 55, cost 10. You can literally see
  the two denotations computed together.

- **`fib-pair.svg`** — `forkS fibS fibS`, the **fork/duplication** combinator. The
  fib pipeline is computed once and its result fans out to both outputs `(55,55)`
  (sharing — `forkS` is `dup` followed by the two branches).

- **`double-fib.svg`** — `fibS ∘S fibS`, the **composition** combinator: two
  10-step fib pipelines chained end-to-end (**20 stages**), advancing Fibonacci to
  `fib(20) = 6765`. Costs add: `10 + 10 = 20`. (telomare's data-dependent
  `fib(fib n)` isn't combinational; this is the pipeline-composition reading of
  `_∘S_`.)

- **`pow2-iter.svg`** — `iterS` is **not fib-specific**: a scalar-state body
  `x ↦ x + x` (doubling), iterated ten times from `1`, computes `2¹⁰ = 1024` — a
  clean chain of ten doublers, a different `iterS` body from fib.

> **A note on what categorifies.** The ConCat plugin's circuit pass is finicky:
> the robust step shapes are fib's `(a,b) ↦ (b, a+b)` (one passthrough + one
> combine of *distinct* inputs) and `fibCost`'s `c+1` (arithmetic on a *use-once*
> wire). Reusing one wire across two combines — a triangular-sum body
> `(s,i) ↦ (s+i, i+1)`, or Pell `(a,b) ↦ (b, a+2b)` — trips its post-transformation
> lint, which is why the non-fib example here is scalar doubling rather than a
> sum. Likewise `fib-pair` shares one fib pipeline (`dup ∘ fib`) rather than
> duplicating the whole pipeline, which also tripped the lint.

### Merge sort as a sorting network

When this was first built, `_⇨S_` had only products (`unit/nat/bool/⊗`), so a
*recursive* merge sort wasn't expressible at all — hence a **fixed-size sorting
network** of compare-and-swap blocks. (`telomare.agda` has since gained sums
`_⊕_`, lists `listT`, and proved-cost recursion via `fixS` — see `lengthS` in
`README-Agda.md` — so a recursive list merge sort *is* now expressible in the
language.) But the diagram here is still a sorting network for a second,
independent reason: a ConCat **circuit is combinational**, so it can't render
recursion or lists regardless — only a fixed, oblivious network of gates. The
compare-and-swap is exactly

```
casS = forkS minS maxS : (nat ⊗ nat) ⇨S (nat ⊗ nat)
       (x , y)  ↦  (min x y , max x y)
```

so it needed two new telomare primitives — `minS, maxS : (nat ⊗ nat) ⇨S nat`
(added to `telomare.agda`, each charging 1 `tel`, precision proof `refl`).

- **In telomare (`telomare.agda`)**: `mergeSortS : V8 ⇨S V8` is the **8-input**
  Batcher odd-even mergesort — 19 compare-and-swaps in six stages (sort the two
  4-halves, then merge). It is built purely from `_⇨S_` constructors, so it is
  automatically `precise`. Agda machine-checks (`mergeSort-test`, by `refl`):
  `⟦mergeSortS⟧C [7,6,5,4,3,2,1,0] = (38, [0,1,2,3,4,5,6,7])` — both the sorted
  result **and** the cost `38 = 19 × 2` (each `min`/`max` costs 1 `tel`).

- **`merge-sort.svg`**: ConCat's circuit serializer blows up on the 8-wire
  network's fan-out (it doesn't terminate in minutes), so the *rendered* diagram
  is the **4-input** merge sort — the same construction at a size ConCat can draw:
  `In(4)` → sort the two pairs (`(0,1)`,`(2,3)`) → merge (`(0,2)`,`(1,3)`,`(1,2)`)
  → sorted `Out(4)`, each comparator a `min` gate and a `max` gate. `[3,1,4,2] ↦
  [1,2,3,4]`. (The `mergeSort8` Haskell function still *runs* correctly —
  `[7..0] ↦ [0..7]` — it just can't be serialized to a graph.)

---

## Regenerating

```sh
nix run .#telomare-ctc-svg     # writes out/*.svg (renders the .dot via GraphViz)
nix run .#ctc                  # just prints the Syn combinator form of each morphism
nix build .#ctc                # build the executables only (telomare-ctc + telomare-hvm)
```

> **Note:** `nix build .#ctc` only *compiles* the binaries — it does not produce
> any `.svg`. The diagrams come from the **app** (`nix run .#telomare-ctc-svg`),
> which runs the binary and pipes its `.dot` output through GraphViz into `./out/`
> (which is git-ignored).

`nix run .#ctc` prints the `Syn` interpretation — the same morphism rendered as a
**text** combinator term rather than a diagram — which is handy for checking a
diagram against its `_⇨S_` source in `telomare.agda`.

## See also: ConCat → HVM2

There is a second ConCat backend that emits **runnable HVM2/Bend** instead of
diagrams — `ctc/HVM-BACKEND.md` (`nix run .#ctc-to-hvm`). Notably the **8-input**
sorting network, which ConCat's *circuit* serializer cannot handle (see the
`merge-sort.svg` note above — it diverges, so the rendered diagram is the 4-input
case), compiles and **runs** through ConCat→HVM2: the emitted term is point-free,
hence linear in size, with no fan-out blowup.

## Notes & caveats

- **GHC lock.** `concat-plugin` is a GHC compiler plugin pinned to **GHC 9.4.8**,
  so this project is built by its own toolchain in `flake.nix` (the ConCat
  `nixpkgs` + overlay), separate from telomare's default `ghc96` project.
- **Plugin scale.** ConCat panics on large programs (dense matvecs, `sqrt` in
  LayerNorm, deep nesting). These morphisms are tiny integer arithmetic + pairing
  at a fixed unroll depth — comfortably within the regime the plugin handles.
- **Faithfulness.** The Haskell is a *manual transcription* of the Agda `_⇨S_`
  terms. The Agda remains the source of truth (it carries the machine-checked
  adequacy/precision proofs); these diagrams are a visualization of that design.
