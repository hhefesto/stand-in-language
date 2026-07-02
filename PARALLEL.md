# Parallel cost in telomare, and the Bend/HVM refinement

This documents the two parallelism-related additions to telomare:

1. a **(work, span) cost functor** in `telomare.agda` — a machine-checked
   prediction of *parallel* cost (Stage 2); and
2. the **refinement statement** relating telomare's proved cost to the actual
   cost of running on **Bend/HVM** (Stage 4).

It follows Conal Elliott's discipline: *one syntax, many homomorphic
interpretations*. telomare's `_⇨S_` already has execution (`⟦_⟧K`) and sequential
cost (`⟦_⟧C`); we add a parallel-cost interpretation and relate it to a runtime
that realizes the parallelism.

---

## 1. The (work, span) cost functor — `⟦_⟧WS`

A third functor out of `_⇨S_` (see `§8g` in `telomare.agda`):

```
WS A = (ℕ × ℕ) × A          -- ((work , span) , value)
```

- **work** = total operations = the sequential `tel` cost (so the §8e execution
  guarantee carries over to the work component);
- **span** = critical-path depth = parallel time.

The only constructor that exposes parallelism is `forkS`: it **adds work** but
takes the **max** of the two branch spans. Everything else (`∘S`, `iterS`,
`caseS`, primitives) is sequential along its path. Machine-checked (`§10c`, all
by `refl`):

| program | work | span | note |
|---|---|---|---|
| `fibS 10` | 10 | 10 | sequential `iterS`, no fork → span = work |
| `fibPairS 10` = `forkS fibS fibS` | 20 | **10** | the two fibs run in parallel |
| `mergeSortS` (8-input) | 38 | **6** | 6 layers of independent compare-and-swaps |

`work / span` is the available parallelism (≈ 6.3× for the sorting network).
And `mergeSort-work-is-cost : work mergeSortS xs ≡ proj₁ (⟦ mergeSortS ⟧C xs)` —
the work component **is** the proved sequential `tel` cost, so the execution
guarantee is preserved while the span predicts the parallel speedup.

### The resource-algebra square (now including SPACE)

The resource functors form a 2×2 family of (sequential, parallel) monoids on ℕ —
telomare's discrete cousin of Timely Computation's interval semiring:

| | parallel `+` | parallel `⊔` |
|---|---|---|
| **sequential `+`** | work `⟦_⟧C` | span `⟦_⟧WS` |
| **sequential `⊔`** | **space `⟦_⟧SP`** | (footprint — not instantiated) |

Space (peak live size, word model) is span's **dual**: sequential stages reuse
memory (`⊔` over `∘S`), parallel branches are simultaneously live (`+` across
`forkS`). Machine-checked: `fibPair-space : space fibPairS 10 ≡ space fibS 10 +
space fibS 10` while `span fibPairS 10 = span fibS 10` (max). `fixS` space is
coarse (`in ⊔ out`); no adequacy square yet (needs a memory-instrumented `⟦_⟧K`).

---

## 2. Refinement to Bend/HVM — the statement

Bend (HVM2) is a pure functional runtime that evaluates via **interaction nets**:
the result is independent of reduction order (confluence), so independent redexes
reduce **in parallel** with no annotations. telomare's `_⇨S_` programs are pure,
oblivious dataflow — exactly the shape HVM parallelizes. `bend/merge_sort.bend`
(run via `nix run .#bend-sort`) is a hand port of `mergeSortS`; HVM reduces the
independent compare-and-swaps in each layer concurrently.

The **refinement statement** ties telomare's *proved* cost to HVM's *actual* cost.
It is stated here as specification/conjecture — **not** machine-proved (a full
proof is a separate, research-grade effort; this is flagged honestly):

> **(R1) Work soundness (oblivious fragment).** For any `f : A ⇨S B` built without
> `caseS`/`fixS` sharing surprises, the number of HVM interactions to normalize
> `⟦f⟧HVM a` equals `work f a` (= the telomare `tel` cost). Intuition: each
> telomare primitive is one interaction-net redex; `∘S`/`forkS` introduce no extra
> reductions beyond wiring.

> **(R2) Work bound (general).** For any `f`, HVM interactions ≤ `c · work f a`
> for a fixed constant `c` (HVM's sharing can only *reduce* the count; the bound
> accounts for fan/dup bookkeeping).

> **(R3) Span realizability.** Given enough parallel resources, HVM's parallel
> reduction depth is `Θ(span f a)` — the `forkS`-max critical path the `⟦_⟧WS`
> functor computes. This is the sense in which *telomare proves the parallelism
> that Bend realizes*.

**Empirical data point for R1/R2** (see `BENCHMARK.md`): for `drainS` on HVM2,
measured interactions are *exactly linear* in the proved tel cost —
`ITRS = 45·cost + 15` at both N=1M (90,000,015 / cost 2,000,000) and N=4M
(360,000,015 / cost 8,000,000). The constant-factor bound R2 is visibly real
for this program; proving it is still open.

What is **guaranteed today** vs. **stated**:
- *Guaranteed (machine-checked in Agda):* `⟦f⟧C` computes an exact `tel` that
  provably suffices to run `⟦f⟧K` (`precise`); `work = ⟦_⟧C` cost; `span` per
  `⟦_⟧WS`. All by `refl`/induction.
- *Stated (R1–R3), not proved:* the bridge to HVM's interaction count. Bend buys
  **speed, not proofs** — its dependently-typed successor (Bend2), which could
  carry proofs, is not publicly available.

---

## 3. A `⟦_⟧HVM` compiler — now built (via ConCat)

The compiler now exists, as a **new ConCat backend**: a category `HVM` whose
CCC-class instances emit Bend/HVM2 code, so `toCcc f :: HVM a b` is a runnable
HVM2 program. See **`ctc/HVM-BACKEND.md`**; run it with `nix run .#ctc-to-hvm`.

Verified on HVM2: `sqr → 25`, `fibAccStep (3,4) → (4,7)`, `mergeSort4 → sorted`,
and **`mergeSort8 → sorted`** — the 8-input sorting network that the ConCat→Circuit
backend could **not** serialize compiles cleanly here (the emitted term is
point-free, hence linear, with no fan-out blowup).

Status: it is a **code generator, not a verified compiler** — the emitted HVM2 is
checked by *running* it against the Agda semantics. Making R1–R3 theorems (the
emission preserves meaning and cost) remains future work.

### Bounded recursion — including the parallel `foldC` (now implemented)

The plugin can't categorify recursion, but bounded recursion reaches HVM2 as a
**primitive** (named globals + a specialized loop; the per-node morphisms still go
through `toCcc`), with the size a **runtime CLI argument** (constant `.bend`, no
unrolling) — see `ctc/HVM-BACKEND.md`:

- **`iterateC`** — sequential bounded iteration (telomare `iterS`): `fib(n)` for
  runtime `n` (span = n).
- **`foldC`** — a **parallel** catamorphism over a binary tree: the two recursive
  calls are independent, so HVM2 folds them concurrently. This is the
  parallel-scaling path the `(work, span)` functor predicts (`forkS` = max): tree
  sum of `2^d` leaves, e.g. d=18 → 262144 via ~15.4M interactions in ~0.7s. This is
  the natural basis for a seq-vs-parallel **benchmark** vs a Haskell baseline.

## Run it

```sh
nix run .#ctc-to-hvm         # ConCat→HVM2: combinational demos + bounded recursion (iterS/foldC)
nix run .#bend-sort          # telomare's merge-sort network on Bend/HVM (parallel)
nix run .#bend-hello         # the Bend hello-world
nix run .#telomare-ctc-svg   # ConCat circuit diagrams → out/*.svg
nix build .#agda-telomare    # type-checks the (work,span) functor + all proofs
```
