# Run comparison: one telomare algorithm, three runtimes

**The algorithm** — written once, in telomare `_⇨S_` syntax:

```agda
drainS : (nat ⊗ nat) ⇨S nat
drainS = whileS nonZeroS predS          -- {x,y,z} tail form: count N down to 0
-- machine-checked:  ⟦ drainS ⟧C (N , N) ≡ (2N , 0)   (test+tick per step; fuel = start ⇒ no final test)
```

Every runtime evaluates *this* algorithm (same denotation; the Haskell/HVM2
forms use the same test/body morphisms that `toCcc` consumes):

| # | runtime | how it gets the algorithm |
|---|---|---|
| 1 | **Agda `⟦_⟧K`** (MAlonzo native) | `runFromSyntax drainS` — the verified reference; auto-budget pipeline (computes `⟦_⟧C`, then runs `⟦_⟧K`) |
| 2 | **native GHC** (-O2) | the `whileS` unfolding as a strict loop over the same `drainTest`/`drainBody` |
| 3 | **HVM2** (`bend run-c`) | `toBendWhile` emission — init/final/test/body through ConCat's `toCcc` |

**Excluded** (documented): `bend run-rs` — crashes on recursive global clones
("non-affine global reference"); **GPU** — this box is AMD and HVM2's GPU
backend is CUDA-only.

**The telomare angle**: the *predicted* cost is exact and machine-checked
(`2N` tel here), so each runtime gets a **ns-per-tel** figure — the runtimes differ
only in how fast they burn a tel.

## Fairness notes

- Number representations differ: Agda `ℕ` compiles to GHC `Integer` (MAlonzo),
  the GHC baseline uses `Int`, HVM2 uses `u24` (N ≤ 16M fits). Documented, not
  hidden.
- Agda/Haskell times: best-of-3, whole process (startup included; ≪ run at
  these N). HVM2: bend's internal `-s` timer (its per-run C compile excluded).
- The Agda time covers the *canonical pipeline* (`⟦_⟧C` budget + `⟦_⟧K` run —
  two O(N) passes): that IS the telomare runtime story.
- Machine: 16-core x86_64-linux (same box for all three).

## Results (measured, `nix run .#bench-drain`, 2026-07-01)

All predictions confirmed at runtime (`cost = span = 2N`, `space = 2`). Every
completed run reported **result = 0** (HVM2 at 16M did not finish — see below).

| N | cost (tel) | Agda `⟦_⟧K` | GHC -O2 | HVM2 run-c (internal) | HVM2 ITRS |
|---|---|---|---|---|---|
| 1,000,000 | 2,000,000 | 497 ms (248.5 ns/tel) | 12 ms (6.0 ns/tel) | 4.02 s (2010 ns/tel) | 90,000,015 |
| 4,000,000 | 8,000,000 | 1,978 ms (247.2 ns/tel) | 13 ms (1.6 ns/tel) | 17.93 s (2241 ns/tel) | 360,000,015 |
| 16,000,000 | 32,000,000 | 7,554 ms (236.1 ns/tel) | 13 ms (0.4 ns/tel) | **DNF (>150 s)** | (predicted 1,440,000,015) |

### Headline observations

- **ns-per-tel is a stable per-runtime constant** (the point of the exercise):
  Agda `⟦_⟧K` ≈ **248 ns/tel** at both sizes — the verified reference runtime
  burns tel at a fixed rate. GHC's figure is startup-dominated at these sizes
  (12→13 ms from 1M→4M: the actual loop is ~1 ns/step; process startup ~10 ms).
- **HVM2 interactions per tel = exactly 45** at both sizes (90,000,015 / 2M and
  360,000,015 / 8M, + 15 setup interactions) — an *empirically measured linear
  coefficient* for the tel↔interactions refinement conjecture (R1/R2 in
  `PARALLEL.md`): for this program, `ITRS = 45·cost + 15`.
- Rough runtime ratios at 4M: **GHC 1× · Agda ⟦_⟧K ~150× · HVM2 ~5500×**
  (sequential loop = HVM2's worst case: pure interaction-machine overhead, no
  parallelism to harvest; see `hvm-tree-sum` for the case where HVM2's
  parallelism pays).
- **Agda ⟦_⟧K stays flat across 16×** (248.5 → 247.2 → 236.1 ns/tel): the
  verified reference runtime is a true per-tel constant. GHC's ns/tel keeps
  *falling* (6.0 → 1.6 → 0.4) because its 13 ms is ~all process startup — the
  actual loop is sub-ms even at 32M steps.
- **HVM2 DNF at 16M (>150 s)**: linear scaling from 4M (17.9 s) predicts ~72 s,
  so the miss is **nonlinear degradation** (≈1.44B interactions; memory/GC
  pressure) — this run is what previously destabilized the machine when run
  without a timeout. The interaction *count* law (45·cost + 15) still predicts
  1,440,000,015 ITRS; only the wall-time blows up.

## Safety note (measurement harness)

An early version of the runner ran HVM2 at 16M with no timeout ×3 reps and had
to be killed by hand. The runner (`nix run .#bench-drain`) now: streams each
result as soon as it's measured, wraps every command in `timeout` (60 s
Agda/GHC per rep, 150 s HVM2), runs HVM2 **once** per size, and accepts an
explicit size list (`nix run .#bench-drain -- 1000000`). DNFs are recorded, not
retried.

## Reading

- The **prediction is the constant** across the table row; the runtimes are
  different *realizations* of the same proved budget. work = span here (the
  loop is sequential), so HVM2's parallelism cannot help — this measures raw
  per-interaction speed.
- To see HVM2's parallelism win instead, see the tree fold (`hvm-tree-sum`,
  `ctc/HVM-BACKEND.md`) — not part of this comparison because a tree type is
  not (yet) expressible in `Ty`.

## Reproduce

```sh
nix run .#bench-drain
```
