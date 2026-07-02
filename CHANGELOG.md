# Revision history for telomare

## Unreleased -- `agda` branch: {x,y,z} reified + space functor

* `whileS` — telomare's limited recursion `{x,y,z}` (tail form) as a syntax
  primitive: fuel-bounded guarded loop with ON-DEMAND metering, full precision
  proof (`while-prec`). Derived twin `whileD = iterS ∘ guardS` (reserved-capacity
  billing) kept with machine-checked value agreement (`tictactoe.agda`).
* `natOutS`/`distlS` (nat destructor + distributivity) — the eliminators that
  made branching-on-numbers expressible; used by tic-tac-toe.
* `tictactoe.agda` — tic-tac-toe as a pure `_⇨S_` program (moves → winner),
  winners proved by `refl`; now on `whileS`, printing cost/reserved/space.
* **Space functor `⟦_⟧SP`** — the fourth resource interpretation (peak live
  size, word model): the `(⊔, +)` cell of the resource-algebra 2×2
  (work `(+,+)`, span `(+,⊔)`, space `(⊔,+)`); span/space duality by `refl`.
* ConCat→HVM2: `toBendWhile` — mechanical emission of the guarded loop (init/
  final/test/body all through `toCcc`; comparisons via OrdCat → Bend u24);
  `hvm-fib-while` verified on HVM2.
* **Run comparison** (`BENCHMARK.md`, `nix run .#bench-drain`): one `_⇨S_`
  algorithm (`drainS`, cost 2N by refl) timed on Agda `⟦_⟧K` (~240 ns/tel,
  flat), native GHC (startup-dominated), and HVM2 (45 interactions/tel;
  DNF at 16M). Timeout-guarded harness (`benchDrain.agda`, `telomare-bench-hs`).
* **Run comparison** (`BENCHMARK.md`, `nix run .#bench-drain`): one telomare
  algorithm (`drainS`) on three runtimes — Agda `⟦_⟧K` (~248 ns/tel, constant),
  native GHC, HVM2 (`ITRS = 45·cost + 15` measured — empirical R1/R2 data).
  New: `benchDrain.agda`, `telomare-bench-hs`, `hvm-drain-while` emission.

## Unreleased -- `agda` branch (denotational design, ConCat, HVM2)

* **Agda denotational design** (`telomare.agda`): typed syntax `_⇨S_` with three
  homomorphic interpretations — execution `⟦_⟧K`, cost `⟦_⟧C`, and parallel
  work/span `⟦_⟧WS` — and machine-checked adequacy/precision (exact, auto-computed
  tel cost per program). See `README-Agda.md`.
* Added to `_⇨S_`: `minS`/`maxS` (comparators, cost 1); sum types (`_⊕_`,
  `inlS`/`inrS`/`caseS`) for data-dependent branching; recursive lists (`listT`,
  `nilS`/`consS`/`unconsS`); the 8-input Batcher sorting network `mergeSortS`
  (sorts + cost 38, by `refl`); and `lengthS`, a recursive list function via `fixS`
  with a proved exact cost.
* **ConCat circuit diagrams** (`ctc/`): the `_⇨S_` morphisms compiled via Conal
  Elliott's ConCat into circuit SVGs (`nix run .#telomare-ctc-svg`). See
  `ctc/DIAGRAMS.md`.
* **ConCat → HVM2 backend** (`ctc/src/HVM.hs`): a new code-emitting CCC category;
  `toCcc f :: HVM a b` produces a runnable HVM2/Bend program
  (`nix run .#ctc-to-hvm`). See `ctc/HVM-BACKEND.md` and `PARALLEL.md`.
* **Bend/HVM2 apps**: `nix run .#bend-hello`, `nix run .#bend-sort`.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
