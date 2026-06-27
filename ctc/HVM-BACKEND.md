# ConCat → HVM2: a code-emitting CCC backend

This joins **ConCat** (Conal Elliott's compile-to-categories) with **HVM2**
(Higher Order Co's parallel runtime, via Bend): a telomare morphism — written as
an ordinary Haskell port and run through ConCat's `toCcc` — is compiled into a
runnable **HVM2 program**.

The idea, in Conal's own framing: *HVM2 implements the cartesian-closed-category
classes.* We define a new ConCat category `HVM` whose CCC-class instances **emit
Bend code**, so `toCcc f :: HVM a b` is a Bend/HVM2 program.

## How it works

- **`ctc/src/HVM.hs`** — a new category `newtype HVM a b`, modeled on ConCat's
  `Syn`, instancing `Category, ProductCat, MonoidalPCat, BraidedPCat,
  AssociativePCat, UnitCat, TerminalCat, ClosedCat, NumCat, MinMaxCat, ConstCat`
  (+ the cocartesian classes). Each method renders a **Bend combinator name**:
  `id→idC`, `(.)→comp`, `(***)→cross`, `exl/exr/dup`, `addC/mulC/minC/maxC`,
  `apply→applyC`, `curry→curryC`, … `Ok HVM = Yes1` (accept all types, like `Syn`).
- The emitted term is **point-free** (no reused variables), so it is *linear in
  size* — there is **no fan-out blowup**. This is exactly the failure that broke
  the ConCat→`Circuit` backend on the sorting network (`mkGraph`/`graphDot`
  diverged); the HVM2 backend renders the same network fine.
- **`bendPrelude`** (in `HVM.hs`) — a small Bend library implementing each
  combinator (`comp(g,f) = λx. g(f(x))`, `cross`, `exl`, `minC` via `switch
  (a<b)`, `curryC`, `applyC`, …). Bend auto-inserts fans for the `dup` combinator,
  so duplication is handled by the runtime.
- **`ctc/src/HvmMain.hs`** — `toCcc`s the demo morphisms into `HVM`, assembles
  `prelude ++ main` and writes `out/hvm-*.bend`.

## What runs (verified on HVM2)

`nix run .#ctc-to-hvm` emits the Bend sources, runs them on HVM2 (`bend run-c`),
and emits the raw HVM2 interaction-nets (`bend gen-hvm` → `out/hvm-*.hvm`):

| morphism | emitted term (abbrev.) | HVM2 result |
|---|---|---|
| `sqr` | `comp(mulC, dup)` | `25` |
| `fibAccStep` | `comp(cross(exr, addC), dup)` | `(4, 7)` |
| `mergeSort4` | `comp(applyC, …(minC/maxC)…)` | `(((1,2),3),4)` |
| **`mergeSort8`** | a large point-free term | **`[0,1,2,3,4,5,6,7]`** |

`mergeSort8` is the headline: the 8-input sorting network that **could not be
serialized by ConCat's `Circuit` backend** compiles through ConCat→HVM2 and runs
correctly. Same telomare design, a runtime that handles it.

## Bounded recursion via primitives (runtime-sized)

The ConCat plugin can't categorify recursion — but the *per-node* morphisms can,
and **HVM2 runs recursion natively (in parallel)**. So recursion enters as a
**primitive**: `toBendIterate`/`toBendFold` (in `HVM.hs`) emit the toCcc'd
sub-morphisms as **named Bend globals** and a specialized recursive loop that
calls them by name. The recursion size is a **runtime CLI argument**, so the
`.bend` is constant — no unrolling.

| program | what goes through `toCcc` | recursion (primitive) | result |
|---|---|---|---|
| `hvm-fib-iter` | `fibAccStep` (step) + `fibInit` | sequential `iterGo` (= telomare `iterS`) | `fib(n)` for runtime `n` (e.g. 30 → 832040) |
| `hvm-tree-sum` | `id` (leaf) + `(+)` (combine) | **parallel** `foldGo` over a 2^d tree | `2^d` for runtime depth `d` (d=18 → 262144 in ~0.7s, 15.4M interactions) |

`foldGo`'s two recursive calls are independent, so HVM2 reduces them **in
parallel** — the genuinely parallel-scaling case. (Why named globals, not a
generic combinator that *passes* the step: HVM2 mis-duplicates a higher-order
tuple-function cloned across a recursion; a global reference is fresh per call and
runs correctly.) Run via `bend run-c out/hvm-fib-iter.bend <n>` /
`bend run-c out/hvm-tree-sum.bend <d>`.

## Scope & honest limits

- **Agda↔ConCat**: ConCat is a GHC plugin on *Haskell*, so the morphisms go
  through as Haskell ports (in `HvmMain.hs`); `telomare.agda` is the verified
  spec. No literal Agda→ConCat path.
- **What the *plugin* compiles**: the first-order combinational fragment
  (products, closed, numeric, min/max). **Bounded recursion** (`iterS`, tree
  `fold`) reaches HVM2 too — but as **primitives** (named globals + a specialized
  loop), not via the plugin; only the per-node morphisms go through `toCcc`.
- **Not yet through the plugin**: an `Either`-`case` leaves an un-rewritten
  `toCcc''` stub (cocartesian instances exist but aren't exercised end-to-end), and
  general structural recursion over arbitrary inductive types (beyond the
  fixed `iterS`/binary-tree-`fold` primitives) would each need its own primitive.
- **Unverified**: this is a code generator, not a verified compiler. The emitted
  HVM2 program is checked by *running* it and comparing to the Agda semantics
  (sqr=25, fib-step=(4,7), sorts sort). A proof that the emission preserves
  meaning (and the cost refinement of `PARALLEL.md`) is future work.
- Scalars are `Int`/u24 (exact); `subC`/`negateC` exist but the demos use
  add/mul/min/max only.

## Run it
```sh
nix run .#ctc-to-hvm        # emit out/hvm-*.bend, run on HVM2, emit out/hvm-*.hvm
nix build .#ctc            # builds telomare-ctc (diagrams) + telomare-hvm (this)
```
