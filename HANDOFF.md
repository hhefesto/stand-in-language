# Telomare Handoff

## Current State

The active branch implements the Tel2 resource-model pivot and first-class
closures. The goal is bounded time and memory; affinity and EAL are mechanisms,
not ends.

- First-order reuse inserts `CopyS` and charges full `sizeVal` in the exact
  duplication grade. Explicit `copy` uses the same path.
- `A -o B` closures are affine. Reusable code is a promoted closed
  `Bang (Lolly a b)`; `mapc` may select among promoted closed lambdas.
- Agda and Haskell share `CurryS`, `ApplyS`, and `MapCS`; transport is v4.
- `design/CLOSURES.md` is the accepted closure design.
- Historical `.tel`, `Telomare.Linear`, and `src/Telomare/Compat/` are frozen.

## Certified Resources

`spec/T3/Bound.agda` now proves both static analyses sound for every core
constructor.

- `costW-sound`: exact work is below `costW`; by adequacy this is a machine fuel
  bound.
- `sizeS-sound`: covered values fit the type-sensitive static word bound.
- `costD-sound`: exact duplication is below `costD`, including copies, probes,
  closures, maps, folds, iteration, and while.
- Haskell mirrors these as `costW`, `sizeS`, and `costD` in
  `src/Telomare/Budget.hs`.
- `--certificate` prints per-entry work and duplication bounds. Tic-tac-toe is
  currently work `init <= 65`, `step <= 779`; duplication `init <= 10`, with
  step unbounded for arbitrary input because `Text` has unrestricted size.

Bounds are constants at a supplied `Shape`. Finite duplication bounds for
variable-size inputs require a refined input shape; the all-top CLI entry shape
cannot provide one.

## Verification

The current milestone passes:

- `cabal build all`
- `cabal test telomare-test` (282 vectors, 15 QuickCheck laws)
- `(cd spec && agda --safe Everything.agda)`
- `git diff --check`

Run `nix flake check "path:."` and `nix run "path:.#format-lint"` before the
next release or handoff.

## Next Milestones

1. Decide and document the space metric. Existing `spaceAlg` appears to measure
   streaming/local peak, not total live heap; do not advertise it as a memory
   bound until this is resolved.
2. After that decision, prove and mirror the static space bound using `sizeS`.
3. Add user-declared input-shape refinements so the CLI can report finite
   size-dependent duplication/space caps.
4. Implement R2 data promotion: copyable open seeds plus residual live context
   (`PromoteS`), unblocking `multiplyNat` and fold-with-retained-state.
5. Add closure-bodied `FoldCS`/`IterCS`/`WhileCS`, richer `mapc` selectors, and
   apply-head synthesis beyond variables/calls.

Every new core constructor remains a cross-stack change: Agda, Haskell,
transport, budget analysis, Ops, and tests. No Bend and no game-specific
compiler behavior.
