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

## Standing Objectives

- Tel2 surface syntax converges on telomare0 (the `.tel` language on `master`)
  wherever the resource model permits. `design/SYNTAX.md` is the normative
  mapping, including the deliberate `left`/`right` divergence (tel2 keeps
  sum injections; telomare0 used them as pair projections).
- The space metric is retention-aware live-heap peak. The streaming `spaceAlg`
  is not a memory bound and is slated for deletion (M1/M2).

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
- `cabal test telomare-test` (298 vectors, 15 QuickCheck laws)
- `(cd spec && agda --safe Everything.agda)`
- `git diff --check`

Run `nix flake check "path:."` and `nix run "path:.#format-lint"` before the
next release or handoff.

## Next Milestones

Syntax convergence first (S1–S4, all in `src/Telomare/Tel2.hs`, tracked in
`design/SYNTAX.md`), then the resource milestones (M1–M5). Goldens
`test/golden/tel2_ttt_*.txt` stay byte-identical through S1–M3.

1. **S1 (done)** — lexical sugar: `--`/`{- -}` comments, `if/then/else`
   (desugars to `matchNat`, sound for Nat and declaration-ordered enums),
   `[e1, …]` list literals, multi-arg lambdas (curried), multi-binding `let`.
   All parser-level desugarings; elaborator untouched. Note: consuming a
   curried lambda still needs each partial application let-bound (`apply`
   heads are variables/calls until M5).
2. **S2 (done)** — juxtaposition application `f x y`. Parsed as `EApp`,
   normalized away by `resolveApps` right after parsing (bound head →
   `EApply`, def head → `ECall`; lexical scope wins; symmetric for `f(x)`
   call forms). Reserved words excluded from identifiers. `synthType`
   projects through `EApply`, so chains and nested applies elaborate.
3. **S3** — optional `let` type annotations via bounded local synthesis
   (`def` annotations stay required).
4. **S4** — telomare0-style `main` entry sugar synthesizing `init`/`step`
   (halt when next state is 0).
5. **M1** — `design/SPACE.md`: normative live-heap metric; document why the
   `CostAlgebra`/`Interp` abstraction cannot express retention (dedicated
   interpreter required) and delete `spaceAlg`.
6. **M2** — prove the static space bound (`spec/T3/Sem/Space.agda`,
   `spec/T3/SpaceBound.agda`: `spaceS`, `γS`, `spaceS-sound`) and mirror it in
   Haskell (`src/Telomare/Space.hs` untyped sized meter, `Budget.hs` static
   mirror, certificate + `--meter` wiring).
7. **M3** — `--assume-shape` input refinements with runtime `coversValue`
   validation, making ttt's size-dependent caps finite.
8. **M4** — R2 `PromoteS` (copyable open seeds), transport v5, unblocking
   `multiplyNat`/`dTimes`/`dMinus`.
9. **M5** — closure-bodied `IterCS`/`FoldCS`/`WhileCS`, richer `mapc`
   selectors, apply-head synthesis, transport v6.

Every new core constructor remains a cross-stack change: Agda, Haskell,
transport, budget analysis, Ops, and tests. No Bend and no game-specific
compiler behavior.
