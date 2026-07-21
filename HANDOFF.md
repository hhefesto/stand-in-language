# Telomare Handoff

## Current State

The active branch implements the Tel2 resource-model pivot and first-class
closures. The goal is bounded time and memory; affinity and EAL are mechanisms,
not ends.

- First-order reuse inserts `CopyS` and charges full `sizeVal` in the exact
  duplication grade. Explicit `copy` uses the same path.
- `A -o B` closures are affine. Reusable code is a promoted closed
  `Bang (Lolly a b)`; `mapc` may select among promoted closed lambdas.
- Agda and Haskell share `CurryS`, `ApplyS`, `MapCS`, and the R2 data
  promotion `PromoteS` (`design/PROMOTE.md`); transport is v5.
- `design/CLOSURES.md` is the accepted closure design.
- Historical `.tel`, `Telomare.Linear`, and `src/Telomare/Compat/` are frozen.

## Standing Objectives

- Tel2 surface syntax converges on telomare0 (the `.tel` language on `master`)
  wherever the resource model permits. `design/SYNTAX.md` is the normative
  mapping, including the deliberate `left`/`right` divergence (tel2 keeps
  sum injections; telomare0 used them as pair projections).
- The space metric is retention-aware live-heap peak (`design/SPACE.md`).
  The streaming `spaceAlg` was not a memory bound and has been deleted;
  the certified replacement is M2.

## Certified Resources

`spec/T3/Bound.agda` now proves both static analyses sound for every core
constructor.

- `costW-sound`: exact work is below `costW`; by adequacy this is a machine fuel
  bound.
- `sizeS-sound`: covered values fit the type-sensitive static word bound.
- `costD-sound`: exact duplication is below `costD`, including copies, probes,
  closures, maps, folds, iteration, and while.
- `spaceS-sound` (`spec/T3/SpaceBound.agda`): the exact live-heap peak
  computed by the dedicated sized interpreter `⟦_⟧S`
  (`spec/T3/Sem/Space.agda`) is below the static `spaceS` — retention
  (tensor siblings, loop tails, map prefixes) is charged, reusing `γW`
  unchanged (closures carry their space peak as their grade).
- Haskell mirrors these as `costW`, `sizeS`, `costD` in
  `src/Telomare/Budget.hs`; the space meter is `evalSp` on untyped sized
  values in `src/Telomare/Space.hs`, the static mirror is `costSp` with a
  partial type rep `TyR` so atomic tops size as one word (unbounded only
  where the type is genuinely lost — see `design/SPACE.md`).
- `--certificate` prints per-entry work, duplication, and space bounds,
  refinable by `--assume-shape 'text<=N'` (runtime-validated by
  `coversValue`). Tic-tac-toe is currently work `init <= 65`,
  `step <= 779`; duplication `init <= 10`, step unbounded (its state
  contains Text; the v1 flag bounds only the input text); space unbounded
  (map/closure result shapes are `topS` in the certified analysis).
  `--meter` prints the exact measured peak (`core peak space: 153` for
  the 5-move win) beside the work line.

Bounds are constants at a supplied `Shape`. Finite duplication bounds for
variable-size inputs require a refined input shape; the all-top CLI entry shape
cannot provide one.

## Verification

The current milestone passes:

- `cabal build all`
- `cabal test telomare-test` (322 vectors, 15 QuickCheck laws)
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
3. **S3 (done)** — optional `let` type annotations via bounded local
   synthesis (`synthType`: variables, literals, tuples, calls/applications,
   `suc`/`add`, `copy`, `prepend`, loop forms via step-def types; lambdas and
   injections still need annotations; `def` annotations stay required).
4. **S4 (done)** — telomare0-style `main` entry sugar (`expandMain`):
   `def main(io: Text * State): Text * State` synthesizes `init`/`step`,
   defaults `type State = Nat;`, halts when the returned state is 0. The
   `main` call is let-bound with a plain variable so recursive `main`
   bodies still take the placement path.
5. **M1 (done)** — `design/SPACE.md` defines the normative live-heap metric
   `spc` (retention explicit: tensor siblings, loop tails, closure envs),
   documents why no `CostAlgebra` instance can express retention, and
   records the `mapS suc` counter-example. `spaceAlg`/`⟦_⟧SP`/`space` are
   deleted from `Graded.agda`.
6. **M2 (done)** — certified static space bound: `spec/T3/Sem/Space.agda`
   (dedicated sized interpreter `⟦_⟧S`) + `spec/T3/SpaceBound.agda`
   (`spaceS`, `spaceS-sound` over `γW`); Haskell meter `evalSp`
   (`src/Telomare/Space.hs`) and static `costSp` (`Budget.hs`), wired
   into `--certificate` and `--meter` (`core peak space` with a
   certified session cap `max(init, step)` when finite). Remaining
   polish for later sessions: an Agda value-coherence lemma for `⟦_⟧S`
   (Haskell hand vectors cover it today) and the two planned QuickCheck
   space laws.
7. **M3 (done)** — `--assume-shape 'text<=N'` refines the certified step
   bounds; every admitted input is validated by `coversValue`
   (`Budget.hs`, the value-level mirror of `γW`) and nonconforming input
   is refused with a nonzero exit, keeping the conditional certificate
   honest. Includes the `TyR` partial type rep threaded through `costSp`
   so atomic tops size as one word (a Nat-state program's init space is
   now finite). Residual gaps for later: the certified analysis returns
   `topS` for map/closure results (so entries that route data through
   `map`/`mapc`/`apply` still print `space unbounded` — fixing it means
   improving the Agda `spaceS` result shapes and re-proving), and the v1
   DSL bounds only the input text, not the machine state, so ttt's step
   duplication cap stays unbounded (its state contains Text).
8. **M4 (done)** — R2 data promotion `promoteS : Ground A → A ⇨ ! A`
   (`design/PROMOTE.md`): Ground excludes `!` so it is never dig; free in
   work and dup (later duplication is priced at its dup sites); depth 0
   (a value is promoted, not a code region). Cross-stack: every Agda
   theorem (work/dup/space/adequacy/placement/abstract) covers it with
   one-line cases; Haskell mirrors in Core/Denotation/Space/Budget;
   transport is v5 with `NPromote` (groundness validated). The elaborator
   accepts open loop seeds of Ground type on the placement path
   (`affine{Iter,Fold,While}OpenFrom`), proving multiplication via an
   open pair seed (`multiplySource`); closure-typed open seeds are still
   rejected. Prelude `dTimes`/`dMinus` wiring is slated with the M5
   stdlib pass; the closed-entry bindings path (`compileClosedLoop`)
   still requires closed seeds.
9. **M5 (nearly done)** — closure-bodied loops are fully certified and
   mirrored: Agda `iterCS`/`foldCS`/`whileCS` proven across
   value/graded/exec/adequacy/placement/abstract/Bound (work+dup
   `fuel *∞ (1 +∞ lollyCostOf …)` with uniform Kripke round bounds;
   space `(nothing , topS)` v1 like mapCS); Haskell `IterCS`/`FoldCS`/
   `WhileCS` (WhileCS carries `STy` for probe sizing) across
   Core/Denotation/Space/Budget/Surface (`UIterC`/`UFoldC`/`UWhileC`,
   placement-only)/Direct; transport **v6** (`iter-clo`/`fold-clo`/
   `while-clo`, round-tripped). REMAINING for M5 close-out: (a) Tel2
   surface forms — extend `mapc`'s pattern to the loops (suggested:
   `iterc count from seed with <selector>`, `foldc input from seed with
   <selector>`, `whilec limit from seed testing <selector> stepping
   <selector>`), elaborated on the placement path via
   `promoteClosureSelector` + the new cores (assemble like Tel2's mapc:
   `IterCS :.: (selector :***: pairCore)`-style with the (fuel, !seed)
   pair; seed promoted closed or via `PromoteS`); (b) richer selectors:
   `matchText` dispatch and let-bound closed lambdas in
   `promoteClosureSelector`; (c) `synthType` for annotated lambdas;
   (d) accept/behavior vectors + HANDOFF/README/SYNTAX updates. Do NOT
   rewrite ttt in the same commit (goldens stay stable).

Every new core constructor remains a cross-stack change: Agda, Haskell,
transport, budget analysis, Ops, and tests. No Bend and no game-specific
compiler behavior.
