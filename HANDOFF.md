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

- Tel2 surface syntax converges on telomare0 (the `.tel` language on
  `master`) wherever the resource model permits, and the convergent syntax
  is the ONLY syntax. Round 1 (2026-07-21) removed `#` comments, the
  `apply` keyword, and the dedicated `f(x)` production (juxtaposition
  subsumes `f(x)`). Round 2 (2026-07-22/23) closed the rest: top-level
  definitions are `name : A -o B = \x -> body` (no `def`); there is one
  `case e of` whose first-arm shape picks nat/text/enum dispatch (no
  `matchNat`/`matchText`); layout replaces semicolons and arm braces;
  `succ`/`add`/`cons`/`prepend` are builtin functions applied by
  juxtaposition; and `main` is the only entry (telomare0-exact Nat shape,
  or `main : Text * State -o Reply State` with `start : Unit -o State` for
  any first-order state), with direct `init`/`step` an error. Every
  shipped `.tel2` program is rewritten in the new style; ttt goldens are
  byte-identical. `design/SYNTAX.md` is the normative mapping, including
  the deliberate `left`/`right` divergence (tel2 keeps sum injections;
  telomare0 used them as pair projections). The enabler for main-only is
  **placed dispatch** (`compilePlacedBody` compiles a match whose arms
  contain recursion: scrutinee direct, recursive arms placed, direct arms
  promoted via `PromoteS`) — no new core constructors.
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
  `coversValue`). Tic-tac-toe is now work `init <= 780`, `step <= 780`
  (both entries route through the single `main`, so init's bound equals
  step's rather than the pre-main `init <= 65` / `step <= 779`);
  duplication unbounded (its state contains Text; the v1 flag bounds only
  the input text); space unbounded (map/closure result shapes are `topS`
  in the certified analysis). `--meter` prints the exact measured peak
  beside the work line.

Bounds are constants at a supplied `Shape`. Finite duplication bounds for
variable-size inputs require a refined input shape; the all-top CLI entry shape
cannot provide one.

## Verification

The current milestone passes:

- `cabal build all`
- `cabal test telomare-test` (352 vectors, 15 QuickCheck laws)
- `(cd spec && agda --safe Everything.agda)`
- `git diff --check`

Run `nix flake check "path:."` and `nix run "path:.#format-lint"` before the
next release or handoff.

## Next Milestones

Syntax convergence (S1–S8, all in `src/Telomare/Tel2.hs`, tracked in
`design/SYNTAX.md`) and the resource milestones (M1–M5) are all done.
Round 1 was S1–S4; round 2 (S5 signature-style defs, S6 unified `case`,
S7 layout, S8 builtin functions, and the main-only entry with placed
dispatch) landed 2026-07-22/23 and removed every legacy form. Only two
convergence candidates were deliberately deferred as future work if ever
wanted — none are outstanding requirements: qualified imports and `let`
list-assignments (both niche telomare0 forms). Goldens
`test/golden/tel2_ttt_*.txt` stayed byte-identical throughout (the
main-form rewrite preserved I/O exactly; only certificate *numbers*
moved, since init and step now share one `main`).

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
9. **M5 (done)** — closure-bodied loops shipped end to end: Agda
   `iterCS`/`foldCS`/`whileCS` certified across value/graded/exec/
   adequacy/placement/abstract/Bound (work+dup `fuel *∞ (1 +∞ body)`
   with uniform Kripke round bounds; space `(nothing , topS)` v1 like
   mapCS); Haskell mirror + transport **v6**; tel2 surface `iterc`/
   `foldc`/`whilec` (mapc's promoted-selector discipline, Ground seeds
   promoted at the loop boundary, `whilec`'s stepping selector closed);
   `promoteClosureSelector` gained `matchText` dispatch; apply-head
   synthesis was already delivered by S2/S3's `synthType` chains.
   Minor polish left for future sessions: let-bound closed lambdas as
   selector leaves, `synthType` for annotated lambdas and `mapc`
   results, and the M5-era stdlib pass (Prelude `dTimes`/`dMinus`,
   possible ttt rewrite using the new forms — goldens deliberately
   untouched).

Every new core constructor remains a cross-stack change: Agda, Haskell,
transport, budget analysis, Ops, and tests. No Bend and no game-specific
compiler behavior.
