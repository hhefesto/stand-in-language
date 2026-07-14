# Telomare 3 — design charter

Status: **charter (M0), 2026-07-13.** This document is the living design record
of telomare3; it grows with each milestone. Lineage: telomare1 = the `src/`
Haskell compiler around `Possible.hs`; telomare2 = the greenfield design
(`TELOMARE2-DESIGN.md`, `telomare2.agda`) plus its empirical program
(`VALIDATION.md`, `T2-BEND-BACKEND.md`). Telomare3 restarts implementation
from first principles — denotational design as Conal Elliott practices it:
meaning functions first, homomorphism laws as specifications, implementations
**calculated** from them — and makes telomare2's central empirical finding
*definitional*:

> **Possible.hs recursion-limit inference and EAL box-depth inference are the
> same analysis.** (VALIDATION.md: box-nesting order = sizing dependency
> order on the whole `{t,s,b}` fragment; levels recoverable structurally,
> budgets by evaluation.)

## 1. Firm decisions

- Whole compiler, core-first. Semantic core (the Possible-successor) before
  parser and backends.
- `telomare3/` cabal package in this repo; `Telomare3.*`; GHC 9.6; one
  haskell-flake project shared with telomare1.
- **Agda-first**: `telomare3/spec/` is the source of truth (`--safe`, zero
  postulates; imported metatheory cited in comments, never axiomatized).
  Haskell mirrors the spec constructor-for-constructor; Agda `refl` examples
  become Haskell test vectors 1:1 by name.
- **New surface language**, telomare spirit (total, bounded, refinements,
  `{test,step,base}`-spirit recursion), syntax free to surface the EAL
  discipline as *iteration levels*. `tictactoe` hand-ported as north star;
  telomare1 is the oracle.
- telomare1 and `bend/` on hold: zero edits, must keep building.

## 2. The design thesis

Two semantic layers connected by erasure; every compiler analysis is a
calculated approximation of one of them.

1. **Types & refinements denote first.** `⟦unit⟧=1`, `⟦nat⟧=ℕ`,
   `⟦A⊗B⟧=×`, `⟦A⊕B⟧=⊎`, `⟦list A⟧=List`; refinement `{x:A | φ}` = subset
   type `Σ ⟦A⟧ ⟦φ⟧`. Refinements enter the semantics — in telomare1 they
   were load-bearing (removing `validBoard` makes programs unsizable) but
   undenoted.
2. **Surface category S** — cartesian, distributive, free dup/weakening,
   fuel-explicit `iter/fold/while` forms — with `⟦_⟧V^S : S → Set`. Totality
   is manifest (structural recursion; Agda's termination checker is the
   proof). The program denotation, fixed once and never changed:

   ```
   ⟦Program In Out⟧ = ( φ    : decidable refinement on ⟦In⟧
                      , f    : ⟦In⟧ → ⟦Out⟧ ⊎ Err   -- total; inr exactly off φ
                      , cert : Certificate )         -- tower height, budgets, grades
   ```

   The cost certificate is part of the denotation of a *compiled* program —
   "knowable bounds" is a semantic promise, not a compiler feature.
3. **Core category E** — telomare2's affine SMC + EAL exponential, unchanged
   in spirit: contraction `dupS` only at `!A`; promotion `boxS` (functorial)
   and `boxValS` **empty-context only** (`(unit ⇨ B) → (unit ⇨ !B)`; the
   general form smuggles contraction — the telomare2 formalization
   discovery); `mergeS`; **no dereliction, no digging**; recursion only as
   fuel-carrying `iterS/foldS/whileS`, output one level deeper. Erasure
   `ε : E → S` strips decoration; telomare2's `⟦!A⟧=⟦A⟧` is upgraded to the
   **factorization law**

   ```
   ⟦_⟧V = ⟦_⟧V^S ∘ ε
   ```

   — decorations are semantically invisible *as a functor identity*.
4. **One graded interpretation.** telomare2.agda's four hand-written
   resource functors (work `⟦_⟧C`, dup `⟦_⟧D`, space `⟦_⟧SP`, execution
   `⟦_⟧K`) collapse into one `⟦_⟧G` parameterized by a `CostAlgebra`
   (ordered commutative monoid, sequential/parallel compositions, per-prim
   `charge`). Functoriality and precision-with-slack **adequacy** (run with
   the computed budget ⇒ finish with 0 fuel) are proved once, generically.
5. **Placement as a universal property (debt 2).** For surface `M`, the
   decorations `D(M) = ε⁻¹(M)` are ordered by the box vector;
   `place(M) = ⋀ D(M)` when nonempty, else Tier 2. Theorem to prove: on the
   compiler-owned fragment (boxes only at iteration + contraction sites),
   `D(M)` is meet-closed, so the least decoration exists. The
   `Levels.hs`-style structural recipe (containment + parameter-offset
   summaries) becomes the algorithm *proved against* `place-least`.
   Fallback: minimal + canonical tie-break (latest-boxing), documented.
6. **The Possible-successor = calculated abstract interpretation.** Fuel is
   data, so sizing collapses from telomare1's church-tower search (the
   15-deep `handleOther` CPS tower, ~2100 lines) to **value-range analysis
   of one `nat` per iteration site**. Abstract domain `Shape`
   (`zero | pair | either | ivar path | anyUpTo n | ⊤`) with meaning `γφ`
   **parameterized by the input refinement** — the analysis starts from
   `α(Σ⟦In⟧φ)`, so "refinements bound open input" is the definition of the
   initial abstract value, and refinement predicates must be ordinary
   programs the abstract interpreter can run. Transfer functions are
   calculated as best abstractions of the collecting semantics (soundness =
   a logical relation per combinator; state optimality where the calculation
   closes, honesty where only ⊆ holds). Budget of a site = sup of the fuel
   reaching its `nat` port; **control structure = recursion on the level
   assignment** (`foldByLevel (place M)`), making VALIDATION's S2 (inner
   site sized to the max over outer iterations — Girard's level-by-level
   bound) the *definition* rather than an emergent behavior. A **stability
   lemma** (`testFailsWithin B ⇒ ⟦while⟧V (B+k) ≡ ⟦while⟧V B`) replaces
   telomare1's dynamic `AbortRecursion` probing, and telomare1's "+2
   padding" (VALIDATION S1) is **derived** from the elaboration as a
   refl-class lemma (debt 3). `⊤` at a fuel port = unsizable = compile
   error, phrased in refinement vocabulary.
7. **`!` gets a real denotation (debt 1; timeboxed, non-blocking).** Length
   spaces over an EAL resource monoid (Dal Lago–Hofmann): `⟦A⟧L = (points,
   majorization relation)`; `⟦!A⟧L` has the *same points and a genuinely
   different space*; `dupS` exists *because of* the bang structure. Laws:
   `U ∘ ⟦_⟧L = ⟦_⟧V`; grades are homomorphic images of realizer cost. Also
   the arbiter for telomare2 §14.1 (foldS boundary typing): if the pragmatic
   typing admits no realizer, the list must stratify. Fallback: record "no
   intrinsic denotation for `!`" as an explicit, documented design axiom
   (never a `postulate`) and keep the graded semantics as the only cost
   layer. Nothing downstream depends on this milestone.
8. **Tier 2 as semantics (debt 4).** The fuel-metered interpreter over S has
   its own adequacy theorem, plus the **fidelity theorem**
   `⟦place M⟧V = ⟦M⟧V^S`: the tiers compute the same function, tier
   assignment is observationally invisible, "deoptimize, never reject" is a
   theorem schema. Budgets are tier-agnostic; only levels are Tier-1-only —
   an unstratifiable program still gets static budgets and adequacy. The
   intensional residue (`λn. n n` denotes a fine Set function) is honest:
   the Set layer keeps its meaning; the resource layer legitimately has more
   structure to satisfy.
9. **Surface requirements (semantics, not syntax).** Surface recursion
   *means* its fuel-elaboration at the inferred budget (no independent
   partial semantics exists to diverge from; stability makes the choice of
   sufficient budget irrelevant). Error taxonomy fixed now: *unstratifiable*
   → Tier-2 **notice** in iteration-level vocabulary; *unsizable* → **error**
   in refinement vocabulary ("the input reaching this iteration is
   unbounded; add an assert that bounds it"); runtime refinement failure →
   error value in the transcript. Users never write a level; the per-binding
   level report (`name` copied k iteration-levels deep, tower height,
   budgets, tier) is standard build output. Boxes/`!`/linearity never appear
   in any user-facing message.

## 3. The four debts → milestone mapping

| §16 debt (TELOMARE2-DESIGN.md) | telomare3 resolution attempt | Milestone |
|---|---|---|
| 1. `!` has no denotation | length spaces over an EAL resource monoid; `U∘⟦_⟧L=⟦_⟧V`; success = a morphism at `!A` with no counterpart at `A` | M5 (timeboxed) |
| 2. placement has no universal property | `place` = least decoration in the erasure fiber; meet-closure theorem on the compiler-owned fragment; algorithm proved against `place-least` | M3 |
| 3. grades machine-anchored | cost object = resource monoid ℳ; every backend a monotone monoid homomorphism (45 ITRS/tel = ratio of two images); +2 padding derived from elaboration | M1 (⟦_⟧G) + M4 (derivation) |
| 4. intensional discipline vs extensional semantics | Tier 2 specified as a semantics with adequacy + fidelity theorem; budgets tier-agnostic | M7 (spec parts in M3/M4) |

## 4. Milestones and exit criteria

(Statuses mirrored in root `HANDOFF.md`.)

- **M0 — scaffolding + handoff restart.** `telomare3/` package (lib + exe +
  test + trivial `spec/Everything.agda`), root `cabal.project`, flake wiring
  (`apps.telomare3`, `checks.telomare3-spec`, agda+stdlib in the devShell),
  `HANDOFF.md` restarted (old → `design/HANDOFF-TELOMARE2-ARCHIVE.md`), this
  charter. *Exit:* `nix run .#telomare3` works; `nix flake check` green;
  existing apps/packages regression-checked; `agda --safe design/telomare2.agda`
  passes in-branch; `nix run .#format-lint` passes.
- **M1 — Agda core spec.** Port telomare2.agda → `spec/T3/Core/*`,
  `spec/T3/Sem/{Value,Graded,Exec}`, `spec/T3/Adequacy`; §14 decisions
  recorded in comments (depth on `Ty`; foldS pragmatic typing + M5 arbiter
  pointer; add `whileS`, ⊕-error prims); four functors → one `⟦_⟧G`.
  *Exit:* spec check green; zero postulates; telomare2 §10 examples reprove
  with identical numbers by refl.
- **M2 — Haskell mirror + property tests.** `Telomare3.Core` (GADT,
  haddocks cite Agda definitions), `Telomare3.Denotation`;
  `test/SpecVectors.hs` (Examples.agda 1:1 by name), `test/Laws.hs`
  (QuickCheck: grade functoriality, adequacy slack, dup-grade ≡ 0 on the
  affine fragment). *Exit:* `cabal test telomare3` green; flake check green.
- **M3 — surface + placement.** `spec/T3/Surface/*`, `spec/T3/Place.agda`
  (ε, factorization, decoration order, meet-closure on the fragment,
  `place`, `place-least`; the `λn. n n` shape shown to have empty fiber).
  Haskell levels-half of `Telomare3.Infer`. *Exit:* spec green incl.
  `place-least`; levels on VALIDATION probe shapes match telomare1
  `--emit-levels` (tictactoe towerHeight 3, `whoWon.board : !!`,
  `newBoard : !`), fixtures in `test/InferOracle.hs` with producing commands.
- **M4 — budgets.** `spec/T3/Abstract/{Domain,Collect,Transfer,Budget}`
  (Shape + γφ, calculated transfer functions with per-combinator soundness,
  `foldByLevel`, stability lemma — per elaboration pattern if the general
  form stalls, soundness corollary: budget ⇒ K-adequacy on all refined
  inputs). Haskell mirror completes `Telomare3.Infer`. *Exit:* spec green;
  S1/S2/S3 as refl checks on dPow/minus ports; budgets match telomare1
  churchK modulo the derived padding (dPow k=5,6,8; whoWon {10}{5}{3};
  pow = no sites).
- **M5 — `!` denotation (timeboxed ≈ one milestone; parallelizable after
  M1).** `spec/T3/Resource/Monoid.agda`, `spec/T3/Sem/Length.agda`. *Exit:*
  the three named theorems green, or the design-axiom fallback documented
  here.
- **M6 — surface language.** Syntax section here first, then
  `Telomare3.Parser` (megaparsec) + `Telomare3.Elaborate`;
  `examples/prelude.t3`. *Exit:* golden + round-trip tests; elaborated
  examples denote correct values and infer expected levels/budgets;
  `nix run .#telomare3 -- --check examples/prelude.t3` exits 0.
- **M7 — Tier-2 evaluator + tictactoe.** `Telomare3.Eval` (metered graph
  reduction consuming M4 budgets; Tier 1 labeled-fan runtime explicitly
  post-M7); game IO loop; `examples/tictactoe.t3`. *Exit:* transcript
  **byte-parity** vs `nix run . -- tictactoe.tel` on ≥3 scripted move
  sequences; no fuel-fault on any parity run; wall/steps recorded against
  the 45 ITRS/tel and ~240 ns/tel anchors (informational).

## 5. Testing / oracle strategy

1. **Agda → Haskell vectors** (primary): refl equations transcribed 1:1 by
   name; drift breaks one side's check.
2. **Law-level QuickCheck**: random core terms must satisfy what Agda proved
   — the bridge transferring proofs to the Haskell artifact.
3. **telomare1 as inference oracle** (M3/M4): `--emit-levels` output and
   `--emit-hvm` churchK numbers on the VALIDATION probe shapes; each fixture
   records the exact producing command.
4. **telomare1 as semantic oracle** (M6/M7): paired `.tel`/`.t3` twins
   compared by output, culminating in tictactoe transcript parity.

## 6. Risks / falsifiers

- Length spaces too heavy or foldS realizability fails → design-axiom
  fallback (M5 is deliberately non-blocking).
- Meet-closure fails beyond the compiler-owned fragment → minimal +
  canonical tie-break spec.
- Shape domain explodes on nested iteration → widen earlier via
  `anyUpTo`/`⊤`; the failure surface is "add a refinement" errors — the same
  UX telomare1 users already know.
- Level/budget connecting theorem fails in a corner → budgets fall back to
  unstratified whole-program abstract runs (correctness unaffected; only the
  `foldByLevel` structure lost).
- **Global falsifier:** if the calculated transfer functions cannot
  reproduce S1/S2/S3 on the probe ports, "Possible ≡ EAL inference" was
  empirics, not essence — that finding gets recorded here loudly, not
  papered over.

## 7. Progress log

- **2026-07-14 (M4 — DONE): budgets by calculated abstract interpretation.**
  `spec/T3/Abstract.agda` (--safe, 0 postulates): `Shape` domain with
  meaning γ (topS/natLE/pairS/sumS/listS/bangS; the input refinement is
  the initial shape), sound join `_⊔S_`, budget trees `BudgetD` indexed
  by the M3 recursion skeletons (Maybe ℕ per site; nothing = unsizable ⊤
  = a Tier-2 NOTICE, never a rejection), and `transfer` — per-combinator
  best abstractions with trivially-sound topS fallbacks; loops are
  fuel-bounded abstract unrolling (`aiter`): shapes joined over every
  prefix, budgets joined over every unrolling, so **VALIDATION S2 (inner
  site = max over outer iterations) is the definition** and S3 is
  sequential composition.  **Proved**: `sound` (the logical relation
  γ s a → γ (transfer f s) (⟦f⟧V a), loops via `aiter-covers` /
  `afold-covers` / `whileV-runs-as-iterV`) and `while-stable` (any
  sufficient budget returns the same value — replaces telomare1's
  dynamic AbortRecursion probing).  `spec/T3/Examples/Budgets.agda`:
  budgets compute by refl — S1 (double: budget 5), S2 (a depth-2 tower
  whose inner fuel grows 4,5,6 across 3 outer rounds → inner budget 6),
  S3 (producer output 6 sizes the consumer), whoWon strata (8,3),
  church-literal arithmetic (no sites), unbounded fuel (⊤ notice).
  **churchK oracle mapping**: telomare1 k = semantic bound + 2
  (VALIDATION S1's measured elaboration constant): dPow-shape (3,6) ↦
  (5,8); whoWon (8,3) ↦ (10,5).  Haskell mirror `Telomare3.Budget`
  (ShapeH untyped; the GADT index does the typing) with
  `test/BudgetOracle.hs` vectors 1:1 by name — all green.
- **2026-07-14 (M5 — attempted; ARBITER FIRED; design axiom recorded).**
  `spec/T3/Sem/Length.agda`: the candidate intrinsic denotation for `!`
  (Dal Lago–Hofmann length spaces) was attempted over the simplest
  resource monoid — additive majorization in the word-size model — and
  the charter's arbiter test fired with a MACHINE-CHECKED negative:
  `iterS-not-additive` proves the fuel-carrying iteration (pragmatic
  typing, §14.1) admits NO additive realizer (a cons-ing step grows the
  output by 2 words per fuel unit while the input stays 2 words; any
  claimed constant c is beaten at fuel c+1).  **Design axiom (documented,
  not postulated)**: an intrinsic `!`-denotation needs a resource monoid
  with genuine elementary growth (Dal Lago–Hofmann's
  polynomial/elementary monoids), deferred; the graded semantics remains
  the sole cost layer — telomare2's position, now held consciously WITH
  a machine-checked reason.  Nothing downstream depends on it (as
  designed).

- **2026-07-14 (M-tel — DONE): the .tel compatibility runtime.**  New
  objective (user): every .tel program that runs on telomare1 runs on
  telomare3, with full interactive IO — spirit-level equivalence required,
  byte-level achieved on everything measured.  Architecture
  (`telomare3/src/Telomare3/Tel/{Frontend,Eval,Loop}.hs`, new CLI):
  * **Frontend**: telomare1's Parser/Resolver reused as a library
    dependency (parseModule → main2Term3/main2Term3let, mirroring
    compileMain's two-track typecheck quirk), then `term3ToTel` converts
    Term3 to the telomare3 IR — mirroring telomare1's convertPT including
    the refinement-wrapper runtime encoding (checks RUN at runtime),
    EXCEPT: **no Possible.hs**.  Where sizing installs a church tower
    `SetEnv^(n+1) Env`, telomare3 installs a native `TUnbounded` node.
  * **Runtime** (the metered Tier-2 evaluator): an environment machine
    over the 8-primitive core.  `{t,s,b}` recursion = a `VRec` value (the
    limit of telomare1's ladder `rWrap^n(abort)`) that unrolls ONE step
    per demanded recursive call, metered per site — "deoptimize, never
    reject" operational.  Two deliberate deviations, both load-bearing:
    lazy gate selection on the `iteB_` shape (required so the unbounded
    ladder stops at the base case; telomare1 eagerly evaluates and then
    discards dead branches), and abort values (`VAborted`) with
    telomare1's exact propagation/discard semantics — the first
    implementation threw at abort creation and was FALSIFIED by
    simpleplus (telomare1 discards the Zero-input iteration's failed
    refinement; the fix reproduced its transcript exactly).
  * **IO loop**: funWrap/evalLoopCore protocol (main runs first on Zero;
    prompts are program output; state Zero ends silently — telomare1's
    "done" is discarded by `void`, verified empirically); EOF ends the
    loop cleanly where telomare1 crashes (documented improvement).
  * **CLI**: optparse-applicative; `--certificate` prints the structural
    levels report (Telomare.Levels reused); `--meter` prints
    applies/gates/per-site unrolls to stderr; `--max-steps` = fuel cap.
  * **Results**: tictactoe plays interactively via
    `nix run .#telomare3 -- tictactoe.tel`; four scripted games (win,
    quit, invalid-input, tie) are BYTE-IDENTICAL to telomare1 golden
    transcripts (`telomare3/test/golden/`, captured from the telomare1
    binary); simpleplus and tc_ultra_minimal transcripts match
    telomare1's; `sizing_fail5.tel` — which telomare1 REJECTS with
    RecursionLimitError — runs on telomare3 (the never-reject
    improvement, asserted in the suite).  Compilation is near-instant
    (no ~3-minute sizing pass).  Parity suite: 7 vectors in
    `test/ParityTel.hs` over frozen program copies in `test/programs/`
    (cabal sdist only ships declared files — `extra-source-files` needed
    for the nix sandbox).  All 41 vectors + 9 laws green; flake gates
    green.
  * **Scope notes**: files that don't `import Prelude` (minimal.tel,
    simpleplus2-8, …) don't resolve on telomare1's CLI either (no
    implicit Prelude) — out of scope; telomare3 reports a clean resolver
    error where telomare1 crashes.  ttt_whowon.tel is the known-broken
    probe (telomare1's sizing crashes on it).  Remaining honest
    deviation: an abort value created on a live path but discarded by a
    later Left/Right projection succeeds on telomare1 and errors here —
    not observed in any real program; parity suite would catch it.

- **2026-07-13 (M1 — DONE).** `telomare3/spec/T3/{Core/{Ty,Syntax},
  Sem/{Value,Graded,Exec},Adequacy,Examples/Basics}.agda` — telomare2.agda
  ported and consolidated: ONE graded interpretation `⟦_⟧G` over a
  `CostAlgebra` record (work/dup/space as instances) replaces the four
  hand-written functors; generic value-coherence `G-val` proved once for
  every algebra; precision-with-slack adequacy restated over the work
  instance (plus `adequateV` against `⟦_⟧V`).  §14 decisions recorded in
  headers (depth on Ty; foldS pragmatic typing with the M5 arbiter
  pointer).  New primitives with full semantics AND proofs: `whileS`
  (fuel+test; stop=inj₁) and `guardS` (the ⊕-error refinement primitive);
  both PROBE their input without consuming it, and that implicit copy is
  priced (`chargeProbe`: dup grade sizeT per probe — never free).  All
  telomare2 §10 examples reprove with identical numbers by refl; new
  countDown/positive examples exercise the additions.  Zero postulates.
  Toolchain: the spec needs `telomare3-spec.agda-lib` (depend:
  standard-library) — without it the sandboxed flake check cannot resolve
  the stdlib (the devshell only worked via ~/.agda defaults); the check
  also needs a UTF-8 locale (glibcLocales + LC_ALL in the runCommand).
- **2026-07-13 (M2 — DONE).** `Telomare3.Core` (GADT, promoted Ty, Val
  family, STy singletons carried by exactly the constructors whose grading
  reads types: DupS/GuardS/WhileS) + `Telomare3.Denotation` (evalV, evalG
  over a CostAlgebra record, workAlg/dupAlg, evalK).  Documented
  deviations: chargePrim specialized to the distinguished charges; the
  space instance not yet mirrored (needs full singleton threading; the
  Agda remains its definition).  `test/SpecVectors.hs` = all 24
  Examples.agda refl facts 1:1 by name; `test/Laws.hs` = 6 properties
  ×1000 cases (G-val coherence, precision, adequacy, affine-dup-zero,
  work/dup functoriality).  The bridge earned its keep immediately: the
  naive affine-fragment property was falsified on a WhileS-capped program
  — correctly, since probes charge the dup grade; the affine fragment
  excludes probe-carrying constructors by definition.
- **2026-07-13 (M3 — DONE).** `T3/Surface/{Ty,Syntax,Sem}.agda` (box-free
  UTy, cartesian `_⇨U_` with free dupU, `⟦_⟧VS`) and `T3/Place.agda`, all
  `--safe`, zero postulates:
  * **Factorization** `ε-factor : stripV ∘ ⟦_⟧V ≡ ⟦ ε _ ⟧VS ∘ stripV` —
    decorations are semantically invisible as a functor identity (the
    fidelity theorem's semantic half).
  * **Placement as a universal property** (debt 2 discharged on the
    fragment): decorations abstracted to level-annotated recursion
    skeletons (`Deco`), stratification (`Solves`), pointwise-⊓
    **meet-closure** (`solves-meet` — why the least decoration exists),
    the structural walk `place` (the Levels.hs recipe: containment +
    offsets, no search) with **`place-least`**, and the bridge
    **`core-dominates`**: every well-typed core term IS a solution
    (`core-solves`, boxes only loosen via n≤1+n) sitting above the
    placement of its own erasure.  Same-level feedback (`λn.n n`) is the
    unsatisfiable constraint ℓ ≥ ℓ+1 (`sameLevelFeedback-unsat`); in the
    first-order core the pattern is unwritable by construction — the
    higher-order emptiness belongs to M6 elaboration.
  * **Haskell**: `Telomare3.Infer` = spec mirror (place/solves/meetD,
    QuickChecked against the proved theorems) + the named-definition
    layer (paramOffsets/occDepth/walk — the Levels.hs recipe on a
    mini-AST).  **Oracle gate green** (`test/InferOracle.hs`): a
    structural reduction of tictactoe.tel reproduces telomare1's
    `nix run . -- --emit-levels tictactoe.tel` facts — towerHeight 3,
    `whoWon.board : !!`, `main.input : !!`, `main.newBoard : !`,
    `foldr.f : !`, `d2c.b : !`, site strata {0,1,2}; plus dPow
    (towerHeight 3, strata 0,1,2) and pow-on-church (no sites — the
    documented scope divergence).

- **2026-07-13 (M0 — DONE, all exit criteria verified):** charter written;
  `telomare3/` package scaffolded (lib/exe/test placeholders + trivial
  `spec/Everything.agda`); root `cabal.project` (haskell-flake's parser
  needs the `packages:`-then-newline layout); flake wiring:
  `apps.telomare3`, `checks.telomare3-spec` (runCommand + `agda --safe`),
  `agdaWithStdlib` added to the devShell (retires the cross-branch
  `nix develop ?ref=agda` trick — `design/telomare2.agda` re-checks
  in-branch under Agda 2.8.0/stdlib 2.3); `HANDOFF.md` restarted,
  predecessor archived to `design/HANDOFF-TELOMARE2-ARCHIVE.md`.
  Verified: `nix run .#telomare3`; `nix flake check` green (telomare +
  telomare3 + telomare3-spec); devshell `cabal build/test telomare3`;
  legacy regression (`nix run . -- tictactoe.tel` sizes and plays to the
  first prompt); `nix run .#format-lint` green — which required clearing
  pre-existing hlint/stylish debt in prior-session telomare1 files
  (HvmBackend, HvmBackendCcc, Levels, T2Backend, app/Main: formatting,
  unused pragmas, two lambda→flip, one map→fmap; functionality re-verified
  by the flake check rebuild). `.agdai` files untracked (gitignored).
