# HANDOFF — telomare3 (updated 2026-07-13)

Cross-machine/session state for the **telomare3** effort: a greenfield
reimplementation of telomare from first principles (Conal Elliott-style
denotational design) using everything learned about EAL. Everything that came
before is archived, not maintained: `design/HANDOFF-TELOMARE2-ARCHIVE.md`.

## What this is / how to resume

- Branch `bend-port`. The telomare2 corpus + T2 backend + telomare3 M0 are
  committed ("telomare2 design + T2 backend verdict; telomare3 restart (M0)").
  Commits only when the user asks. Flake builds see only git-*tracked* files —
  `git add` every new file before any `nix build`/`nix run`/`nix flake check`.
- One-command health check: `nix flake check` (builds telomare1 + telomare3,
  runs both test suites, type-checks the Agda spec via `checks.telomare3-spec`).
- The roadmap and its rationale: `design/TELOMARE3-DESIGN.md` (charter) with
  the milestone board below kept in sync.
- telomare1 (`src/`, `telomare.cabal`) and the bend/HVM2 work (`bend/`) are
  **on hold**: zero edits, must keep building; their staged-but-uncommitted
  state is carried as-is.

## Firm decisions (user-stated)

- Whole compiler, **core-first**: semantic core (the Possible-successor,
  where recursion sizing ≡ EAL box-depth/budget inference) comes first;
  parser/backends follow.
- Lives in **`telomare3/`** — its own cabal package (`telomare3`, namespace
  `Telomare3.*`, GHC 9.6, same haskell-flake project), wired via root
  `cabal.project`.
- **Agda-first**: `telomare3/spec/` (`--safe`, zero postulates) is the source
  of truth; Haskell mirrors it constructor-for-constructor. Imported
  metatheory is cited in comments, never axiomatized.
- **New surface language** in the telomare spirit (total, bounded,
  `{test,step,base}`-spirit recursion, refinements); `tictactoe` hand-ported
  as the north-star benchmark, telomare1 as oracle.

## Design lessons inherited (each one paragraph, with pointer)

- **The central thesis, now definitional:** Possible.hs recursion-limit
  inference and EAL box-depth inference are the same analysis
  (`design/VALIDATION.md`: box-nesting order = sizing dependency order on the
  whole `{t,s,b}` fragment). Division of labor validated empirically:
  **levels by structure** (no evaluation — `src/Telomare/Levels.hs` does full
  tictactoe in 37 ms), **budgets by evaluation**.
- **boxVal soundness:** `boxVal : A ⇨ !A` for general `A` is UNSOUND
  (`dup ∘ boxVal` smuggles contraction on an open input). Promotion with
  empty context only: `(unit ⇨ B) → (unit ⇨ !B)`. Discovered while
  formalizing `design/telomare2.agda`; easy to get wrong again.
- **The four §16 debts are the telomare3 agenda** (TELOMARE2-DESIGN.md §16):
  (1) `!` has no denotation — telomare3 attempts length spaces over an EAL
  resource monoid (Dal Lago–Hofmann); (2) box placement has no universal
  property — telomare3 specifies `place` = least decoration in the erasure
  fiber (Galois insertion) and proves the Levels.hs-style algorithm against
  it; (3) grades are machine-anchored — cost object = resource monoid,
  backends = monoid homomorphisms, telomare1's "+2 padding" derived not
  measured; (4) discipline intensional vs semantics extensional — Tier 2 is
  a fidelity *theorem* (`⟦place M⟧V = ⟦M⟧V^S`), deoptimize-never-reject.
- **HVM2 lacks level-annotated fans.** The T2 backend experiment
  (`design/T2-BEND-BACKEND.md`) proved the affine discipline works (+1–2%
  overhead, fixes the OOM class) but depth-2 sharing (`whoWon.board : !!`)
  defeats every single-level forcing regime. Tier 1 proper needs labeled
  fans with levels as labels; **Tier 2 metered reduction is mandatory**, and
  telomare3 does not target vanilla HVM2 for the fast path.
- **Refinements are the totality certificate.** Removing `validBoard`-style
  asserts makes programs UNSIZABLE (`RecursionLimitError`), not merely
  unchecked. In telomare3 refinements denote (subset types), parameterize
  the abstract interpretation's γ, and refinement predicates must be
  ordinary surface programs.
- **Cost anchors** (agda branch `BENCHMARK.md`): ~45 HVM2 interactions per
  tel, ~240 ns/tel on the metered Haskell runtime — the measured ratios of
  two homomorphic images of the one cost object.

## Milestone board (details + exit criteria in design/TELOMARE3-DESIGN.md)

| M | What | Status |
|---|------|--------|
| M0 | Scaffolding (`telomare3/` package, `cabal.project`, flake wiring: `apps.telomare3`, `checks.telomare3-spec`, agda in devShell) + HANDOFF restart + charter | **DONE 2026-07-13** (all exit criteria verified; also cleared pre-existing hlint/stylish debt so `format-lint` is green) |
| M1 | Agda core spec: port `design/telomare2.agda` into `telomare3/spec/T3/*`, collapse the four resource functors into one graded `⟦_⟧G` over a CostAlgebra, adequacy stated once; §10 examples reprove by refl | pending |
| M2 | Haskell mirror (`Telomare3.Core`/`Denotation`) + spec-vector tests (1:1 with Examples.agda) + QuickCheck law tests | pending |
| M3 | Surface category + placement: ε, factorization `⟦_⟧V = ⟦_⟧V^S ∘ ε`, `place`, `place-least`; levels oracle vs telomare1 `--emit-levels` | pending |
| M4 | Possible-successor budgets: Shape/γφ abstract domain, calculated transfer functions, `foldByLevel`, stability lemma; oracle vs telomare1 churchK numbers (dPow 5,6,8; whoWon {10}{5}{3}) | pending |
| M5 | `!` denotation (length spaces; timeboxed, non-blocking; parallelizable after M1) or documented design-axiom fallback | pending |
| M6 | Surface language: syntax design → `Telomare3.Parser` + `Elaborate`; `examples/prelude.t3` | pending |
| M7 | Tier-2 metered evaluator + `examples/tictactoe.t3`; transcript byte-parity vs `nix run . -- tictactoe.tel` | pending |

## How to verify everything

```sh
nix flake check                                   # everything at once
nix run .#telomare3                               # the M0 executable
nix develop --command cabal test telomare3        # Haskell tests (M2+)
nix develop --command agda --safe telomare3/spec/Everything.agda   # spec
nix develop --command agda --safe design/telomare2.agda            # frozen predecessor still checks
# telomare1 oracle commands (M3/M4): telomare --emit-levels / --emit-hvm
#   (each oracle number in test/InferOracle.hs carries its producing command)
```

## Standing constraints (user-stated)

- No python — shell/awk only.
- No commits unless explicitly asked; stage (`git add`) every new file so the
  flake sees it.
- Document progress in the repo's md files; keep THIS file current.
- If any bend/hvm invocation happens (shouldn't this round): timeout-wrap it,
  cap output (`head`), one big-arena binary at a time, kill leftovers via
  `/proc/PID/exe` (never `pkill -f`, it self-matches).

## Archive & evidence pointers

- `design/HANDOFF-TELOMARE2-ARCHIVE.md` — the full telomare1/2-era handoff
  (workstreams A/B, toolchain hazards, GC pinning of bend/hvm).
- `design/TELOMARE2-DESIGN.md` (§12 migration, §14 open questions, §16
  debts), `design/telomare2.agda` (frozen), `design/VALIDATION.md`,
  `design/T2-BEND-BACKEND.md`.
- `bend/HYBRID_PROGRESS.md`, `bend/PORT.md` — the HVM2 negative result.
- agda branch: `telomare.agda`, `README-Agda.md`, `BENCHMARK.md` (45
  ITRS/tel, ~240 ns/tel).
- Conal Elliott papers in `~/src/conal-elliott/` (Denotational Design,
  Compiling to Categories, Timely Computation).
