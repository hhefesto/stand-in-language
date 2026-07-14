# HANDOFF — telomare3 (updated 2026-07-13; objective: .tel compatibility runtime)

Cross-machine/session state for **telomare3**: a greenfield reimplementation
of telomare via denotational design + EAL. **Current objective: every .tel
program that runs on telomare1 must run on telomare3** — full interactive IO
(the transcript loop) and a playable two-player tictactoe, in the spirit of
telomare1 (equivalent behavior; byte-identity not required). Predecessor-era
handoff archived at `design/HANDOFF-TELOMARE2-ARCHIVE.md`.

## What this is / how to resume

- Branch `bend-port`. M0 is committed ("telomare2 design + T2 backend
  verdict; telomare3 restart (M0)"); M1–M3 and later work are **staged but
  uncommitted**. Commits only when the user asks. Flake builds see only
  git-*tracked* files — `git add` every new file before any nix command.
- One-command health check: `nix flake check` (telomare1 + telomare3 builds,
  both test suites, Agda spec check `checks.telomare3-spec`).
- Roadmap + full progress log: `design/TELOMARE3-DESIGN.md` (§7 has the
  detailed M0–M3 records; this file keeps only the board).
- telomare1 (`src/`, `telomare.cabal`) and `bend/` are on hold: **zero
  edits**, but telomare1 is now allowed as a **library dependency** of
  telomare3 (frontend reuse — user decision).

## Firm decisions (user-stated, current)

- **Surface = the .tel language** (compatibility mode). The earlier "design
  a fresh .t3 syntax" decision is SUPERSEDED; any future surface work builds
  on .tel.
- **Frontend reused from telomare1** as a library dep (Parser/Resolver as a
  base; be critical — industry standards where telomare1 is idiosyncratic:
  Either-based errors, no partial functions, clean optparse CLI).
- **No Possible.hs.** telomare3's budgets come from the EAL side (M4).
  Running .tel now = telomare3's own **metered Tier-2 evaluator**: native
  `{test,step,base}` recursion (iterate until the base fires) + a work
  meter — "deoptimize, never reject". Parity rationale: telomare1's sizing
  only proves a bound suffices; at runtime the base fires early, so
  while-semantics ≡ sized-church semantics on everything telomare1 accepts.
  Unsizable programs additionally run here (improvement, documented).
- Acceptance: CLI program running (`telomare3 foo.tel < input` behaves like
  telomare1's, spirit-level). REPL/LSP/unit-test harness stay telomare1's.
- Agda-first discipline unchanged for the spec side (`telomare3/spec/`,
  `--safe`, zero postulates; Haskell mirrors it).

## Milestone board

| M | What | Status |
|---|------|--------|
| M0 | Scaffolding, flake wiring, charter, HANDOFF restart | DONE 2026-07-13 (committed) |
| M1 | Agda core spec ported + consolidated (one graded `⟦_⟧G`/CostAlgebra, adequacy once, whileS+guardS with priced probes) | DONE 2026-07-13 — see charter §7 |
| M2 | Haskell mirror + 24 spec vectors + 6 QuickCheck laws ×1000 | DONE 2026-07-13 — see charter §7 |
| M3 | Surface category + placement: ε-factor, meet-closure, `place-least`, `core-dominates`; `Telomare3.Infer` + levels oracle vs telomare1 `--emit-levels` | DONE 2026-07-13 — see charter §7 |
| **M-tel** | **.tel compat runtime**: `Telomare3.Tel.{Frontend,Eval,Loop}` + CLI — telomare1 frontend (dep) → Term3 → telomare3 IR with native recursion; metered Tier-2 evaluator; transcript IO loop | **DONE 2026-07-14** — tictactoe plays via `nix run .#telomare3 -- tictactoe.tel`; 4 scripted games BYTE-identical to telomare1 goldens; simpleplus/tc_ultra_minimal match; sizing_fail5 runs (telomare1 rejects it); details charter §7 |
| M4 | Possible-successor budgets: `spec/T3/Abstract.agda` (Shape/γ, transfer = fuel-bounded abstract unrolling, SOUND + while-stable proved) + `Telomare3.Budget` mirror | **DONE 2026-07-14** — S1/S2/S3 by refl; churchK oracle = bound+2 (dPow (3,6)↦(5,8); whoWon (8,3)↦(10,5)); ⊤ budget = Tier-2 notice; charter §7 |
| M5 | `!` denotation attempt | **CLOSED 2026-07-14** — arbiter FIRED: `spec/T3/Sem/Length.agda` machine-checks that additive length spaces admit NO realizer for iterS (`iterS-not-additive`); design axiom recorded (elementary-growth monoid deferred, Dal Lago–Hofmann cited); charter §7 |

## Design lessons still steering M4/M5 (pointers)

- Sizing ≡ EAL box-depth inference (design/VALIDATION.md); levels by
  structure (proved least in `T3/Place.agda`), budgets by evaluation (M4).
- `boxVal` promotion is empty-context only (dup∘boxVal smuggles contraction).
- Probes (guard/while tests) are implicit copies and are PRICED in the dup
  grade (T3.Sem.Graded chargeProbe).
- HVM2 lacks level-annotated fans ⇒ Tier 1 needs labeled fans; Tier 2
  metered reduction is mandatory (design/T2-BEND-BACKEND.md).
- Cost anchors: ~45 ITRS/tel, ~240 ns/tel (agda branch BENCHMARK.md).

## How to verify everything

```sh
nix flake check                                   # everything at once
nix run .#telomare3 -- tictactoe.tel              # interactive game (M-tel)
nix develop --command cabal test telomare3        # vectors + laws + oracle + parity
nix develop --command agda --safe telomare3/spec/Everything.agda
nix run .#format-lint
```

## Standing constraints (user-stated)

- No python — shell/awk only. No commits unless explicitly asked; stage new
  files before nix builds. Document progress in the repo's md files; keep
  THIS file current. Timeout-wrap + cap output on any bend/hvm run (not
  expected this round); kill leftovers via /proc/PID/exe, never `pkill -f`.

## Archive & evidence pointers

`design/TELOMARE3-DESIGN.md` (charter + progress log) ·
`design/HANDOFF-TELOMARE2-ARCHIVE.md` (telomare1/2-era handoff, toolchain
hazards) · `design/TELOMARE2-DESIGN.md` / `VALIDATION.md` /
`T2-BEND-BACKEND.md` / `telomare2.agda` (frozen) · agda branch
`BENCHMARK.md`.
