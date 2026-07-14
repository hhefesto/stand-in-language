# ARCHIVED 2026-07-13 — telomare1/telomare2-era handoff
#
# Archived verbatim at the start of the telomare3 effort; superseded by the
# restarted HANDOFF.md at the repository root. Nothing below is maintained.

# HANDOFF — telomare session state (2026-07-13, updated after T2 backend + workstream-A closure)

Purpose: continue this work from **another account/machine with no access to
the original conversation**. Everything needed is in this file plus the files
it points to. **All of it is uncommitted on branch `bend-port`** (HEAD =
`e0a2482 "add bend hvm backend"`) — commit or copy the working tree to carry
the state (the owner has not asked for any commits; do not commit without
being asked).

Uncommitted state worth carrying:

```
MM CHANGELOG.md              — hybrid/tvRepeat/tvFix entries (workstream A log)
M  COMPARISON.md, bend/PORT.md, bend/run_parity_tests.sh, flake.nix
AM bend/HYBRID_PROGRESS.md   — workstream A engineering log (READ THIS)
MM bend/run_telomare_hvm.sh  — hybrid driver (gen-c-big runner, defs_buf patch)
 M src/Telomare/HvmBackend.hs — the emitter: tvRepeat, tvFix, N-leaves, forcing
?? design/                   — workstream B deliverables (NEW, this session)
?? ttt_whowon.tel
```

There are TWO independent workstreams. B is the most recent and was completed
this session; A is paused mid-experiment with a precise resume point.

---

## Workstream B (current): "Telomare 2" language design — DELIVERED

**Request:** design telomare as a total language that guarantees time and
memory bounds using limited recursion, via Conal Elliott's Denotational
Design, with Elementary Affine Logic. User decisions: pure greenfield;
deliverable = design doc + Agda skeleton; **whole-program inference** (no
depth ever in a signature).

**Deliverables (done, verified):**

- `design/TELOMARE2-DESIGN.md` — the design document. Every claim labeled
  [proved]/[measured]/[cited].
- `design/telomare2.agda` — type-checked skeleton (`--safe`, zero postulates):
  affine bicartesian-distributive category with EAL exponential
  (`dupS`/`boxS`/`boxValS`/`mergeS`; **deliberately NO dereliction/digging**),
  fuel-carrying `iterS`/`foldS`, five interpretations (value, work ⟦_⟧C, dup
  grade ⟦_⟧D, space ⟦_⟧SP, execution ⟦_⟧K), **adequacy theorem proved**
  (precision-with-slack, technique copied from `agda` branch telomare.agda
  §8e), worked examples all checking by `refl`.
- Verify with:
  `cd design && nix develop 'git+file:///home/hhefesto/src/telomare?ref=agda' --command agda telomare2.agda`
  (any Agda ≥ 2.6 + standard-library works; exit 0 = green).

**Design core (one paragraph):** three layers — plain surface (no modalities);
trusted core category (affine = no implicit copying; EAL `!`-boxes placed by
whole-program ILP-style inference; recursion only as fuel-carrying iteration
whose output lands one box-level deeper); tiered backends (Tier 1 =
level-annotated interaction nets, oracle-free Lévy-optimal because fan pairing
is a static level comparison; Tier 2 = metered graph reduction for
total-but-unstratifiable programs, with LOUD tier reporting). Resources are
graded interpretations (functors) with per-functor adequacy; the new **dup
grade** prices exactly the duplication that killed workstream A's full
tictactoe. Central thesis: **recursion-limit inference (Possible.hs) and EAL
box-depth inference are the same analysis** — the level structure is both the
termination certificate and the optimal-sharing certificate.

**Key inputs that shaped it** (from a claude.ai conversation the user pasted;
its conclusions are folded into the design doc, esp. §2, §6–8, §10): trusted
core ≠ runtime; EAL not LAL; no dereliction/digging = stratification = both
theorems; errors must speak "iteration levels", never boxes/linearity;
`λn. n n` is the canonical untypable; tiered fallback instead of rejection;
Coppola–Martini constraint recipe for box placement; tree calculus rejected as
foundation. A subtlety discovered while formalizing: `boxVal : A ⇨ !A` for
general A is UNSOUND (dup∘boxVal smuggles contraction on an open input) —
empty-context promotion must be `(unit ⇨ B) → (unit ⇨ !B)`; the skeleton and
doc reflect this.

**§13 validation exercise: DONE (2026-07-12) — bet CONFIRMED.** See
`design/VALIDATION.md`. Method: inferred limits read from `--emit-hvm`'s
`churchK` table (no compiler changes; probes = `import Prelude` + 1-line
main; all size in <1 s stage-1). Findings: on the `{t,r,b}` fragment (= all
telomare recursion) box-nesting order = sizing's evaluation-dependency order
everywhere tested; sizes are exact bound+2; dPow's inner token = max over
outer iterations (Girard's level argument, operationally); whoWon k-groups
{10}{5}{3} partition by hand-derived strata, `board : !!`; `pow` on church
literals has NO tokens (sizing-invisible) while EAL still levels it — scope
divergence handled by tiering. Gotchas: `c2d` applied to a DATA nat crashes
sizing with `sizeTermM unhandled case` (surface type error, not a sizing
bug); root `ttt_whowon.tel` has exactly that bug in its main (`concat [c2d
w]` — whoWon returns data; corrected probe uses `[w]`).

**Box-placement pass: PROTOTYPED (2026-07-13).** `telomare --emit-levels
<file.tel>` — new `src/Telomare/Levels.hs` (+ flag in `app/Main.hs`, module
in `telomare.cabal`; all uncommitted). Structural only (containment +
parameter-offset summaries composed at call sites; no evaluation, no
search). Reproduces every VALIDATION.md hand decoration: dPow = one textual
d2c site at levels 0/1/2 with `dPow.a : !!!`; whoWon strata + `whoWon.board
: !!`; pow = no sites. Full tictactoe: **37 ms**, towerHeight 3, statically
flags `main.newBoard : !` (THE bend-port blowup binding). Known
approximations (in module header + VALIDATION.md §8): church-literal
iteration invisible (minus's producer → level 0 vs hand's 1), unknown
higher-order heads contribute offset 0, one witness path per (site, level).
`--emit-hvm` smoke-tested unchanged (dPow churchK still 5 6 8).

Also added: design doc §16 — a denotational (Elliott-style) critique of the
EAL box, recording four design debts: `!` lacks its own denotation
(coherence-space/cofree-comonoid home wanted); box placement needs a
universal property (least-boxing Galois connection), not just an algorithm;
grades are machine-anchored (45 ITRS/tel empirical — want machine-free cost
algebra with backends as homomorphic images); the discipline is intensional
while the semantics is not (hence Tier 2 = semantic-fidelity requirement).

**T2 backend on Bend/HVM2: BUILT + MEASURED (2026-07-13).**
`telomare --emit-t2` (`src/Telomare/T2Backend.hs`, git-staged) +
**`nix run .#telomare2 -- prog.tel < moves`** (flake app; driver reused via
`TELOMARE_EMIT_FLAG`, which is already in the driver's cache key). The §12
migration table operational: dupS = scope-aware-gated force of contracted
computed lets; boxS = step-closure force at iteration entry; force operator
= `tvDF` (data NF, STOPS at closure heads — tvNF-through-closures is
reduction across a box boundary and grinds). Static cost certificate in
every emitted header. Results (`design/T2-BEND-BACKEND.md`): tttSPmin
OOM→3.97M; tttD/tttLit/tttFull +1–2% (T2Lazy reproduces baseline
byte-exact, 141,075,149 on tttD); parity oracle-exact (p_dpow, tttD, incl.
via the flake app). tttSP still times out under EVERY regime → bisected to
{computed board}×{whoWon's 2-deep iteration capture} = the `whoWon.board :
!!` levels-pass site; single-level forcing cannot realize a depth-2 box —
the empirical case for Tier 1 proper (level-annotated fans). Removing
`validBoard` makes tttSP-class probes UNSIZABLE — refinements are the
totality certificate.

**Sensible next steps (not started):** drive the T2 emitter's force
placement directly from the levels pass (emit `!^k` boxes at the depths
`--emit-levels` prints — a depth-2 materialization inside the row-fold
frame is the candidate fix for tttSP/tictactoe on HVM2); or target labeled
fans (levels as dup labels) — Tier 1 proper. Design side: §14 open
questions; church-literal producers in the levels pass; least-boxing
universal property (§16 debt 2).

**Evidence sources to read first on a fresh machine:**
`git show agda:telomare.agda`, `git show agda:README-Agda.md`,
`git show agda:BENCHMARK.md` (45 ITRS/tel, ~240 ns/tel numbers),
`bend/HYBRID_PROGRESS.md` (duplication-is-the-cost evidence),
Conal Elliott papers (user keeps copies in `~/src/conal-elliott/`),
Taelin's Elementary-Affine-Core repo (`agda/Linear.agda`).

---

## Workstream A (CLOSED 2026-07-13, negative result): tictactoe on HVM2 within 10×

**Goal (user's `/goal`, unmet and now characterized as blocked on the
runtime):** full `tictactoe.tel` on the hybrid backend within 10× of
Haskell (budget ≈ 620 s stage-2). **Resolution:** the exact resume-point
test below WAS run (plus stronger variants from the T2 backend): tttSP
does not complete under ANY forcing regime; the blowup is duplication of
the closures capturing a computed board inside whoWon's nested recursions
(`whoWon.board : !!`), which single-level forcing cannot fix on a
level-less runtime. See the 2026-07-13 addendum in `bend/HYBRID_PROGRESS.md`
and `design/T2-BEND-BACKEND.md`. The paragraphs below are kept as the
historical record of the interrupted state.

**Where it stands (read `bend/HYBRID_PROGRESS.md` + CHANGELOG for the full
story):** crash fixed (hvm gen-c's `Def defs_buf[0x4000]` overflow → patched
to 0x20000 in `bend/run_telomare_hvm.sh`); native u24 leaves (2–5×); tvRepeat
(church `$k` → O(1)); tvFix (sized recursion as self-unwinding closure —
whoWon+drawBoard 1167M→141M ITRS, 8.3×, parity byte-exact); `tttFull` (most of
one move) = 163M ≈ 6.5 s — inside budget. Full tictactoe still blows up.

**The then-current theory (REFUTED 2026-07-13 — the "copy-on-dup of
capturing closures is fundamental" diagnosis in HYBRID_PROGRESS.md is what
stands):** "the blocker is recompute-on-dup of setPiece per read — which IS
forceable". Basis: `tttLit` = 93M completes; `tttSP` OOMs; `tttSPmin`
(setPiece read 3× directly, forcing ON) = 4.7M completes. What the theory
missed: tttSPmin's reads are DIRECT; tttSP's go through whoWon's two-deep
iteration captures.

**Exact resume point (EXECUTED 2026-07-13 — result: RUN_FAIL/timeout 600 s;
kept for the record):** forcing was re-enabled UNGATED in
`src/Telomare/HvmBackend.hs` (`worthForcing` returns True for
SetEnvB-containing values; appB force site has NO `closureArgReads ≥ 2` gate)
and the compiler was rebuilt. The interrupted decisive test:

```
TELOMARE_BIN=dist-newstyle/build/x86_64-linux/ghc-9.6.7/telomare-0.1.0.0/x/telomare/build/telomare/telomare
run tttSP.tel through the driver, gen-c-big runner, timeout ~150 s
```

(The tttD/tttFull/tttSP/tttLit/tttSPmin probes + measure.sh lived in the
session scratchpad `/tmp/claude-1000/...` — likely GONE on a new machine;
they're easy to reconstruct: tttD = whoWon+drawBoard on a literal board;
tttSP = same with `setPiece`-built board; tttFull adds fullBoard+$127; all
carved out of `tictactoe.tel`.) Expected if the theory holds: tttSP ≈ 95M and
completes. Then: emit + run FULL tictactoe, check ≤620 s + byte parity vs
`telomare tictactoe.tel`; re-run parity suite (simpleplus valid/multi-turn,
tttD, tttFull — `bend/run_parity_tests.sh`); decide the forcing gate (ungated
regressed tttD 141M→178M; the read-count gate avoided that but may miss
setPiece's binding); then correct the outdated "copy-on-dup fundamental"
paragraphs in `bend/HYBRID_PROGRESS.md` and CHANGELOG.

**Hard-won toolchain facts:** driver = `bend/run_telomare_hvm.sh`, use
`TELOMARE_HVM_RUNNER=gen-c-big` (patches arena to 1<<30 and defs_buf;
`TELOMARE_HVM_DEFS_BUF`/`TELOMARE_HVM_TPC_L2` override). `hvm run-c` on OOM
loops printing "OOM" forever — ALWAYS cap output. bend 0.2.37 / hvm 2.0.22
from nixpkgs rev `22b5577`. **GC-pinned (2026-07-13, after nix swept them
once):** (1) they are now in the flake devShell (`mkShellArgs` in
flake.nix), so nix-direnv's `use flake .` gcroot covers them after the next
`direnv reload`; (2) explicit roots exist at `.nix-gc-roots/{bend,hvm}`
(gitignored) — recreate on a fresh machine with
`nix build 'github:nixos/nixpkgs/22b5577ab32f946edde57fb119c503e13634f2b4#bend' --out-link .nix-gc-roots/bend`
(same for `#hvm`). ITRS is printed by the runtime; interactions ≈ wall time
× ~25M/s single-thread.

---

## Standing constraints (user-stated, apply to everything)

- **No python** — shell/awk only for tooling.
- **Timeout-wrap every bend/hvm invocation**; cap/head all output.
- **One big-arena binary at a time**; watch memory (a previous run
  destabilized the machine); kill leftover bend/hvm processes after runs.
- **No commits unless explicitly asked.**
- Document progress in the repo's md files (HYBRID_PROGRESS.md, CHANGELOG,
  PORT.md, this file).
