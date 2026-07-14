# Revision history for telomare

## Unreleased (branch `bend-port`)

* New: `bend/` — a port of the telomare compiler to Bend (HVM2): lexer,
  parser, shared-let resolver, the full Possible.hs recursion-sizing
  abstract interpreter, and a native-Bend emission backend — compiled
  programs are emitted as defunctionalized Bend code executed directly by
  HVM. Fully type-annotated; verified against the Haskell compiler
  (see `bend/PORT.md` for the engineering log and `COMPARISON.md` for the
  three-way Haskell/Agda/Bend comparison).
* New flake app: `nix run .#telomare-bend -- <program.tel> < moves` —
  two-stage driver (compile under `bend run-rs`, cached by source hash;
  run under `hvm run-c`), shell/awk only.
* New: hybrid pipeline — the Haskell compiler front end (parse, resolve,
  Possible.hs recursion sizing) emits the sized program as a
  defunctionalized Bend/HVM2 program: `telomare --emit-hvm <file.tel>`
  (`src/Telomare/HvmBackend.hs`). Flake app
  `nix run .#telomare-hvm -- <program.tel> < moves`
  (`bend/run_telomare_hvm.sh`; runners: `gen-hvm`, `bend-run-c`,
  `gen-c-big`). Oracle-verified on e1/simpleplus/echo-`$127` (echo: 15s
  cold vs 734s self-hosted); tictactoe compiles+caches in 68s but its
  evaluation exceeds practical HVM2 interaction budgets — diagnosis in
  `bend/HYBRID_PROGRESS.md` and `bend/PORT.md`.
* Fix (hybrid driver, `gen-c-big` runner): patch `hvm gen-c`'s hardcoded
  `Def defs_buf[0x4000]` (16384-entry definition table) up to `0x20000`. Large
  programs like tictactoe emit ~32k HVM defs and overflow that fixed array,
  which SEGFAULTs the compiled binary in ~2 s (previously misdiagnosed as arena
  overflow). With the patch tictactoe no longer crashes. `TELOMARE_HVM_DEFS_BUF`
  and `TELOMARE_HVM_TPC_L2` override.
* Optimization (hybrid emitter): native `u24` nat leaves. `type TV` gains
  `N { v: u24 }` folding a clean unary-nat pair chain into one machine word,
  plus a native `iter_setenv` church-spine driver. HVM2 copies pair structure
  on every non-affine read but duplicates a u24 for free, so deep telomare
  numbers cost O(1) to copy instead of O(depth): measured 2.2-5.2x fewer
  interactions on `simpleplus`/`drawBoard`-shaped programs, all outputs
  oracle-verified. tictactoe now runs (no longer crashes) but one evalLoop
  iteration is ~10^9-10^10 interactions: the dominant cost is intrinsic
  Church-numeral recursion-scheme overhead (`whoWon` alone = 580M ITRS),
  which native leaves cannot touch. Reaching Haskell-competitive speed needs
  native compilation of arithmetic/`map`/`foldr` upstream of the emitter.
  See `bend/HYBRID_PROGRESS.md`.
* Optimization (hybrid emitter): `tvRepeat` native counted loop. All telomare
  recursion funnels through `repeatFunctionS`; the emitter now recognizes its
  inner-lambda body and emits `tvRepeat(k, f, x)` (with a generated `churchK`
  fid->count table) instead of a church-spine-driven frame rebuild. Pure church
  iteration (`$k`, the `$127`/`$9`/`$3` refinement towers) goes from O(k)*~0.5M
  to O(1) (~150K flat); static unary-nat literals now emit `TV/N(n)` directly.
  See `bend/HYBRID_PROGRESS.md`.
* Optimization (hybrid emitter): `tvFix` native tail-recursion for `{t,r,b}`.
  The emitter detects a sized recursion's step (rWrap, via `isRWrapDefer`) and
  emits the recursion result as a self-referential closure that unwinds via its
  base case in O(n) (`tvFixApply`), instead of the church count building an
  O(k)-size tower at O(k^2) cost. Makes `map`/`foldr`/`d2c` linear: `d2c` n=64
  12.3M->1.08M (~11x), `whoWon`+`drawBoard` 1167M->141M (**8.3x**), all
  parity-verified byte-exact. `tttFull` (most of a tictactoe move) is now
  ~163M ITRS (~6.5s). Full `tictactoe.tel` still exceeds budget due to a
  remaining dense multi-consumer compounding (shared computed bindings like
  `newBoard` recomputed per read); characterized in `bend/HYBRID_PROGRESS.md`.
* New: `design/` — Telomare 2 design (`TELOMARE2-DESIGN.md`): a greenfield
  denotational design of telomare as a total language with machine-checked
  time/memory bounds — affine categorical core, EAL `!`-boxes placed by
  whole-program inference, fuel-carrying recursion only, resource functors
  with adequacy (type-checked skeleton `design/telomare2.agda`, `--safe`, no
  postulates). Validated empirically (`design/VALIDATION.md`): on the
  `{t,r,b}` fragment, EAL box-nesting order = Possible.hs's sizing-dependency
  order (whoWon, dPow tower, minus; sizes readable from `--emit-hvm`'s
  churchK table).
* New: `telomare --emit-levels` (`src/Telomare/Levels.hs`) — structural EAL
  box-placement prototype: assigns every reachable `{test,step,base}` site a
  level (containment + parameter-offset summaries, no evaluation/search) and
  reports variables forced under `!` (max use-below-binding). Reproduces the
  VALIDATION.md hand decorations; full tictactoe in 37 ms, towerHeight 3,
  flags `main.newBoard : !` / `whoWon.board : !!` — the bindings behind the
  HVM2 duplication blowup.
* New: Telomare 2 backend — `telomare --emit-t2` (`src/Telomare/T2Backend.hs`)
  and flake app `nix run .#telomare2 -- <program.tel> < moves`. Emits the
  sized program under the T2 affine discipline (design §12): computed let
  bindings that are contracted (read >1×, counted scope-aware through let
  chains — the legacy gate saw 0 such sites on tttSP, this one 29) are
  forced ONCE at the binding to data normal form (`tvDF`, which stops at
  closure boundaries — forcing through a captured env is reduction across a
  box boundary and measurably grinds); iteration step closures likewise at
  loop entry. Emitted programs carry a static cost certificate (dupS/iterS
  sites, churchK budgets). Measured: tttSPmin OOM→3.97M; +1–2% overhead on
  tttD/tttLit/tttFull vs the lazy baseline (vs +26%/+57% for the tvNF
  forcing variants). `--emit-t2-lazy`/`--emit-t2-letonly` for A/B. See
  `design/T2-BEND-BACKEND.md`.
* Workstream-A closure: the pending "tttSP ≈95M with ungated forcing" theory
  was tested and REFUTED — no forcing regime (ungated tvNF, gated tvNF,
  gated tvDF) completes tttSP (600 s budget). Consumer bisection pins the
  blowup to {setPiece-computed board} × {whoWon's nested iteration capture}
  (= the `whoWon.board : !!` site of `--emit-levels`); drawBoard over the
  same board completes at 11.2M. HYBRID_PROGRESS.md's copy-on-dup-of-
  capturing-closures diagnosis stands; full tictactoe remains out of reach
  on level-less HVM2 (tttSP ⊂ tictactoe). Also: removing the `validBoard`
  refinement makes tttSP-class probes UNSIZABLE (`RecursionLimitError`) —
  the refinements are the totality certificate, not optional checks.
* New: `telomare --emit-hvm-ccc` (`src/Telomare/HvmBackendCcc.hs`) —
  experimental ConCat-style combinator backend (after the `agda` branch's
  ctc/HVM.hs); works on affine programs, documents HVM2's non-affine
  closure-duplication limit on church towers.
* New: **telomare3** (`telomare3/`, `design/TELOMARE3-DESIGN.md`) —
  greenfield reimplementation of telomare from first principles via
  denotational design, making the telomare2 finding definitional: recursion
  sizing ≡ EAL box-depth/budget inference. Agda-first spec
  (`telomare3/spec/`, `--safe`, zero postulates) mirrored by Haskell; new
  surface language planned; telomare1 and `bend/` on hold as oracle/archive.
  M0 landed: second cabal package (root `cabal.project`), flake app
  `nix run .#telomare3`, spec gate `checks.telomare3-spec`, agda+stdlib in
  the dev shell, `HANDOFF.md` restarted (predecessor archived to
  `design/HANDOFF-TELOMARE2-ARCHIVE.md`).
* telomare3 M1–M3 landed (all Agda `--safe`, zero postulates; details in
  `design/TELOMARE3-DESIGN.md` §7):
  - M1 `telomare3/spec/T3/*`: telomare2.agda ported + consolidated — ONE
    graded interpretation `⟦_⟧G` over a CostAlgebra (work/dup/space
    instances), generic value coherence `G-val`, adequacy restated once;
    new `whileS`/`guardS` primitives whose probes (reads that don't
    consume) are PRICED in the dup grade; §10 examples reprove by refl.
  - M2 Haskell mirror `Telomare3.{Core,Denotation}` (GADT + STy
    singletons only where grading reads types) with `cabal test
    telomare3`: 24 spec vectors 1:1 by name with Examples.agda + 6
    QuickCheck laws ×1000 re-checking the proved theorems.
  - M3 surface + placement: `T3/Surface/*`, `T3/Place.agda` — erasure ε,
    factorization `stripV ∘ ⟦_⟧V ≡ ⟦ε _⟧VS ∘ stripV`, meet-closure,
    `place-least` (the least-boxing universal property, telomare2 §16
    debt 2 discharged on the compiler-owned fragment), `core-dominates`
    (typed core terms stratify above the structural placement of their
    erasure).  `Telomare3.Infer` mirrors the spec + the Levels.hs recipe;
    `test/InferOracle.hs` reproduces telomare1's `--emit-levels` facts on
    a structural tictactoe reduction (towerHeight 3, `whoWon.board : !!`,
    `main.input : !!`, `main.newBoard : !`, strata {0,1,2}).
* telomare3 M-tel: the .tel compatibility runtime —
  `nix run .#telomare3 -- game.tel` runs .tel programs with full
  interactive IO on telomare3's own metered Tier-2 evaluator
  (`Telomare3.Tel.{Frontend,Eval,Loop}`).  Frontend reuses telomare1's
  Parser/Resolver as a library dependency; **no Possible.hs** — `{t,s,b}`
  recursion runs natively (a `VRec` ladder value unrolling one step per
  demanded call, metered per site), so compilation is near-instant and
  programs telomare1 rejects as unsizable (e.g. `sizing_fail5.tel`) run.
  Two-player tictactoe plays; four scripted games byte-identical to
  telomare1 golden transcripts; simpleplus/tc_ultra_minimal transcripts
  match.  CLI: `--certificate` (structural levels report), `--meter`
  (work report on stderr), `--max-steps` (fuel cap).  Parity suite in
  `telomare3/test/ParityTel.hs` over frozen program copies.  Details and
  the two documented semantic deviations (lazy gate selection,
  value-aborts) in `design/TELOMARE3-DESIGN.md` §7.
* telomare3 M4: the Possible-successor — budgets by calculated abstract
  interpretation (`spec/T3/Abstract.agda`, --safe, 0 postulates): Shape
  domain + γ, budget trees over the M3 skeletons, transfer with
  fuel-bounded abstract unrolling (VALIDATION S2 = the definition, S3 =
  composition), PROVED sound (per-combinator logical relation) and
  stable (`while-stable`); unbounded fuel = ⊤ budget = Tier-2 notice,
  never rejection.  `spec/T3/Examples/Budgets.agda` refl-computes the
  probe budgets; churchK oracle mapping k = bound + 2 (dPow (3,6)↦(5,8),
  whoWon strata (8,3)↦(10,5)).  Haskell mirror `Telomare3.Budget` +
  `test/BudgetOracle.hs` vectors 1:1.
* telomare3 M5 closed: the intrinsic `!`-denotation attempt
  (`spec/T3/Sem/Length.agda`) machine-checks its own arbiter firing —
  `iterS-not-additive`: additive length spaces admit no realizer for
  fuel-carrying iteration.  Design axiom recorded (elementary-growth
  resource monoid deferred; graded semantics remains the cost layer).

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
