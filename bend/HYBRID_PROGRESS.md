# Hybrid HVM Progress

This file records the current direct Haskell-to-Bend/HVM hybrid status. It is
intended as a short handoff note separate from the longer engineering log in
`bend/PORT.md`.

## Checkpoint Commit

- Created commit `e0a2482 add bend hvm backend` before continuing further work.
- That commit includes the Bend-hosted compiler files, the direct HVM backend,
  the experimental CCC backend as existing code only, CLI flags, flake apps, and
  the first hybrid driver.

## Direct Hybrid Path

- Primary path remains `telomare --emit-hvm` plus `bend/run_telomare_hvm.sh`.
- `src/Telomare/HvmBackend.hs` validates the post-sizing expression before
  emitting Bend/HVM code.
- Bare `Gate` is rejected unless it appears in the expected compiler shape:
  `SetEnv(Pair(Gate left right, scrutinee))`.
- The generated driver now stops immediately when there are no remaining input
  lines instead of carrying a newly computed Telomare state into another loop
  call.

## Driver Hardening

- `bend/run_telomare_hvm.sh` cache keys now include a hash of the compiler
  binary content when available, not just the compiler path.
- Stage-2 stdout is capped by `TELOMARE_HVM_MAX_OUTPUT_BYTES` to avoid runaway
  HVM readback filling disk or memory.
- The default cap was raised to `268435456` bytes after `tictactoe.tel` exceeded
  the initial 10 MiB guard.
- Stage-2 failure reporting now distinguishes HVM command failures from output
  processing failures and reports the relevant exit status.
- Added `TELOMARE_HVM_RUNNER` with values:
  - `gen-hvm`: default raw `bend gen-hvm` then `hvm run-c` path.
  - `bend-run-c`: direct `bend run-c` path for comparison.

## Nix Wiring

- The `telomare-hvm` flake app works as the reliable way to provide Bend/HVM2
  tools in this environment.
- The normal shell does not have `bend` or `hvm` in `PATH`.
- The `agda` branch wiring confirmed that `pkgs.bend` plus `pkgs.gcc` is the
  standard Bend/HVM2 app setup here.
- Added `pkgs.gcc` to `apps.telomare-hvm.runtimeInputs` to match that pattern.

## Verified So Far

- `cabal build exe:telomare` succeeds after fixing the Haskell layout error in
  `emitProgram`.
- `bend/run_telomare_hvm.sh` passes `bash -n`.
- `simpleplus.tel` matches the normal interpreter through the hybrid flake app:
  input `2 3` prints:

```text
enter two digits separated by a space
2 plus 3 is 5
```

## Current Tictactoe Status

- `tictactoe.tel` baseline p1 script produces the expected transcript ending in
  `Player 2 wins!`.
- Direct hybrid `tictactoe.tel` no-input and p1 runs are not yet passing.
- Before the driver state-stop change, `tictactoe.tel` exceeded the stage-2
  stdout cap even at 256 MiB, indicating a huge HVM result/readback term.
- After the state-stop change, the no-input run no longer hits the stdout cap in
  the observed run, but it timed out at the configured 300 second stage-2 budget
  with status `124`.
- Both raw `gen-hvm`/`hvm run-c` and `bend run-c` showed the same output-cap
  behavior before the state-stop change, so the issue is likely in generated
  program evaluation/readback shape rather than only in the runner wrapper.

## Explicit Stop Point

- Do not spend time on the CCC backend in this pass.
- Continue direct hybrid diagnostics only until `tictactoe.tel` is understood or
  fixed.

## Diagnosis Corrections (2026-07-03, follow-up session)

Two earlier conclusions above did not survive instrumentation (raw stage-2
stdout captured to a file instead of inferring from the byte cap):

- The >256 MiB stage-2 flood is **not** a huge result/readback term. It is
  the HVM C runtime's **OOM loop**: the captured output is literally
  `OOM\n` repeated forever (500k lines in the first 2 MB). `hvm run-c`
  exhausts its node arena and loops printing `OOM` instead of exiting —
  the same pathology already documented in `bend/PORT.md`.
- The driver "state-stop" change is semantically a no-op (the old emitted
  driver already returned the accumulator when inputs ran out:
  `loop_go(ns, 0, [], acc)` reduces to `acc` without calling `one_iter`).
  The post-change run "no longer hitting the cap" was the 300 s timeout
  killing the run before the OOM loop started, not a fix. The change was
  kept anyway (harmless, marginally less work).

Established facts:

- `tictactoe.tel`'s FIRST evalLoop iteration overflows the C runtime's
  per-thread node slice (`G_NODE_LEN/TPC`). The allocator (see
  `node_alloc_1` in `hvm gen-c` output) reuses freed slots — OOM means
  the LIVE net truly exceeded the slice.
- A compiled `hvm gen-c` + gcc binary with the default 536M-node arena
  and `-DTPC_L2=2` (4 threads → 134M nodes/thread) also OOMs.
- `hvm run` (lazy Rust runtime, growable memory) refuses the emitted
  program: "attempt to clone a non-affine global reference" — only the C
  runtime executes the defunctionalized encoding.
- The emitted driver now computes `tel_main()` ONCE and threads the value
  through the loop (HVM2 re-unfolds nullary global refs per reference;
  sharing is sound because TV is pure data). e1 and echo-`$127` still
  match the oracle after this change.
- In flight: single-threaded (`TPC_L2=0`) binary with the arena raised to
  1B nodes (whole arena = one slice, ~13 GB), and a `$63` tictactoe
  scale-bisect through the plain interpreter.

## Final Diagnosis (2026-07-03): tictactoe is understood

All experiments completed. `tictactoe.tel` stage 2 is not fixable by
budget, arena size, thread count, runtime choice, or recursion bound:

| experiment | result |
|---|---|
| `hvm run-c` interpreter (33M-node/thread slices) | OOM loop at ~15 s |
| gen-c + gcc, 4 threads, 536M arena (134M slice) | OOM loop |
| gen-c + gcc, 1 thread, **1B-node arena (~13 GB)** | **no OOM — but no result in 30 min** |
| same, `$63` variant | no OOM, no result in 40 min |
| `hvm run` (lazy Rust, growable memory) | refuses: cloning refs to non-affine defs is unsupported, and every emitted `d<slot>` is non-affine (env used many times) |
| GHC evaluating the same sized `CompiledExpr` | < 1 s |

Root cause — a cost-model gap, not a bug: GHC's graph reduction reads a
shared structure by reference for free; interaction nets must route every
shared read through dup nodes that physically COPY structure as it is
demanded. Tictactoe's per-turn logic re-reads the game state through
hundreds of gate checks wrapped in `$127` (or `$63`) abort-checked
towers, so the net materializes copies of copies — an interaction gap of
roughly 10^4–10^5 versus GHC for a single evalLoop iteration. echo-`$127`
passes because its state is a single input line; the board is what makes
tictactoe blow up. The old tree-walking interpreter port hit the same
wall (536M-node OOM at `$63`), so this is intrinsic to evaluating this
program shape on HVM2, not to any particular backend encoding.

What the hybrid pipeline DOES deliver (all oracle-verified):
`e1` 0.15 s end-to-end; `simpleplus` parity; echo-`$127` parity ~15 s
cold / ~1.6 s warm — the case that took the self-hosted Bend compiler
734 s. Stage-1 compile+size of tictactoe: 68 s, cached (the self-hosted
port never finished it in 4+ h).

Hardening shipped with the diagnosis: the emitted driver now computes
`tel_main()` once and threads the value through the loop (HVM2 re-unfolds
nullary refs per reference), forcing/rebuilding it in `main` so the dup
lands on data; and `TELOMARE_HVM_RUNNER=gen-c-big` (gen-c + gcc,
single-thread, 1<<30 arena, binary cached by program+inputs hash) avoids
the interpreter's OOM print-loop entirely and is the recommended runner
for large programs.

If tictactoe-on-HVM2 is ever revisited, the leverage is in emission
strategy, not runtimes: keep the game state out of the copied path (e.g.
index-passing instead of structure-passing through gates), or await an
HVM with by-reference shared reads.

## Emission optimization (2026-07-03, follow-up): native u24 nat leaves

Acting on the "emission strategy" leverage above, two changes landed in
`src/Telomare/HvmBackend.hs` (measured, not speculative):

- **Native-number leaves (the win).** `type TV` gains `N { v: u24 }`: a clean
  unary nat chain `P(P(..Z..),Z)` of depth v is folded into one u24. A runtime
  smart constructor `mkP` collapses `P(Z,Z)->N 1` and `P(N k,Z)->N(k+1)`; every
  `PairB` emits `mkP`; `ceBasic` emits `TV/N(n)` for statically-clean chains.
  Every `match`/`switch` over a `TV` (tvL/tvR/tvTrunc/tvAbort/tvApp/tvCall, the
  generated gate defs, and the driver decoders) carries an `N` arm behaving
  EXACTLY as the equivalent pair chain (invariant: v>=1; zero is always `Z`).
  The point: HVM2 physically copies pair structure on every non-affine read,
  but duplicates a u24 for free — so deep telomare numbers (chars, arithmetic
  intermediates, coordinates) that used to cost O(depth) per copy now cost O(1).
- **Native iteration driver (`iter_setenv`, code-size only).** A pure church
  spine `SetEnv^k Env` (`setEnvSpineDepth`) is emitted as `iter_setenv(k, env)`
  instead of k nested `tvApp`. This does NOT reduce interactions (measured
  flat) — it shrinks the emitted program (relevant to tictactoe's stage-2
  compile). Kept for that reason; not a runtime lever.

Measured interaction counts (`hvm run-c`, ITRS; Part-1 off vs on, both with
`iter_setenv` on; all outputs byte-for-byte oracle-verified):

| program | before | after | speedup |
|---|---|---|---|
| `simpleplus.tel` "2 3" | 166,806,939 | 35,377,127 | 4.7x |
| `repro.tel` (church-tower `drop` reads) | 10,812,066 | 4,892,678 | 2.2x |
| `repro_board.tel` (tictactoe `drawBoard` path) | 145,621,681 | 27,834,731 | 5.2x |

(`repro.tel`/`repro_board.tel` are minimal measurement programs at repo root;
`repro_board.tel` is verbatim tictactoe `drawBoard` over a filled board.)

NOTE: this optimization lives only in the hybrid emitter `HvmBackend.hs`; the
self-hosted `bend/emitter.bend` twin was NOT updated and no longer emits
identical text.

## The tictactoe crash, root-caused and FIXED (2026-07-06)

The earlier "`hvm run-c` segfaults in ~2 s" was **misdiagnosed as arena
overflow**. The real cause: `hvm gen-c` hardcodes the Book's definition table
to `Def defs_buf[0x4000]` (16384 entries). Full tictactoe emits **32457** HVM
defs (bend expands each of the ~580 emitted `def`s into ~56 book entries),
which overflows that fixed array — a genuine out-of-bounds crash (SIGSEGV in
~2 s, independent of arena size, thread count, or stack limit). Confirmed by
bisection: variants with < 16384 defs (`drawBoard`+`whoWon`, 2791-4790 defs)
run fine; the full program (32457) crashes.

**Fix (`bend/run_telomare_hvm.sh`, `gen-c-big` runner):** `sed` the generated
C to `Def defs_buf[0x20000]` (131072), alongside the existing `G_NODE_LEN`
patch. `TELOMARE_HVM_DEFS_BUF` / `TELOMARE_HVM_TPC_L2` override. With this,
tictactoe no longer crashes — it runs.

## Why it still isn't within 10x of Haskell (the honest wall)

With the crash fixed and native numbers on, tictactoe *runs* but one evalLoop
iteration is ~10^9-10^10 interactions and does not complete in 600 s even at
`gcc -O2`, single-thread, 1<<30-node arena. Component costs (each completes in
isolation on `hvm run-c`, native numbers on):

| isolated piece (tictactoe's own code) | ITRS |
|---|---|
| `drawBoard` on the board | 76 M |
| + `whoWon` (8 rows, map/foldr) | **580 M** |
| + `fullBoard` | +57 M |

`whoWon` alone is 580 M for checking eight 3-cell rows. This is **intrinsic
recursion-scheme cost**, not a copy/arena artifact: telomare compiles every
arithmetic op (`d2c`, `dEqual`, `plus`) and every `map`/`foldr` to
Church-numeral manipulation over sized `SetEnv` towers, and each basic op costs
~1-5 M HVM2 interactions. Haskell's tree-walker does the same in microseconds.
Native `u24` leaves shave 2-5x off the *values*; they cannot touch the
*operations*, which are already church towers by the time the emitter sees the
defunctionalized IR.

Two forcing experiments (deep `tvNF` normal-form forcing of let-bound values,
to defeat HVM2's recompute-on-duplication) were **measured and rejected**:
first-order data (the board) is already shared cheaply through env projections
(a `map succ` board read 1/4/8 times grew only ~1.2 M/read, not the ~15 M/read
of true recompute); the values that *do* recompute are Church-numeral
*closures*, which `tvNF` cannot force (you cannot reduce a function without
applying it). Forcing added overhead with no offsetting win (whoWon: 733 M
forced vs 580 M unforced). Removed.

Reaching 10x would require compiling telomare's arithmetic and `map`/`foldr`
to **native Bend recursion over native numbers/lists** instead of church
towers — i.e. recognizing those Prelude combinators upstream of
defunctionalization (in Possible.hs / Term3), not in the emitter. That is a
compiler-level change, out of scope for the emitter.

HVM2 fact worth keeping: **HVM2 does not share reductions across duplication.**
A value that is passed as a function argument through recursion and dup'd while
still an unreduced redex is recomputed once per copy (clean test:
`readN(k, expensive())` is exactly linear in k). Let-bound data projected from
an environment is the shareable case; church-closure results are the
recomputed case.

### Per-operation profile (2026-07-06): the cost is uniform, not localized

Minimal sizeable programs, native numbers on, `hvm run-c` ITRS:

| operation | ITRS | notes |
|---|---|---|
| empty skeleton | 18 K | fixed overhead |
| `drop $2 [..5]` | 179 K | church-driven right-walk |
| `map succ [1,2,3]` | 1.41 M | |
| `map succ [1..6]` | 2.87 M | |
| `map succ [1..9]` | 4.87 M | **~0.5 M interactions PER element** |

`map`ping a *trivial* `succ` over a list costs ~500 K HVM2 interactions per
element (GHC: ~10 ops → ~50,000x). This is the sized-recursion machinery
(`map`/`foldr` as fixed-point church recursion + defunctionalized dispatch +
env rebuild + recompute-on-dup), and it is uniform across every recursion-
scheme op — there is no single hot function to patch. `whoWon` (8 rows x 3
maps x 3 cells, each cell doing `d2c`+`drop`+`dEqual`) = 580 M follows directly.

**Bottom line for a ~10x target:** the only lever large enough is to stop
compiling telomare arithmetic and `map`/`foldr` to church/sized-recursion
towers and instead emit **native Bend recursion over native numbers/lists**.
That recognition must happen upstream of defunctionalization (in Resolver /
Term3 / Possible, where `map`/`foldr`/`plus`/`d2c` are still identifiable as
named Prelude functions), not in `HvmBackend.hs` (which only sees the
flattened `SetEnv`/`Defer`/`Gate` IR). This is a compiler-level change to the
sizing pipeline, deferred pending a scoping decision.

### `tvRepeat`: native counted loop for the ONE recursion primitive (2026-07-06)

All telomare recursion funnels through `repeatFunctionS` (Telomare.hs:758): a
church numeral `SetEnv^k Env` drives k rebuilds of a frame that re-projects the
whole environment per step. `HvmBackend.hs` now recognizes that primitive's
inner-lambda body (`isRepeatBody`) and, using a generated fid->k table
(`churchK`, from `matchChurchCode`), emits a native `tvRepeat(k, f, x)` counted
loop instead of the church-spine-driven frame. `matchChurchCode` recovers k at
emit time from the church code body `L.R.R.R(SetEnv^k Env)`; the fallback is
the exact original frame emission. Also: static unary-nat literals (church
constants, e.g. a 122-deep gate arm) now emit `TV/N(n)` directly in `ce`
(`compiledNatDepth`) instead of n nested `mkP`. All parity-verified byte-exact
(simpleplus valid/multi-turn, tttD whoWon+drawBoard).

Measured (ITRS; baseline = native numbers, before tvRepeat):

| program | before | after | speedup |
|---|---|---|---|
| `$k succ 0` pure church, k=3..90 | ~0.5M * k | ~150-190 K FLAT | O(k) -> **O(1)** |
| `simpleplus` "2 3" | 35.1 M | 29.7 M | 1.18x |
| `tttD` (whoWon+drawBoard) | 1167 M | 723 M | **1.6x** |

Pure church iteration (`$k`, the `$127`/`$9`/`$3` refinement towers) is now
essentially constant in k — a large structural win. But `map`/`foldr` (the
`{t,r,b}` recursion) only improved ~1.6x, because there the count is NOT the
only cost: **the recursion re-invokes the repeater per element**, so `map succ`
is super-linear, measured **~O(n^1.45)** (n=3/6/12/18: 1.08M/2.23M/5.78M/
10.92M). tvRepeat makes each re-invocation cheaper but there are O(n) of them.
Full tictactoe still does not complete one iteration in 400s.

**Next lever (identified, not yet built):** emit the whole `{t,r,b}` recursion
(`unsizedRecursionWrapper`) as a single native tail-recursive Bend function
doing ONE O(n) pass, so `recur` is a direct call instead of re-driving the
church count (O(n^1.45) -> O(n)). Ruled out as the cost: church count (fixed by
tvRepeat), fenv size (+14% for 4 big added bindings), `tvDispatch` (O(1), 21
interactions regardless of def count), the abort/`RecursionTest` machinery
(bypassing `tvAbort` changed nothing), and deep static-nat chains (fixed,
neutral).

### `tvFix`: native tail-recursion for `{t,r,b}` — the big win (2026-07-06)

Built the lever above. `HvmBackend.hs` now detects the recursion step (rWrap,
`isRWrapDefer` — a curried lambda that unwraps to the `if t i then step recur i
else b i` GateSwitch; sizing restructures the exact tree so it is matched
robustly by shape, not by the builder's literal form) and, when it is the
repeated function of a sized recursion, emits the recursion result as a
fixed-size self-referential closure `P(F(fixSlot), rwrap)`. Applying it
(`tvFixApply`) reconstructs the SAME closure as `recur` and runs one rWrap step,
so the recursion unwinds via its own base case in **O(n)** with O(1) per step —
instead of the church count building an O(k)-size tower at O(k^2) cost. `$k`
(i2CB) still uses `tvRepeat` (`isRWrap` returns 0 for `left`/`succ`/steppers, so
they are not misrouted). Safe because sizing proved the base fires within k.

Measured (ITRS; baseline = native numbers, no tvRepeat/tvFix; all
parity-verified byte-exact vs the GHC oracle):

| program | baseline | tvRepeat | **tvFix** | total |
|---|---|---|---|---|
| `d2c`/`c2d` n=64 (pure `{t,r,b}`) | ~12.3 M | 12.3 M | **1.08 M** | ~11x, now linear |
| `map succ` n=18 | 10.9 M | 3.8 M | **2.31 M** | 4.7x |
| `tttD` (whoWon+drawBoard) | 1167 M | 723 M | **141 M** | **8.3x** |

The `{t,r,b}` recursion is now O(n) (native map is ~93 ITRS/element; telomare's
was ~4000x that, now within a small factor). `tttFull` — whoWon + fullBoard +
drawBoard + a `$127` refinement, i.e. most of tictactoe's per-move compute — is
**163 M ITRS (~6.5 s)**, comfortably inside a 10x-of-Haskell budget.

**Remaining blocker for the full `tictactoe.tel`, profiled to the metal.** The
minimal reproducer is `tttSP` (a `setPiece`-computed board read by `whoWon`);
`setPiece` read ONCE is 1.75 M, but read through whoWon it does not finish.
Instrumenting `hvm gen-c` with per-fid interaction counters (inject a
`g_fidc[fid]++` + cap into `interact_call`, recompile, dump the top fids) shows
the hot interactions are **`TV/P_tag` (~50% of all CALL interactions), `TV/Z`,
`TV/F_tag`** — the core pair construct/match ops — not any telomare function
and not the recursion control flow (tvFix fixed that). It is **HVM2's
copy-on-duplication of the board data structure**: whoWon's nested foldr/map
capture the board in their step closures, and every recursion step duplicates
those closures (and the board inside them). For a *literal* board (tttD) this
completes at 141 M; for the *`setPiece`* board the duplicated closures re-drive
the unreduced take/drop/concat, blowing up. This is the ORIGINAL diagnosis
(copy-on-read, `bend/PORT.md`) — now the *only* thing left after tvFix removed
the recursion-scheme overhead. A call-by-value `tvNF` force (present,
read-count-gated via `argReadCount` so it does not regress tttD) does NOT crack
it, because the cost is duplication of the *closures that capture* the board,
not just the board datum; forcing a value to NF still copies it on every dup.

**Honest bottom line:** tvFix makes *most* of a tictactoe move tractable
(`tttFull` = 163 M ~6.5 s, inside 10x). The last piece is HVM2's fundamental
copy-on-dup for the one pattern where a computed board is captured by a nested
recursion — not fixable by forcing; it needs either a board representation that
does not deep-copy (native arrays/index-passing, not available in this HVM2) or
an HVM with by-reference reads.

## Addendum 2026-07-13: the interrupted forcing test — run, theory refuted; diagnosis above CONFIRMED

The pending decisive test (tttSP under UNGATED `tvNF` forcing, gen-c-big,
expected ≈95 M if "recompute-on-dup is forceable") was run: **timeout at
600 s.** So were two further regimes from the new T2 backend
(`--emit-t2`, src/Telomare/T2Backend.hs): scope-aware gated forcing (fires
on 29 sites incl. `newBoard`, vs 0 for the old `argReadCount` gate) and
closure-boundary-respecting data forcing (`tvDF`). **No forcing regime
completes tttSP.** The paragraph above stands as written: the cost is
duplication of the closures that *capture* the board inside whoWon's nested
recursions, not the board datum.

Consumer bisection (T2 v2, all with the load-bearing `validBoard`
refinement — removing it makes the probe unsizable):
drawBoard-only over the setPiece board = **11.2 M, completes**;
whoWon-only = timeout; whoWon+drawBoard with state=emptyBoard = timeout.
The toxic pair is exactly {computed board} × {whoWon's two-deep iteration
capture} — the binding `telomare --emit-levels` statically flags as
`whoWon.board : !!`. A single-level force cannot realize a depth-2 box;
see design/T2-BEND-BACKEND.md for the measurements and the level-annotated-
runtime conclusion. Positive side: the same backend turns tttSPmin from OOM
into 3.97 M (vs 4.7 M under old ungated forcing) at +1–2 % on
tttD/tttLit/tttFull — the forcing DISCIPLINE is right; the runtime lacks
levels.
