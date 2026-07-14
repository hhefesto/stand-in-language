# The Telomare 2 backend on Bend/HVM2 — `telomare --emit-t2` / `nix run .#telomare2`

**Status: prototype, measured (2026-07-13). All numbers reproducible by the
commands recorded here. Uncommitted on branch `bend-port` (new .hs files are
git-staged so the flake app builds from the working tree).**

## What this is

An end-to-end execution path for telomare programs under the **Telomare 2
affine discipline** (design/TELOMARE2-DESIGN.md §12, the migration table made
executable):

```
program.tel
  → Haskell front end (parse, resolve, Possible.hs recursion sizing)   [reused]
  → src/Telomare/T2Backend.hs: sized CompiledExpr emitted as Bend       [NEW]
      under the T2 rules (below); same generated-program contract as
      the legacy emitter, so the same shell driver runs both
  → bend gen-hvm → hvm gen-c (+arena/defs_buf patch) → gcc → run       [reused]
```

Run it: **`nix run .#telomare2 -- program.tel < moves`**
(driver = `bend/run_telomare_hvm.sh`; the flake app sets
`TELOMARE_EMIT_FLAG=--emit-t2` and defaults to the `gen-c-big` runner.
`TELOMARE_EMIT_FLAG=--emit-t2-lazy` gives the discipline-off baseline through
the identical code path; `--emit-t2-letonly` disables only the iteration-entry
box.) Verified end-to-end: `p_dpow` via the flake app produces the oracle
transcript.

## The discipline

The legacy backend lets HVM2's lazy dup handle every non-affine read. Lazy
dup duplicates *computation*: a binding whose value is an unreduced redex
graph is re-reduced per read. Telomare 2's core licenses contraction only on
boxed values (`dupS : !A ⇨ !A ⊗ !A`), and a box is a *value*. Operationally:
**force once at the box site; copies afterwards are of realized data.** Two
static rules — exactly the two `!`-shapes `telomare --emit-levels` reports:

1. **dupS at let-contraction** (the `main.newBoard : !` class): an appB
   binding of a computed value (`worthForcing`) is forced at the binding —
   unless *provably affine* (read ≤ 1). Read-counting is scope-aware
   (`deepArgReads`): a let chain compiles to nested closures, and the same
   binding is reachable at `Left (Right^k env)` k scopes down. The legacy
   `closureArgReads` gate stopped at scope boundaries and missed every
   let-chain consumer — measured: it fires on **0** sites in tttSP where the
   scope-aware count fires on **29**. Opaque continuations are boxed
   conservatively (unknown use counts as use-many).
2. **boxS at the iteration boundary** (the `whoWon.board : !!` class): the
   step closure of a sized recursion is forced once at loop entry, before
   `tvRepeat`/`tvFixApply` copy it per unwinding.

**The force operator matters.** v1 used the legacy deep `tvNF`, which walks
*through* closures (captured environments). In EAL terms that is reduction
across a box boundary — and it measurably grinds (see table). v2 uses
`tvDF`, **data normal form**: realize data spines, stop at closure heads
(`P(F fid, cap)` keeps `cap` untouched). A box's contents are realized at
the box's own binding, never transitively from outside. tvDF is both the
theoretically correct reading and strictly faster everywhere measured.

Every emitted program carries a static **cost certificate** header: dupS
site count, iterS site count, and the inferred iteration budgets (churchK —
the numbers design/VALIDATION.md reads as EAL levels).

## Results

Probes are the workstream-A carve-outs of `tictactoe.tel` (bend/
HYBRID_PROGRESS.md; sources in the session scratchpad, reconstruction
recipes below). Runner `gen-c-big`, input `"1"`, 600 s budget. ITRS is
deterministic; wall times from this session's machine.

| probe | baseline (lazy dup) | legacy `--emit-hvm` (ungated tvNF) | T2 v1 (tvNF) | **T2 v2 (tvDF)** |
|---|---|---|---|---|
| tttSPmin (setPiece, 3 direct reads) | OOM [historical] | 4.7M [historical] | 5.1M, 0.22 s | **3.97M, 0.16 s** |
| tttD (whoWon+drawBoard, gate board) | 141.08M | 177.84M (+26%) | 220.96M (+57%) | **143.79M (+1.9%), 5.9 s** |
| tttLit (literal board) | 93M [historical] | — | — | **93.87M (+0.9%), 3.9 s** |
| tttFull (most of a move, gate board) | 163M [historical] | — | — | **166.66M (+2.3%), 6.9 s** |
| tttSP (setPiece board → whoWon+drawBoard+state) | OOM [historical; run-c OOM reconfirmed] | **timeout 600 s** | timeout 600 s | timeout 600 s |
| full tictactoe | exceeds budget [historical] | — | — | not run: tttSP ⊂ tictactoe |

Consumer bisection of tttSP under T2 v2 (all keep the load-bearing
`validBoard` refinement — removing it makes the program UNSIZABLE,
`RecursionLimitError`; the refinement is what bounds `setPiece`'s
`concat`/`drop` over the input board):

| variant | consumers of the setPiece board | result |
|---|---|---|
| tttSPw | drawBoard only | **11.21M, 0.45 s — completes** |
| tttSPd | whoWon only (+state) | timeout 600 s |
| tttSPs | whoWon + drawBoard, state = emptyBoard | timeout 600 s |
| tttSPmin | 3 bare getSquares | 3.97M |

**Parity:** `p_dpow` and `tttD` transcripts byte-identical to the Haskell
oracle through the full driver; `p_dpow` also via `nix run .#telomare2`.
T2Lazy reproduces the historical baseline ITRS exactly (141,075,149 on
tttD) — the fork is measurement-clean.

## Findings

1. **The dupS discipline works on its class.** tttSPmin: OOM → 3.97M. The
   contraction-of-computed-lets blowup is fixed by scope-aware gated forcing,
   at ~1–2% overhead on programs that never need it (tttD/tttLit/tttFull) —
   versus +26% for legacy ungated tvNF and +57% for blanket tvNF. The
   overhead ordering (tvDF-gated < tvNF-ungated < tvNF-everywhere) is the dup
   grade made visible.
2. **Workstream A's pending theory is refuted.** The interrupted decisive
   test ("tttSP with ungated forcing ≈ 95M and completes") was run: it times
   out at 600 s. No forcing regime — lazy, tvNF, tvDF, gated or not —
   rescues tttSP.
3. **The blocker is localized: a computed ({t,r,b}-produced) board consumed
   by whoWon's nested iterations.** Same board through drawBoard's
   church-indexed reads: 11M. Gate-produced board through whoWon: 144M.
   Computed board through whoWon: >600 s. Production is innocent,
   state-threading is innocent, the *pairing* is toxic: the board crosses
   TWO iteration boundaries (row fold → per-row map/foldr) via captured-env
   chains — exactly the binding `--emit-levels` flags as `whoWon.board : !!`.
   A depth-1 fix (force at binding) cannot realize a depth-2 box; HVM2 has
   no level machinery to price or pair the inner duplications.
4. **The refinement types are load-bearing for sizing** (tangential but
   notable): every attempt to bisect the asserts away produced
   `RecursionLimitError` — `validBoard`'s `$9` is what bounds `setPiece`'s
   recursion over the input board. Refinements aren't checks bolted on; they
   are the totality certificate.

## Verdict — does this backend have a chance?

**On the discipline: yes, demonstrated.** The T2 rules turn the
recompute-on-contraction class from OOM into milliseconds, cost ~2% where
unneeded, are placed by a static analysis that agrees with the levels pass,
and ship a static cost certificate per program. This is the design's dup
grade + box placement working end to end on real programs, and it
strictly dominates the legacy backend's forcing experiments.

**On HVM2 as the Tier-1 runtime: no — and now with a precise reason.** The
surviving blowup is a depth-2 sharing pattern (`whoWon.board : !!`) that no
single-level, syntax-directed forcing can realize, under any regime. This
is the strongest empirical argument yet for the design's actual Tier-1
claim: EAL-*level-annotated* interaction nets, where the fan carrying the
board into the row iteration and the fans inside the per-row folds are
paired by static level — not HVM2's global lazy dup plus compensating
forces. The backend didn't fail the design; it isolated the exact feature
the design's runtime must have and HVM2 lacks. (Corollary: full tictactoe
stays out of reach on HVM2 — tttSP is a sub-program of it.)

Next steps if pursued: (a) emit per-level dup operators for bindings the
levels pass marks `!^k` — a depth-2 force materializing the board *inside*
the row-fold frame (one realized copy per row, 8 copies, bounded by the dup
grade) would be the depth-aware fix within HVM2; (b) alternatively, target
a runtime with labeled fans (HVM's lab-carrying dups) using levels as
labels — the design's Tier 1 proper.

## Reproduce

```
nix develop --command cabal build exe:telomare
TELOMARE_BIN=dist-newstyle/build/x86_64-linux/ghc-9.6.7/telomare-0.1.0.0/x/telomare/build/telomare/telomare

$TELOMARE_BIN --emit-t2 <prog>.tel | head -10        # static certificate
nix run .#telomare2 -- <prog>.tel < moves            # end to end
TELOMARE_EMIT_FLAG=--emit-t2-lazy nix run .#telomare2 -- <prog>.tel < moves  # baseline
```

ITRS measurements used a gen-c-big harness (emit → gen-hvm → gen-c → patch
`G_NODE_LEN`/`G_VARS_LEN` to 1<<30 and `defs_buf` to 0x20000 → gcc -O2
-DTPC_L2=0 → run, timeout-wrapped, output capped). Probe reconstruction:
tttSP/tttD/tttSPmin/tttFull/tttLit per bend/HYBRID_PROGRESS.md; tttSPw =
tttSP with `winner = 0`; tttSPd = tttSP without `drawBoard newBoard` in the
output; tttSPs = tttSP with state `(0, emptyBoard)`.

## Known limitations

- Contraction reachable only through opaque continuations is boxed
  conservatively (over-forcing, never unsoundness).
- tvDF stops at closure heads by a value-shape heuristic (`P(F,·)`); a
  data pair whose first element is genuinely a closure value stays lazy
  (undercount of realization — safe).
- The dupS/boxS placement is syntax-directed (appB shape, repeat machinery);
  it is the operational shadow of the levels pass, not yet driven by it.
  Unifying them (emit forces exactly where `--emit-levels` prints `!`) is
  the natural next iteration.
