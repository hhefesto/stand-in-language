# Progress log: `{x,y,z}` reification + space functor

Working log for the current milestone (see plan: whileD → whileS → Bend emission
→ `⟦_⟧SP`), designed through Conal Elliott's Denotational Design / Timely
Computation lens (`~/Documents/conal-elliott`). Updated as stages land.

## Design frame (from the Conal reading)

- **Derive before primitive**: bounded while is *expressible* from the existing
  vocabulary (`whileD t b = iterS (guardS t b)`); the `whileS` *primitive* is
  justified only as a **refined cost extraction** — same value denotation,
  on-demand metering (stop billing when the test goes false) vs `whileD`'s
  reserved-capacity billing (every fuel tick). Billing framing per the
  user's AWS-style charging goal (email-draft.md).
- **Fig. 1 commuting square** (Timely Computation) ≙ telomare's `precise`.
- **Resource algebra 2×2** (sequential, parallel) monoids on ℕ:
  work `(+,+)` = `⟦_⟧C` · span `(+,⊔)` = `⟦_⟧WS` · **space `(⊔,+)`** = `⟦_⟧SP`
  (to be added) · footprint `(⊔,⊔)` (noted only).
- Correction on record: tictactoe's empty-game cost 295 was **all `winnerS`**
  (the unrolled-but-skipped steps cost 0); the while rewrite is architectural,
  not a cost win.

## Stage 0 — derived `whileD` (no core change) ✅ DONE

- `tictactoe.agda`: added `guardS t b = caseS (b ∘S exlS) exlS ∘S distlS ∘S
  forkS idS t`, `whileD t b = iterS (guardS t b)`, `nonEmptyS`
  (cons↦true, nil↦false via `unconsS`).
- Replaced the 9×-unrolled `play9` with `playLoop = whileD (nonEmptyS ∘S exrS)
  playStep` at fuel `constS 9`.
- **Verified**: `nix build .#agda-tictactoe` green (all three winner `refl`s
  still type-check); `nix run .#tictactoe` → winners 0/1/2/1/1 unchanged.
  Costs (whileD, reserved-capacity): 304 / 796 / 1025 / 1097 / 1340
  (vs unrolled 295/787/1016/1088/1331 — +9 = the 9 `nonEmptyS`… wait, exactly
  +9 across the board: one `unconsS`-test tick per fuel unit; `unconsS` costs 0,
  the +9 is the 9 `iterS` ticks now always taken… -- REVISIT in Stage-1 notes:
  precisely, whileD pays the iterS tick for all 9 iterations even when guarded
  idle, and `nonEmptyS` itself is cost-0 (`unconsS`/`caseS` free)).

## Stage 1 — primitive `whileS` (on-demand metering) ✅ DONE

- `telomare.agda`:
  - constructor `whileS : (A ⇨S (unit ⊕ unit)) → (A ⇨S A) → (nat ⊗ A) ⇨S A`;
  - helpers `whileT-aux/-cont`, `whileC-aux/-cont`, `whileWS-aux/-cont`
    (mutual, **named continuation** so the precision proof's `cong`s stay
    definitional); per attempt: run test (its own cost via bind); false → stop
    free; true → 1 tel tick + body + recurse (fuel−1);
  - clauses added to `⟦_⟧K`, `⟦_⟧C`, `⟦_⟧WS`;
  - **`precise (whileS t b)`**: mutual fuel-induction `while-prec`/`cont-prec`
    mirroring `iter-prec` + a `caseS`-style split on the test value; weaves
    `precise t` at slack `m + extra` and `precise b` at slack `cr + extra`
    via the `+-assoc`/`subst`/`trans`/`cong` machinery;
  - example `drainS = whileS nonZeroS predS`;
    `drainS-test : ⟦ drainS ⟧C (10 , 3) ≡ (7 , 0)` — 3 taken steps ×(1 test +
    1 tick) + 1 final false test = 7, demonstrating early-exit metering
    (whileD equivalent would bill 20 = 10×(1 tick + 1 test)).
- **`while-prec` passed on the first attempt** (`nix build .#agda-telomare`
  green, 58s) — the mutual `while-prec`/`cont-prec` fuel induction with the
  named-continuation trick worked exactly as designed; `drainS-test ≡ (7 , 0)`
  confirmed the on-demand cost semantics by `refl`.
- tictactoe switched to `whileS` (primary `playLoop`); `whileD` kept as
  `playLoopD`/`ticTacToeD`; **agreement refls** (`agree-empty/p1/full`) prove
  both loops compute the same winner. Build green.

## Stage 2 — mechanical Bend/HVM2 emission for while ✅ DONE

- Bend template de-risked by scratch probe first (two helpers `whileGo`/
  `whileStep`, no nested `switch`; `n` stays in scope under `case _`).
- `toBendWhile init final test body` in `ctc/src/HVM.hs`: **all four morphisms
  through `toCcc`** as named globals; fuel = runtime CLI arg. Bend prelude
  extended with comparison/boolean combinators (`lessThanC` … via u24 0/1;
  `leqC = 1 - (b < a)` etc.).
- Demo `hvm-fib-while` (test `0 < n` via OrdCat, body `n-1` subC guarded by the
  test): **verified on HVM2** — fib 10/20/30 → 55/6765/832040, constant `.bend`.
- `apps.ctc-to-hvm` extended (whileS block); end-to-end app run pending final
  verification pass.

## Stage 3 — space functor `⟦_⟧SP` ✅ DONE

- Added to `telomare.agda`: `sizeT` word model; `⟦_⟧SP` = the `(⊔ , +)` cell
  (primitives in ⊔ out; `∘S` ⊔ of stage peaks; `forkS` **sum** of branch peaks;
  `caseS` taken branch; `iterS`/`whileS` structural via auxes; `fixS` coarse
  `in ⊔ out` documented); `space` extractor; refl examples `add-space ≡ (2,5)`
  and the **span/space duality** `fibPair-space : space fibPairS 10 ≡
  space fibS 10 + space fibS 10`. Build green.

## Final measured results (nix run .#tictactoe)

| game | winner | cost (whileS, on-demand) | reserved (whileD) | space |
|---|---|---|---|---|
| `[]` | 0 | 295 | 304 | 1512 |
| `[1,4,2,5,3]` (p1 row) | 1 | 792 | 796 | 1512 |
| `[1,4,9,5,7,6]` (p2 row) | 2 | 1022 | 1025 | 1512 |
| `[1,2,5,3,9,6,7]` (p1 diag) | 1 | 1095 | 1097 | 1512 |
| full board | 1 | 1340 | 1340 | 1512 |

- **on-demand vs reserved delta = exactly (9 − moves) fuel ticks** per game
  (9/4/3/2/0) — the billing story made concrete; full board coincides.
- **space constant 1512** — fixed-size board ⇒ game-independent peak, exactly
  what the (⊔,+) model predicts for this program shape.
- HVM2: `hvm-fib-while` (guarded whileS emission, all 4 morphisms via toCcc)
  → fib 10/20/30 = 55/6765/832040 on HVM2.

## Run comparison (bench-drain) ✅

One algorithm — `drainS = whileS nonZeroS predS` (telomare syntax, cost 2N
proved) — on three runtimes: Agda `⟦_⟧K` (verified reference), native GHC loop,
HVM2 via ConCat `toBendWhile` emission. `nix run .#bench-drain`; results in
**`BENCHMARK.md`**. Headlines: Agda `⟦_⟧K` ≈ **248–249 ns/tel, constant across
1M/4M/16M** (the runtime burns tel at a fixed rate — the metering story is
physical); GHC startup-dominated (~1 ns/step loop); HVM2 ≈ 2000–2250 ns/tel
sequential-worst-case, with **ITRS = 45·cost + 15 exactly** at 1M and 4M — an
empirically measured linear tel↔interactions coefficient for PARALLEL.md's
R1/R2 conjecture. Excluded + documented: `run-rs` (recursion-clone crash), GPU
(AMD box). New: `benchDrain.agda` (+`agda-benchDrain` pkg), `telomare-bench-hs`
exe, `hvm-drain-while.bend` emission, `apps.bench-drain`.

## Run comparison (BENCHMARK.md) ✅ DONE

One algorithm — `drainS = whileS nonZeroS predS` (cost 2N by refl) — timed on
three runtimes at N = 1M/4M/16M. Full table + analysis in **`BENCHMARK.md`**.
Headlines: Agda `⟦_⟧K` is a flat **~236–248 ns/tel** across 16×; GHC is
startup-dominated (loop sub-ms at 32M steps); HVM2 costs **exactly 45
interactions per tel** (ITRS = 45·cost + 15 at 1M and 4M) but **DNF'd (>150 s)
at 16M** — nonlinear degradation past ~10⁹ interactions; this is the run that
originally destabilized the machine. Runner hardened after the incident:
per-command timeouts, streamed results, HVM2 single-run, size args
(`nix run .#bench-drain -- N…`). DNFs recorded, not retried.

## Docs updated ✅

`README-Agda.md` (§8h space + resource-algebra 2×2, §8i whileS derive-then-
refine, morphism list, file table), `PARALLEL.md` (2×2 table), `ctc/
HVM-BACKEND.md` (while emission row + template note), `CHANGELOG.md`.

## Docs to update at the end

`README-Agda.md` (whileD/whileS derive-then-refine + agreement, `⟦_⟧SP`, 2×2
resource table, Timely-Computation lineage), `PARALLEL.md`, `ctc/HVM-BACKEND.md`
(while emission), `CHANGELOG.md`.
