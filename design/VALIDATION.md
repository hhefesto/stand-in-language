# Telomare 2 — §13 Validation Exercise

**Question under test** (the design's central bet, `TELOMARE2-DESIGN.md` §1):

> Recursion-limit inference (Possible.hs) and EAL box-depth inference are the
> same analysis: the level structure is simultaneously the termination
> certificate and the optimal-sharing certificate.

**Method.** Hand-decorate real telomare programs with EAL boxes using the
design doc's §8 constraint recipe; separately, read the limits Possible.hs
actually infers; compare the two structures. Every measured number below is
labeled **[measured]** and reproducible; decorations are **[analysis]**
(hand-derived, spot-checkable); imported facts are **[cited]**.

**Verdict up front: the bet is confirmed for the `{t,r,b}` fragment — which
is 100% of telomare recursion.** The box-nesting order of the hand decoration
coincides with the sizer's evaluation-dependency order in every program
tested, the free variables the decoration forces under `!` are exactly the
values the sizer's abstract evaluation replays per iteration, and the one
place the sizer must work hardest (inner tokens sized to the max over all
outer iterations) is a concrete instance of EAL's level-by-level
normalization argument. One deliberate divergence was found and is consistent
with the design's tiering (§ "pow" below).

---

## 1. How the ground truth was measured

Every telomare recursion elaborates through the surface construct
`{ test, step, base } scrutinee` (`Prelude.tel`: `d2c` l.11, `map` l.39,
`foldr` l.44, …). Possible.hs (`sizeTermM`, `src/Telomare/Possible.hs:999`)
assigns each such site a size `n` by abstract evaluation and materializes it
as the church code `SetEnv^n Env`. The hybrid emitter prints a `churchK`
fid→k table (`src/Telomare/HvmBackend.hs:375-382`) containing exactly those
k's — so inferred limits are readable from `--emit-hvm` output with **no
compiler changes**:

```
$TELOMARE_BIN --emit-hvm probe.tel > probe.bend       # stage 1 only, no hvm
awk '/^def churchK/{f=1;next} f&&/^def /{exit}
     f&&/case /{c=$2} f&&/return/&&$NF!=16777215{print c,$NF}' probe.bend
```

Binary: the working-tree build of 2026-07-06, sha256 `291f7d76…` (branch
`bend-port`, uncommitted emitter — irrelevant to sizing, which is upstream).
Probes live in the session scratchpad; each is `import Prelude` plus a
one-line `main`. Sentinel 16777215 = non-church defer. All probes size in
< 1 s of stage-1 time — including whoWon (the famous ~60 s sizing cost
belongs to full tictactoe's input-dependent event loop, not to these
closed boards).

### Measured table [measured]

| probe | program | non-sentinel churchK | reading |
|---|---|---|---|
| p_d2c | `c2d (d2c 5)` | 7 | 5 + 2 |
| p_map | `map succ [8 els]` | 10 | 8 + 2 |
| p_foldr | `foldr and 1 [3 els]` | 5 | 3 + 2 |
| p_foldr8 | `foldr and 1 [8 els]` | 10 | 8 + 2 |
| p_getsq | `left (drop (d2c 8) board9)` | 10 | d2c = 8 + 2; `drop` has NO token (church application, `Prelude.tel:93`) |
| p_dplus | `dPlus 2 3` | 5 | 3 + 2 |
| p_dtimes | `dTimes 2 3` | 6, 5 | outer d2c = 3+2; inner dPlus's d2c = **max accumulator 4** + 2 |
| p_dpow | `dPow 2 3` | 8, 6, 5 | outer = 3+2; middle (dTimes) = max acc 4 + 2; inner (dPlus) = **max acc 6** + 2 |
| p_pow | `c2d (pow $2 $3)` | 3, 2 | church LITERALS only — **no sized tokens at all** |
| p_minus | `c2d (minus $7 $3)` | 6 (+ literals 7, 3) | scrutinee `$3 left (c2d $7)` abstractly evaluated to data 4 → 4 + 2 |
| p_whowon | whoWon on `[1,1,1,0,0,0,2,2,0]` | 10, 10, 5, 5, 5, 3 | see §3 |

Three behavioral facts extracted:

- **(S1)** size = exact maximum unwindings + 2, per site, per whole-program
  input — tight values from abstract evaluation, not worst-case powers.
- **(S2)** a token inside another iteration is sized to the **max over all
  outer iterations** (dTimes: inner dPlus runs with accumulators 0,2,4 →
  sized 4+2; dPow: inner-inner sees 0,2,…,6 → 6+2).
- **(S3)** a compound scrutinee is **fully evaluated before its consumer is
  sized** (minus: `$3 left (c2d $7)` → 4, then d2c sized 6).

(Two probe crashes during the exercise were *probe* type errors — `c2d`
applied to a data nat — not sizing failures; the sizer surfaces surface type
errors as `sizeTermM unhandled case` crashes. Side-observation for future
error-message work. Note `ttt_whowon.tel` at the repo root contains exactly
this bug in its `main`; the corrected probe replaces `concat [c2d w]` with
`[w]`.)

---

## 2. The generic decoration: one `{t,r,b}` = one box [analysis]

Desugared, `{t,s,b} x` is a church-bounded fixpoint: with
`Φ = λrecur. λi. if t i then s recur i else b i`, the construct is
`n ⟨Φ⟩ ⟨b⟩ x` — the (inferred) numeral `n` produces the n-fold composite of
Φ and applies it. Applying the §8 constraint recipe to this skeleton:

- `recur` occurs once in `s` — affine, no constraint.
- The numeral duplicates Φ n times, so **Φ sits inside a box** (this is the
  contraction-licensing constraint: n's type is `!(F ⊸ F) ⊸ !(F ⊸ F)`
  [cited: EAL church numerals]).
- Therefore **every free variable of the step is forced under `!`** (it is
  copied into each of the n copies of Φ), and the scrutinee, base, and result
  all live **one level deeper** than the orchestration.

Solved level assignment for the three Prelude workhorses (single box each):

| site | free vars of step forced under `!` | levels |
|---|---|---|
| `d2c n f b` | `f` | n at 0; f, b, result at 1 |
| `map f l` | `f` | list consumed at 1; result at 1 |
| `foldr f b ta` | `f` | accumulator threaded affinely at 1 |

**Comparison:** Possible.hs gives each of these sites exactly one token with
k = data bound + 2 [measured, rows 1–4]. One site, one box, one token, one
number. The variables the decoration boxes (`f`) are precisely the values the
sizer's evaluation re-enters per unwinding. Consistent. ✓

---

## 3. whoWon — the nested-foldr program [analysis + measured]

Source (`ttt_whowon.tel` / `tictactoe.tel:48-65`): outer
`foldr combineRow 0 rows` over 8 rows; each `doRow` runs
`map (\x -> getSquare (d2c x) board) row` (3 positions), then
`foldr and 1 (map (dEqual p) pieces)` twice; `getSquare = left (drop pos
board)` with `drop` a church application driven by `d2c x`; `dEqual` reuses
`d2c` on `left a` (piece values ≤ 2, so bound ≤ 1).

**Hand decoration.** Box tree (levels in parentheses):

```
main (0)
└─ B_foldr rows (0→1)                      bound 8
   ├─ B_map pieces (1→2)                   bound 3
   │  └─ B_d2c position (2→3)              bound ≤ 8
   │       output = a church numeral, CONSUMED BY drop AT LEVEL 3
   │       — the output-one-level-deeper law, in the wild
   ├─ B_map (dEqual p) / B_foldr and (1→2) bound 3
   │  └─ B_d2c in dEqual (2→3)             bound ≤ 1
```

Forced `!` positions: `board` is free in the pieces-map step (copied across 3
positions) *and* that map sits inside the rows-fold step (copied across 8
rows) — so **board : `!!`**, two strata deep, and nothing else needs more
than the generic one-box-per-site pattern. No same-level feedback anywhere
(no iteration's output is used as a step at its own level) — **stratifies
cleanly**; Tier 1.

**Measured** [row p_whowon]: six sized fids, k ∈ {10, 10, 5, 5, 5, 3}.
Association (confirmed by the single-site probes p_getsq, p_foldr8, p_foldr):
the 8-bound sites (rows-fold, position-d2c) → k=10; the 3-bound row-level
sites (maps/and-folds) → k=5; the piece-level d2c inside dEqual → k=3.
(Six fids vs three textual `{t,r,b}` sites: emission-level duplication of
church codes; the k-value groups are what carry the comparison.)

**Comparison.** The k-groups partition exactly along the strata of the box
tree: {8-bound} at the fold/position layer, {3-bound} at the row layer,
{1-bound} at the piece layer. And the deepest bound (dEqual's 1) is
determined by data reachable only through the outer iterations — the sizer
had to run the outer strata to find it, which is (S3)/(S2) = the box-nesting
order. Consistent. ✓ Also note `board : !!` is precisely the value the
bend-port experiments caught being duplicated catastrophically when unshared
(`bend/HYBRID_PROGRESS.md`) — the decoration finds it statically.

---

## 4. dPow — the tower [analysis + measured]

`dPow a b = d2c b (dTimes a) 1`; `dTimes a x = d2c x (dPlus a) 0`;
`dPlus a x = d2c x succ a`. The step of each d2c is *built by* the next d2c
in — but always used one level deeper, never fed back at its own level:

```
B_d2c dPow (0→1)  bound b            = 3   → measured k = 5  ✓
└─ B_d2c dTimes (1→2)  bound = accs {1,2,4}, max 4  → k = 6  ✓
   └─ B_d2c dPlus (2→3)  bound = accs {0,2,…,6}, max 6 → k = 8  ✓
```

Stratifies at fixed depth 3 — EAL-typable, exactly as predicted (iterated
multiplication is the EAL-friendly exponential; [cited: Danos–Joinet]).

**This is the sharpest confirmation in the exercise:** (S2) — the inner token
sized to the max over all outer iterations — is EAL's normalization argument
made operational: *level-(k+1) material is duplicated wholesale by level-k
orchestration, and its size is bounded by a function of the level-k part*
[cited: Girard's level-by-level cut elimination]. The sizer computes, per
level, precisely the quantity the elementary-bound proof quantifies over.

---

## 5. minus — the compound scrutinee [analysis + measured]

`minus a b = d2c (b left (c2d a))`: the d2c's scrutinee is itself an
iteration result. Decoration: `b`'s orchestration at level 0 copies `left` at
level 1; the resulting data nat lives at level 1; the consuming d2c's box
must therefore sit at 1→2 — **the consumer's box is strictly deeper than the
producer's**, forced by the depth-matching constraint at the application.

**Measured**: literals 7 and 3 pass through unsized; the d2c token is sized
6 = (7−3) + 2 — the sizer evaluated the inner iteration to completion
*first* (S3), then sized the consumer. Evaluation-dependency order =
box-nesting order. Consistent. ✓ (The historical worry that compound
scrutinees "lose information" did not materialize here: the whole-program
abstract evaluation preserved the exact bound.)

---

## 6. pow — the deliberate divergence [analysis + measured]

`pow m n = n m` on church literals (`pow $2 $3`). **Measured**: churchK shows
only the literals (3, 2) — **no sized tokens exist**; the program is
invisible to the sizing analysis, total by simple types alone.

EAL decoration: `n m` types with `m` boxed inside `n`'s duplication — the
result numeral is usable only one level down; and the pathological relative
`λn. n n` is untypable at any fixed level (it manufactures towers of dynamic
height) [cited: standard EAL folklore; design doc §7].

So here the two analyses genuinely differ in *scope*: Possible.hs has nothing
to say (no `{t,r,b}` sites), while EAL still imposes levels — because levels
serve the *runtime* theorem (oracle-free fan pairing), not just termination.
This is not a counterexample to the bet; it delimits it: **the analyses
coincide on the `{t,r,b}` fragment (= all telomare recursion); church-literal
higher-order arithmetic is extra surface where only the EAL side has content,
and a program like `λn. n n` is exactly what the design already routes to
Tier 2.** In Telomare 2 numerals-as-iterators become `iterS` applications, so
this surface folds back into the compiler-owned fragment where the analyses
agree (design doc §8).

---

## 7. Conclusions

| program | hand levels | Possible.hs | coincide? |
|---|---|---|---|
| d2c / map / foldr | 1 box | 1 token, k = bound+2 | ✓ |
| whoWon | 3 strata; board `!!` | k-groups {10}{5}{3} partition by stratum | ✓ |
| dPow | depth-3 tower | 3 tokens, inner = max over outer iters (S2) | ✓ (sharpest) |
| minus | consumer box deeper than producer | scrutinee evaluated first (S3) | ✓ |
| pow | levels required (runtime) | no tokens (nothing to size) | scope divergence, by design → §6 |

1. **The bet holds where it was made**: on the `{t,r,b}` fragment, box
   structure and sizing structure are the same object viewed statically vs
   operationally. In Telomare 2 terms: **levels are recoverable purely
   structurally** (one box per recursion construct, nest by syntactic
   containment plus scrutinee-dependency — no search), while the **k values
   need evaluation** — which is exactly the design's split: levels by
   inference (§8), budgets by the cost functor (§7).
2. (S2) is the elementary-bound argument running inside the current compiler
   — strong evidence the EAL reading is the right *theory of* Possible.hs,
   not a foreign discipline bolted on.
3. The divergence (pow) is confined to church-literal arithmetic, is handled
   by the design's tiering, and disappears under Telomare 2's `iterS`
   elaboration.

**Threats to validity.** Decorations were solved over the surface/desugared
skeleton, not the exact Term3 the sizer sees (sizing's +2 padding and the
emission-level fid duplication are visible seams). Token↔site association
for whoWon is by single-site probe diffing, not instrumentation. One board
input for whoWon. The pow analysis is analytical only (nothing measurable on
the sizing side — that absence being the point).

---

## 8. Follow-up: the structural box-placement pass, prototyped

Conclusion (1) above — *levels are recoverable purely structurally* — is now
a program: `telomare --emit-levels <file.tel>`
(`src/Telomare/Levels.hs`, wired in `app/Main.hs`; uncommitted). It assigns
every reachable `{t,s,b}` site an EAL level with **no evaluation and no
search**, from two ingredients:

1. **containment** — a site's test/step/base contents are one level deeper;
2. **parameter-offset summaries** — for each definition, how many boxes deep
   each parameter's occurrences sit; at call sites, argument *j* is walked
   `offset(f, j)` levels deeper. This is how `d2c b (dTimes a) 0` places
   `dTimes`'s own recursion one level below `d2c`'s: the step argument is
   duplicated by the numeral. Offsets compose along call chains (this is the
   §8 constraint system solved by construction — the compiler-owned-constructs
   argument made executable).

It also reports, per binder, the max levels-below-binding of any occurrence
(`use − bind`, composed through offsets) — i.e. **which values are forced
under `!` and how deep**.

**Results, checked against the hand decorations of §§2–6 [measured]:**

| program | `--emit-levels` output | vs hand decoration |
|---|---|---|
| d2c / map / foldr | 1 site @ level 0; `f : !` | ✓ |
| dPow | one textual site at levels 0, 1, 2 via `dPow > dTimes > dPlus`; `dPow.a : !!!`, `dTimes.a : !!`, `dPlus.a : !` (the multiplicand present at every stratum) | ✓ (and sharpened the hand analysis: composed offsets give a's true depth 3) |
| whoWon | {fixed@0}, {fixed@1, map@1}, {d2c@2}; **`whoWon.board : !!`** | ✓ (§3's strata and the board `!!` exactly) |
| pow | no sites | ✓ (church-literal fragment, §6) |
| minus | d2c @ level 0 | **known approximation**: the hand decoration puts it at 1 because the scrutinee is a numeral *application* — church-literal producers are invisible to the structural pass, the same §6 fragment |
| **tictactoe.tel (full)** | **37 ms**, towerHeight 3, 8 site-classes; `main.newBoard : !`, `main.input : !!`, `whoWon.board : !!` | n/a (beyond the hand exercise) — statically names the exact bindings whose unpriced duplication was the bend-port blowup |

Contrast of costs: Possible.hs needs ~60 s of abstract evaluation to find
tictactoe's *budgets*; the structural pass finds its *strata and dup-forced
bindings* in 37 ms. Exactly the design's division of labor (§7/§8 of the
design doc): levels by structure, budgets by the cost functor.

**Prototype limitations** (documented in the module header): church-literal
iteration is invisible (`minus`'s producer, `pow`); unknown higher-order
heads contribute offset 0 to their arguments; one witness path per
(site, level) class; locals resolve against use-site scope; Case patterns
don't bind for the `!` report.
