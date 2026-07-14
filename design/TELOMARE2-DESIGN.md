# Telomare 2 — Design

**A total language with machine-checked time and memory bounds, designed
denotationally, with Elementary Affine Logic as the duplication discipline.**

Status: design document (greenfield — deliberately unconstrained by the current
8-combinator core). Companion artifact: `design/telomare2.agda`, a type-checked
skeleton of the core category and its resource interpretations.

Every claim in this document is labeled one of:

- **[proved]** — machine-checked in `design/telomare2.agda` or in the `agda`
  branch's `telomare.agda`.
- **[measured]** — empirically measured in this repository (file cited).
- **[cited]** — imported metatheory from the literature (reference given).

---

## 1. Motivation and evidence

Telomare's promise is *totality with knowable resource bounds*: every program
terminates, and the compiler can tell you how much time and memory it needs
before you run it. The current implementation delivers totality through
`repeatFunctionS`-funneled bounded recursion plus the `Possible.hs`
recursion-sizing abstract interpreter. This design reconstructs that promise
from first principles, incorporating three bodies of evidence accumulated in
this repository:

**Evidence 1 — the `agda` branch (`telomare.agda`, `README-Agda.md`).**
A denotational-design formalization already exists and works: a typed syntax
category `_⇨S_` whose only recursion is fuel-carrying (`iterS`, `whileS`),
interpreted by four resource functors — execution (`TelM`), cost (`CostM`),
work/span, and space — with a machine-checked **adequacy theorem**: running a
program with its auto-computed budget always finishes **[proved]**. Measured
results: tictactoe ≈ 1000 tel per game, space constant 1512 across games
**[measured, `agda:PROGRESS.md`]**; HVM2 executes the metered drain benchmark
at *exactly* 45 interactions per tel on duplication-free programs
**[measured, `agda:BENCHMARK.md`]**.

**Evidence 2 — the `bend-port` branch (`bend/HYBRID_PROGRESS.md`).**
Running the *current* telomare on interaction nets (HVM2) exposed the cost
model's blind spot. Two findings matter here:

1. The catastrophic cost on interaction nets is **duplication** — copying of
   data on every non-affine read, and recompute of closures on dup. Programs
   that share a computed value across many readers (tictactoe's `newBoard`)
   went from tractable to out-of-memory purely on duplication structure
   **[measured]**. No functor on the `agda` branch prices this.
2. Reifying recursion as counted loops (`tvRepeat`) and self-unwinding
   closures (`tvFix`) instead of church-numeral towers was an 8–11× win
   **[measured]** — evidence that *fuel-carrying, reified recursion is the
   right core primitive*, operationally and not just logically.

**Evidence 3 — Elementary Affine Logic.**
EAL-typable terms enjoy two theorems from one typing discipline:
normalization in elementary time **[cited: Girard, "Light Linear Logic";
Danos–Joinet, "Linear Logic and Elementary Time"]**, and Lévy-optimal
reduction on sharing graphs *without the bookkeeping oracle*
**[cited: Asperti, "Light affine logic and optimal reduction";
Coppola–Martini]**. The mechanism — stratified duplication via `!`-boxes — is
philosophically the discipline telomare already imposes: "you may duplicate
this, this many levels deep."

The design thesis, in one line:

> **Telomare's recursion-limit inference and EAL's box-placement inference are
> the same analysis. The level structure is simultaneously the termination
> certificate and the optimal-sharing certificate.**

## 2. Architecture: the trusted core and the runtime are different objects

"Central calculus" is two jobs that need not be done by one object:

- the **semantic core** — where meaning and totality are *defined*, the thing
  the definitional interpreter runs; the trusted kernel;
- the **operational representation** — the thing you reduce efficiently.

Termination checking is a front/middle-end property; optimal evaluation is a
backend property. Lamping's algorithm exists precisely so that lambda calculus
can be reduced Lévy-optimally *without changing the source calculus*. So
Telomare 2 does not marry its runtime:

```
surface language          plain total functional programming; duplication
      │                   written freely; no modalities anywhere
      ▼
core category             affine, distributive, bicartesian monoidal category;
(trusted kernel)          EAL !-boxes placed by whole-program inference;
      │                   recursion only via fuel-carrying, level-typed
      │                   iteration; denotational semantics + resource
      │                   functors + adequacy proofs live HERE
      ▼
┌─ Tier 1 ────────────────┐   ┌─ Tier 2 ─────────────────────┐
│ level-annotated          │   │ metered graph reduction      │
│ interaction nets:        │   │ (definitional interpreter    │
│ oracle-free, Lévy-       │   │ or GHC-style evaluator):     │
│ optimal, parallel        │   │ total-but-unstratifiable     │
└──────────────────────────┘   └──────────────────────────────┘
```

A guiding principle: **minimality of the trusted part matters more than
minimality of the whole.** Interaction combinators are unbeatably minimal
(three agents, six rules), but their meaning is only available through a
translation, so going IC-native makes the trusted base = translation + net
semantics — larger than a small direct interpreter. The nets are therefore a
*backend*, verified against the core's denotation, not the definition of the
language.

A bonus the net backend brings: interaction nets are strongly confluent, so
**termination and step-count become strategy-independent properties of the
program** rather than of program-plus-strategy — recursion budgets are
well-defined without reference to an evaluation order **[cited: Lafont,
"Interaction Combinators"]**.

Rejected foundations, for the record: **tree calculus** (unique intensional
powers — programs inspecting programs without quotation — but no intrinsic
termination story, no sharing/optimality theory, and it breaks η; keep it in
mind as a possible future *layer*, not a foundation). **HVM-style IC-native
semantics** (duplicating a lambda yields superposition semantics that diverge
from LC at the edges; we instead restrict to the fragment where the embedding
is faithful — which is exactly what EAL typing delimits).

## 3. Methodology: Denotational Design

Following Conal Elliott (Denotational Design with Type Class Morphisms;
Compiling to Categories, ICFP 2017):

1. **Choose the semantic model first.** Every type gets a mathematical
   meaning; every program gets a mathematical function.
2. **Specify operations as homomorphisms** (`⟦f ∘ g⟧ = ⟦f⟧ ∘ ⟦g⟧`, …). A
   failed homomorphism is a detected abstraction leak, not a shrug.
3. **Derive implementations from the homomorphism equations.** The equations
   usually determine the implementation; laws are inherited from the model.

The move that makes resource bounds *denotational* rather than bolted-on is
Elliott's Compiling-to-Categories: write programs as morphisms of a syntax
category, then interpret the same syntax in several categories. The `agda`
branch already demonstrates this with four interpretations; Telomare 2 keeps
the pattern and adds the one interpretation the `bend-port` experiments proved
is missing (duplication) plus the typing discipline that controls it (EAL).
The metering lineage is Elliott's *Timely Computation*: cost as a semantics,
not a profiler.

## 4. The semantic model

**Types denote sets.**

```
⟦unit⟧ = 1        ⟦A ⊗ B⟧ = ⟦A⟧ × ⟦B⟧       ⟦list A⟧ = List ⟦A⟧
⟦nat⟧  = ℕ        ⟦A ⊕ B⟧ = ⟦A⟧ ⊎ ⟦B⟧       ⟦!A⟧     = ⟦A⟧
```

Note `⟦!A⟧ = ⟦A⟧`: the modality is **cost- and discipline-relevant but
value-irrelevant**. `!` changes what you may *do* with a value (duplicate it)
and what that *costs*, never what the value *is*. This is the design's TCM
moment: the value semantics must not be able to observe boxes.

**Programs denote functions.** `⟦f : A ⇨ B⟧V : ⟦A⟧ → ⟦B⟧`, a plain total
mathematical function. This is the specification against which every backend
is judged.

**Resources denote grades.** A resource interpretation is a functor from the
syntax category into the Kleisli category of a monad graded by an ordered
monoid `(M, ⋄, ε, ≤)`; functoriality is the composition law

```
grade (g ∘ f) a  =  grade f a  ⋄  grade g (⟦f⟧V a)
```

— cost flows through the *value* semantics, which is what makes grades exact
rather than worst-case. Each resource functor comes with an **adequacy
theorem**: executing with the computed grade always succeeds. (Proved by the
"precision with slack" induction: `⟦f⟧K a (cost + extra) ≡ just (val, extra)`;
adequacy is the `extra = 0` corollary. **[proved]**, both in `telomare.agda`
§8e/§9 and reproduced for the new core in `telomare2.agda`.)

## 5. The core category

Objects:

```
Ty ::= unit | nat | A ⊗ B | A ⊕ B | list A | !A
```

Morphisms, in four groups:

**(a) Affine symmetric monoidal structure.** `id`, composition, `f ⊗ g` on
morphisms, symmetry, unit introduction, and — because we are *affine*, not
linear — free weakening: `weak : A ⇨ unit` and the projections
`exl : A ⊗ B ⇨ A`, `exr : A ⊗ B ⇨ B` (projections discard, which is
weakening, which is free). **What is absent is contraction**: there is no
`fork f g : A ⇨ B ⊗ C` and no `dup : A ⇨ A ⊗ A` on ordinary objects. Using an
input twice is not something the plain monoidal fragment can express. This is
the single deletion from the `agda` branch's category, and everything else in
the design flows from it.

**(b) Data: coproducts, distributivity, lists, naturals.**
`inl`, `inr`, `case`, `distl : A ⊗ (B ⊕ C) ⇨ (A ⊗ B) ⊕ (A ⊗ C)` (a branch
keeps its context — distributive category), `nil/cons/uncons`,
`natOut : nat ⇨ unit ⊕ nat`, `suc`, `add`, `const k`. All exactly as on the
`agda` branch. One pragmatic addition backed by measurement:
`dupNat : nat ⇨ nat ⊗ nat`. Machine-scalar duplication is free on interaction
nets (HVM2 dups a u24 in one interaction, with none of the structural-copy
pathology — **[measured, `bend/HYBRID_PROGRESS.md`, the `TV/N` native-number
optimization]**), and an atom contains no redexes, so duplicating it cannot
disturb sharing or fan pairing. Atoms are exempt from the discipline because
the discipline exists to police exactly what atoms don't have.

**(c) The EAL exponential — the entire duplication interface:**

```
dup    : !A ⇨ !A ⊗ !A                    -- contraction: ONLY on banged types
box    : (A ⇨ B) → (!A ⇨ !B)             -- promotion (functoriality of !)
boxVal : (unit ⇨ A) → (unit ⇨ !A)        -- promotion with empty context
merge  : !A ⊗ !B ⇨ !(A ⊗ B)              -- monoidality of promotion
```

And, load-bearingly, **nothing else**. In particular:

```
der : !A ⇨ A      -- DOES NOT EXIST (dereliction)
dig : !A ⇨ !!A    -- DOES NOT EXIST (digging)
```

In full linear logic `!` is a comonad — dereliction is its counit, digging its
comultiplication. EAL is linear logic with both deleted: `!` degrades to a
functor with contraction. `A`, `!A`, `!!A` are three unrelated strata with
functorial maps deeper (via `box`) and no coercions between. Weakening stays
free for *everything* (that's the "affine"), which is why users never think
about discarding.

**(d) Recursion** — §7.

### Depth

The **depth** of a subterm is the number of `box`es enclosing it; the depth of
a program is its maximum box nesting — a static, syntactic number. Because
dereliction and digging don't exist, *no reduction step ever moves material
across a box boundary*, so depth is fixed before reduction begins. Levels are
geological strata: computation at level *n* can orchestrate wholesale copying
of level-(*n*+1) packages, but nothing migrates between strata.

## 6. Stratification: one invariant, two theorems

**Theorem (elementary termination) [cited: Girard; Danos–Joinet].**
Cut-elimination can be organized level by level. Reducing all redexes at depth
0 may duplicate depth-1 boxes — but only by a factor bounded by the size of
the depth-0 part, and depth 0 itself only shrinks; then move to depth 1, and
so on. Since depth never grows, total work is bounded by a tower of
exponentials whose height is the program's *syntactic box depth*. Termination
isn't an analysis bolted onto EAL — it is what the type system *is*.

**Theorem (oracle-free optimal reduction) [cited: Asperti; Coppola].**
Lévy-optimality demands no redex family be reduced twice; Lamping's sharing
graphs achieve it with fan nodes, and the notorious difficulty is *fan
pairing* — when a fan meets a fan, do they annihilate (same sharing) or
duplicate through each other (unrelated)? For arbitrary LC the answer is
context-dependent and the croissant/bracket "oracle" exists solely to track
it — and the oracle's own bookkeeping can blow up **[cited:
Asperti–Mairson]**. Under stratification the answer is static: **fans pair iff
they carry the same level, and levels never change during reduction.**
Annotate each fan with its box depth at translation time; pairing becomes an
integer comparison; the oracle evaporates.

Both theorems are restatements of one fact: *the strata are fixed before
reduction begins.* This is why the design treats them as imported metatheory
(**[cited]**, stated with references in `telomare2.agda`) rather than
something to re-prove: what we prove locally is adequacy of our functors on
our syntax; what we inherit is the metatheory of the discipline our syntax is
embedded in.

For Telomare this should feel familiar: the current language also fixes its
budget syntactically before running. EAL's refinement is that the budget has a
*shape* — a level structure — rather than being one scalar, and the budget
arithmetic is done by typing rather than by abstract interpretation.

## 7. Limited recursion = levels

There is no `fix` and no `Y` — self-application of a duplicable at its own
level is precisely a dereliction-shaped move, and its absence is what makes
depth static. All repetition comes from data:

```
iter  : (A ⇨ A) → (nat ⊗ !A) ⇨ !A       -- n and a boxed seed; step applied
                                          -- n times, one level down
fold  : ((B ⊗ A) ⇨ B) → (list A ⊗ !B) ⇨ !B
while : (A ⇨ unit ⊕ unit) → (A ⇨ A) → (nat ⊗ !A) ⇨ !A
                                          -- fuel + test; on-demand metering
                                          -- (charges per TAKEN step; see the
                                          -- agda branch's whileS)
```

The type of `iter` *is* the EAL story of Church numerals. In EAL a numeral has
type `N = !(A ⊸ A) ⊸ !(A ⊸ A)`: it receives a boxed step function — boxed
because it is about to be duplicated n times — and returns the boxed n-fold
composite. A number is not a thing you pattern-match; it is *the ability to
duplicate a level-(k+1) package n times under level-k orchestration*. Hence
the fundamental law, visible in `iter`'s type:

> **The output of an iteration lives one level deeper than the orchestration
> that produced it.**

You may use that output as the step of a *further* iteration — at its own,
deeper level. What you cannot do is feed it back as the step of an iteration
at the *original* level: that would need `!(A⊸A) ⇨ !!(A⊸A)` digging or a
dereliction to unwrap, and neither exists. Concretely `λn. n n` is untypable —
and not incidentally: `n n` is how you build exponential towers of *dynamic*
height, exactly what the "depth is fixed statically" theorem forbids.
Meanwhile `add`, `mult`, `exp`-with-static-exponent-position all typecheck,
each landing a fixed number of levels down.

**Relation to the complexity literature.** Fuel-as-data with level-stratified
step functions is the categorical form of predicative/ramified recursion
(Bellantoni–Cook's safe/normal separation, Leivant's tiering) — those systems
characterize polytime; EAL's coarser stratification characterizes elementary
time. Complexity-class control = choice of modal discipline × recursion
primitives, with the language design otherwise unchanged.

**Possible.hs, reborn.** The current compiler's recursion-sizing pass — an
abstract interpretation that *searches* for a sufficient church-numeral bound,
costing ~60 of tictactoe's 62 seconds — becomes **certified budget
inference**: the fuel for elaborated recursion is computed by the cost
interpretation itself (a structural, homomorphic fold over the syntax — no
search, no runtime probing), and the adequacy theorem is the certificate that
the computed budget suffices. The `agda` branch's `runFromSyntax` already
demonstrates the full pipeline **[proved]**; what changes is that level
assignment rides along with the same pass.

## 8. Whole-program inference: nobody writes a box

The design decision (made explicitly for Telomare 2): **whole-program
inference, no depth ever appears in a signature.**

Surface programs are plain total functional code. Users duplicate values
freely in the syntax and never see `!`, `dup`, `box`, or a level. The
compiler places boxes by inference. The known recipe **[cited:
Coppola–Martini; Coppola–Ronchi della Rocca; for the polytime-from-System-F
variant, Atassi–Baillot–Terui]**:

1. compute the simple-type skeleton of the program;
2. introduce an integer unknown for the number of boxes wrapping each subterm
   edge (constrained ≥ 0 — a negative would be a dereliction/digging);
3. generate linear constraints from (a) modal-depth matching at every
   application and (b) every multiply-used variable sitting under enough
   boxes to license its contraction;
4. EAL-typability = solvability; a solution *is* the level annotation handed
   to the Tier-1 runtime.

Contraction grouping makes the general problem disjunctive (ILP rather than
LP). **Telomare dodges most of that blowup**: iteration — the only way
duplication-hungry computation enters a program — arrives exclusively through
compiler-owned constructs (`iter`/`fold`/`while`; today, everything already
funnels through `repeatFunctionS` **[measured fact about the current
compiler]**). So box-introduction sites are few and structured, and inference
degenerates from "solve constraints over an arbitrary term" toward "assign
levels to the recursion constructs."

**The one honest leak.** Not every terminating program is EAL-typable. The
fragment is elementary-time *complete* extensionally (every elementary
function has some EAL program) but rejects natural-feeling programs whose
duplication structure isn't stratifiable — canonically, iterating at the level
you were built at. When inference fails, the error must be phrased in a
concept the surface language owns — **iteration levels** — never in terms of
boxes or linearity the user was promised they could ignore:

> "this iteration's step function is itself built by iteration at the same
> level; hoist it (compute it once, outside) or raise the level (accept one
> more tower story)"

This is the Rust-borrow-checker dynamic, managed deliberately: most users,
most of the time, think about nothing; the repair vocabulary when they must
think is a rule about *iteration nesting* — a concept Telomare users already
have, and arguably the same "bounded recursion" worldview restated.

Whole-program inference kills separate compilation (accepted consequence; a
library ecosystem would need depth polymorphism — indexed-type machinery
explicitly deferred to Open Questions).

## 9. The resource algebra

Resource functors form a 2×2 of (sequential-composition, parallel-composition)
monoids on ℕ — the `agda` branch's family **[proved]** — plus the new one:

| functor | ∘ combines | ⊗/fork combines | reading |
|---|---|---|---|
| work `⟦_⟧C` | + | + | total steps (= tel) |
| span `⟦_⟧WS` | + | ⊔ | parallel critical path |
| space `⟦_⟧SP` | ⊔ | + | stages reuse memory; parallel branches are simultaneously live |
| footprint | ⊔ | ⊔ | (not yet instantiated) |
| **dup `⟦_⟧D`** | + | + | **sizeT-weighted copies: `Σ (copies−1)·size(value)`** |

`⟦_⟧D` is zero on every constructor except `dup` (charges `size(value)`) and
`dupNat` (charges 1) — affine code has dup-grade 0 *by construction*. This is
the functor whose absence the `bend-port` experiments exposed: tictactoe's
blowup was invisible to work/span/space and entirely a dup-grade phenomenon.
Combined with the measured **45 interactions/tel** coefficient on dup-free
programs **[measured, `agda:BENCHMARK.md`]**, work + dup grade gives a
concrete wall-clock predictor for the net backend.

Two cost reports the compiler can print per program, both statically:

- **exact grades** per input (work/span/space/dup, computed by the functors);
- **tower height** = box depth: "worst case is a height-3 tower in the size of
  the level-0 data" — coarse, but honest, and in the spirit of telomare
  telling you your recursion budget.

Adequacy is proved per resource functor via the precision-with-slack pattern
(**[proved]** for work on both formalizations; stated for the others).

## 10. Backends and tiers

**Tier 1 — level-annotated sharing graphs** (EAL-typable programs, i.e. the
inference succeeded): fans carry their static level; pairing is integer
comparison; reduction is oracle-free and Lévy-optimal; strong confluence makes
the interaction count strategy-independent, so the work grade is *the* cost.
This is the disciplined fragment of the interaction-net world — with semantics
pinned to the core's denotation rather than HVM-style superposition. The
`bend-port` failure modes become impossible by construction: tictactoe's
multiply-read `newBoard` is, in this design, either an inferred `dup` on a
boxed value (priced by `⟦_⟧D`, shared correctly by the level-annotated fan) or
a Tier-assignment story — never a silent 10⁴× recompute.

**Tier 2 — metered graph reduction** (total but unstratifiable programs): the
definitional interpreter with tel metering. Measured on the `agda` branch at a
flat ~240–248 ns/tel **[measured, `agda:BENCHMARK.md`]** — tel is physical.

**Tier assignment is loud.** EAL-typability is an optimization property the
compiler *reports*, not a wall the user hits: programs never get rejected for
failing stratification, they get the slower backend and a message naming the
iteration-level conflict. The known risk is performance cliffs (a
semantically-identical refactor silently dropping off Tier 1), managed the way
GHC users watch fusion: the tier and the reason are always in the build
output.

## 11. Effects and totality

Unchanged from telomare's stance, now stated denotationally: a program *is* a
pure transcript function `list input ⇨ output`; interactivity is replaying a
longer input list (this is exactly how the current HVM driver works —
input-independent stage-1 compile, inputs appended at stage 2). Failure/abort
is a coproduct (`A ⊕ error`), priced like everything else. There is no
partiality anywhere in the model: `⟦_⟧V` is total, `⟦_⟧K`'s `Maybe` is *fuel
exhaustion* (impossible under adequacy — that's the theorem), not
nontermination.

## 12. Migration appendix (how the old core maps)

Not a compatibility requirement — a sanity check that nothing expressible is
lost.

| current core | Telomare 2 |
|---|---|
| `Zero`, `Pair` | `unit`/`nat`/`⊗` data (plus native `nat` leaves, validated by the `TV/N` measurement) |
| `Gate` | `case ∘ natOut` (the `agda` branch's tictactoe does exactly this) |
| `PLeft`, `PRight` | `exl`, `exr` (affine projections) |
| `Defer` + `SetEnv` closures | `box` + application: the closure discipline *is* the box discipline — a `Defer`red body whose env is supplied later is a package promoted to be consumed one level in |
| church-numeral recursion via `repeatFunctionS` | `iter` (fuel as data; the `tvRepeat`/`tvFix` optimizations are the operational shadow of this being the primitive) |
| `Possible.hs` sizing | budget = cost-functor output; levels = the same pass (§7) |
| `Abort` | `⊕` error coproduct |

## 13. Validation exercise — DONE, bet confirmed (see `design/VALIDATION.md`)

Executed 2026-07-12. Hand EAL decorations of `d2c`/`map`/`foldr`, `whoWon`
(nested-foldr), `dPow` (tower), `minus` (compound scrutinee), and `pow`
(church exponentiation) were compared against the limits Possible.hs actually
infers (read from `--emit-hvm`'s `churchK` table, no compiler changes).
Result: **on the `{t,r,b}` fragment — all telomare recursion — box-nesting
order = the sizer's evaluation-dependency order in every case** [measured].
Sharpest instance: `dPow`'s inner token is sized to the max over all outer
iterations, which is Girard's level-by-level bound argument running inside
the current compiler. whoWon's k-groups {8-bound}{3-bound}{1-bound} partition
exactly along the hand-derived strata, and the decoration forces `board : !!`
— statically finding the value whose duplication killed the bend-port run.
One scope divergence: `pow` on church literals has no tokens (invisible to
sizing) while EAL still assigns levels — confined to church-literal
arithmetic, handled by tiering, and folded back into the agreeing fragment by
Telomare 2's `iterS` elaboration. Full method, tables, decorations, and
threats-to-validity: `design/VALIDATION.md`.

The structural box-placement pass is now **prototyped**:
`telomare --emit-levels` (`src/Telomare/Levels.hs`) reproduces the hand
decorations with no evaluation and no search, and handles full
`tictactoe.tel` in 37 ms — statically reporting `main.newBoard : !` and
`whoWon.board : !!`, the bend-port blowup bindings. `VALIDATION.md` §8.

## 14. Open questions

1. **Exact typing of `iter`/`fold` at the boundary.** `iter`'s seed and result
   are boxed; should the fuel `nat` also be one level down? `fold` consumes
   list elements from the orchestration level inside a body that runs one
   level deeper — the skeleton takes the pragmatic typing and flags it; the
   faithful answer probably stratifies the *list* type itself.
2. **Where the depth index lives**: on `Ty` (`!` as a type constructor, depths
   implicit in nesting — the skeleton's choice) vs on the judgment
   (`A ⇨ⁿ B`). The judgment-indexed form makes the stratification condition
   local but infects every rule.
3. **Footprint functor** (⊔,⊔) — instantiate when a batch/streaming story
   needs it.
4. **Depth polymorphism** — only if a library ecosystem (separate compilation)
   ever outweighs the simplicity of whole-program inference.
5. **Surface syntax** — how convenience recursion (`let rec` with a
   termination-visible argument) elaborates to `iter`/`fold`/`while`; what the
   iteration-level error looks like verbatim.
6. **Intensional layer** — tree-calculus-style program inspection as a
   *stratum* (programs at level n analyzing programs at level n+1) rather than
   a foundation; speculative.

## 15. Sources

- Girard, *Light Linear Logic* (origin of ELL/LLL).
- Danos–Joinet, *Linear Logic and Elementary Time* (the clean EAL/ELL story).
- Asperti–Roversi, *Intuitionistic Light Affine Logic* (the PL treatment).
- Coppola–Martini; Coppola–Ronchi della Rocca — EAL type inference / box
  placement as linear constraints; oracle-free-reduction criterion.
- Atassi–Baillot–Terui — DLAL inference from System F, polytime.
- Asperti–Guerrini, *The Optimal Implementation of Functional Programming
  Languages* (the whole Lamping/oracle landscape); Asperti–Mairson (the
  oracle's own cost).
- Lafont, *Interaction Combinators* (strong confluence).
- Elliott — *Denotational Design with Type Class Morphisms*; *Compiling to
  Categories* (ICFP 2017); *Timely Computation*. (Local copies:
  `~/src/conal-elliott/`.)
- Taelin, *Elementary-Affine-Core* (`agda/Linear.agda`: usage-tracked affine
  contexts in Agda) — the lineage that leads to HVM.
- This repository: `agda` branch (`telomare.agda`, `README-Agda.md`,
  `BENCHMARK.md`, `PROGRESS.md`); `bend-port` branch
  (`bend/HYBRID_PROGRESS.md`, `bend/PORT.md`, `CHANGELOG.md`).

## 16. Appendix: a denotational critique of the box

Reading the design against Elliott's own standards, honestly.

**What the methodology commends.** (a) The discipline is *inherited, not
invented*: deleting dereliction/digging buys forty years of metatheory
(elementary bounds, oracle-freedom) the way a monad instance buys its laws.
(b) `⟦!A⟧ = ⟦A⟧` — the value semantics cannot observe boxes; the modality is
a TCM-invisible annotation, so no abstraction leak into meaning. (c) One
invariant, two theorems is exactly the economy Denotational Design prizes.
(d) Resource functors out of one syntax = Compiling to Categories used as
intended.

**What the methodology finds lacking — recorded as design debts:**

1. **`!` has no denotation of its own.** Its meaning is *permission* (what
   the machine may do), not *value* — an operational rider on the semantics.
   Girard's own coherence-space semantics gives `!A` a real denotation (the
   cofree-comonoid / finite-multiset construction); this design does not.
   Debt: find the semantic model in which `!` is a homomorphism target
   (values-with-copying-structure, or duplication priced in the grading with
   `!` as an adjoint to forgetting it).
2. **Box placement has an algorithm but no universal property.** Whole-
   program inference should be *specified* denotationally — a Galois
   connection between the cartesian surface and the affine core, with
   placement as "the least boxing such that the program is stratified" — and
   the Coppola-style solver proved against that spec, not taken as the
   definition. (The structural pass of `design/VALIDATION.md` §8 is evidence
   the least solution is computable by construction on the `{t,s,b}`
   fragment.)
3. **Grades are machine-anchored.** The 45-ITRS/tel coefficient is
   empirical; the cost algebra should be machine-independent with the net
   backend as one homomorphic image (Timely-Computation style), the exact
   per-input grade and the coarse tower-height both quotients of one cost
   object — and observed paddings (sizing's +2) *derived*, not measured.
4. **The discipline is intensional; the semantics is not.** `λn. n n`
   denotes a perfectly total function; EAL rejects it for operational
   reasons. Excluding a semantically meaningful program would be a category
   error — which is why Tier 2 (deoptimize, never reject) is not a
   convenience but a semantic-fidelity requirement of this design.
