# The Space Metric (M1 decision)

Decision (2026-07-21): the space metric is **live-heap peak** — the maximum,
over the machine's left-to-right evaluation order (`evalK`), of the total size
in words of every value that is still live. Retention is explicit: whatever a
later stage will still consume counts while an earlier stage runs. This is the
only metric that is honestly a *memory bound*: allocate `spc f` words at the
input and the run cannot exhaust them.

The previously shipped `spaceAlg` (a `CostAlgebra` instance with
`_⋄_ = _⊔_`) measured streaming/local peak — the largest single leaf
transition — and was deleted with this decision. It was not advertised
anywhere and had no Haskell mirror.

## Normative definition of `spc`

Sizes are `sizeVal`/`sizeG` words. For `f : A ⇨ B` run on input `a`:

- **Leaves** (`idS`, `swapS`, `consS`, `natOutS`, …): `sz_in ⊔ sz_out`.
  Input and output of a primitive are not co-live beyond the transition.
- **Sequential composition** `g ∘ f`: `spc f a ⊔ spc g (f a)`.
  Stages reuse memory; the intermediate value is counted inside both operands'
  own peaks.
- **Tensor** `f ⊗ g` on `(a , b)`: `(sz b + spc f a) ⊔ (sz (f a) + spc g b)`.
  While `f` runs, the sibling `b` is retained; while `g` runs, `f`'s result
  is retained. This is where retention first appears.
- **Case** `case f g`: the branch taken, plus nothing — the scrutinee has
  already been consumed into the branch input.
- **Loops** (`mapS`, `iterS`, `foldS`, `whileS`, and the closure forms):
  per round, the un-consumed remainder is live alongside the body:
  - `mapS f`, round `i`: `sz tail_i + sz produced-prefix_i + spc f x_i`.
  - `foldS f`: `sz tail_i + spc f (acc_i , x_i)` — the tail is retained
    while the body folds.
  - `iterS`/`whileS`: `spc body acc_i` (plus the probe's read for `whileS`);
    the counter is a word.
- **Closures**: one word (the `sizeT`/`sizeVal` pointer model). The
  environment's words surface when the body runs: `applyS` charges the
  body's peak on `env ⊗ arg`, which is at least `sz env + sz arg`. The
  sit-in-heap undercount between creation and application is the same one
  documented for the dup grade in `T3.Core.Ty`.
- **Boxes**: weightless and transparent (`sizeT (! A) = sizeT A`); running
  boxed code charges the same space as running it unboxed.

Peak, not sum: `spc` is a maximum over the trace, so bounds compose with
`⊔` along sequence and `+` only across genuinely co-live siblings.

## Why the `CostAlgebra`/`Interp` abstraction cannot express this

`CostAlgebra` (spec/T3/Sem/Graded.agda) gives an instance exactly these
signals: `chargePrim : (A B : Ty) → PrimTag → ℕ → ℕ → ℳ` (leaf input/output
sizes only), `_⋄_ : ℳ → ℳ → ℳ` (combines *grades*, with no access to the
value flowing between the stages), `chargeStep`, `chargeBase`, `chargeProbe`.
Retention needs precisely what these are not given: the sizes of values that
are *not* participating in the current transition. `Interp.foldG` and
`Interp.mapG` recurse without ever passing the retained tail (or the
produced prefix) to the algebra, and the tensor case combines the two sides'
grades with `_∥_` without the sibling sizes. No instance of the record can
see them; this is structural, not a matter of picking better constants.

### The counter-example that killed `spaceAlg`

`mapS sucS` over an `n`-element list of naturals: true live heap while
processing element `i` is about `(n − i) + i` list cells plus the body's
constant — Θ(n). `spaceAlg` computed `⨆_i (sz x_i ⊔ sz (suc x_i)) ⊔
chargeBase`, a constant in `n` (the largest single element transition).
Any `⋄ = ⊔`-style algebra under-counts every program whose container
outlives the per-element step — i.e. every loop. The same shape breaks
`foldS`: the un-consumed tail is live through every round and no leaf
transition ever mentions it.

## Consequences (M2 shape)

- **Agda**: a dedicated sized interpreter, new `spec/T3/Sem/Space.agda`
  (`SVal` with sized closures, `⟦_⟧S` returning `peak × result`, coherence
  with `⟦_⟧V`), plus `spec/T3/SpaceBound.agda`: static `spaceS` over
  `Shape`s mirroring `costW`'s structure (composition `⊔∞`, tensor adds the
  sibling's `sizeS` bound, loops add the full container bound per round),
  and `spaceS-sound` via a Kripke relation `γS` mirroring `γW`.
  `Graded.agda` and `Adequacy.agda` stay untouched.
- **Haskell**: no singleton threading — an untyped sized-value meter
  (`src/Telomare/Space.hs`: `DVal`, `dSize`, `toDVal`, `evalSp`) mirrors
  `⟦_⟧S`; the static `spaceS` mirror lives in `Budget.hs` and reaches
  `--certificate`/`--meter` through `Machine.hs`.
- **Shift-equivariance**: every charge in the dedicated interpreter is
  `retained + local`; adding residual context to the live set adds the same
  constant to every round's charge, so bounds proved for the loop body in
  isolation lift to any placement — no live-parameter threading is needed
  in the static analysis.
- v1 keeps `Shape` unchanged: `lollyS` carries only the closure's peak
  bound, so `mapCS`'s retained output prefix is bounded through `topS`
  element sizes — finite only at atomic element types.
- **Haskell static mirror is type-blind** (`sizeSH TopS = unbounded`): the
  typed Agda `sizeS` resolves atomic `topS` to one word, but `costSp`
  cannot thread singletons through composite morphisms, so every `TopS`
  reached in a shape makes the Haskell bound unbounded. In particular
  list shapes built from `NilS` carry `TopS` elements, so today's
  certificate prints `static space bound: … unbounded` for entries that
  touch lists. The fix (an M3-era refinement alongside `--assume-shape`)
  is a partial type representation (`TyR`) threaded through `costSp` so
  atomic tops size to one word. The measured meter (`--meter`'s
  `core peak space`) is exact today regardless.
