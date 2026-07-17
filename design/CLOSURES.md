# Tel2 Resource Pivot and First-Class Closures

Status: design accepted; staged implementation in progress.

## The pivot

The project goal is **bounded time and memory**. Affinity and EAL are tools
toward that goal, not commitments. Two consequences:

1. **Duplication of first-order data is legal wherever it is priced.**
   Implicit in source: reusing a copyable variable inserts a costed copy,
   charged its full `sizeVal`/`sizeT` in the duplication grade. Nothing is
   ever duplicated for free; nothing data-shaped is rejected for reuse.
2. **The EAL modality gates the reuse of code, not data.** A closure is
   suspended computation; duplicating it multiplies future work. Closures
   are therefore *not* copyable — reuse of a closure exists only behind
   `Bang`, formed by empty-context promotion, duplicated only by `DupS`,
   applied one box level deeper. This is where `Bang` earns its keep.

## R1 — costed data copy

New core primitive (Agda `copyS`, Haskell `CopyS`):

```text
copyS : Copyable A → A ⇨ (A ⊗ A)
```

`Copyable` moves to the type layer and becomes total on first-order data:
`unit`, `nat`, products, sums, lists (of copyable), `! A`. It stays
evidence-indexed because arrows will have **no witness, ever**.

Charges: work 0, fuel 0, dup `sizeT A a`, depth 0. Erases to `dupU`; tip
skeleton; shape transfer `s ↦ (s, s)`. The elaborator realizes implicit
reuse by demand threading (see `T3.Source.Affine`'s `both` split rule):
a copyable binding may be sent to both subexpressions, priced per use.

## First-class closures (FC stages)

### Types and constructors

```text
Lolly a b                 -- A ⊸ B, affine: applied at most once
CurryS :: STy c -> Morph (c :*: a) b -> Morph c (Lolly a b)
ApplyS :: Morph (Lolly a b :*: a) b
MapCS  :: Morph (Bang (Lolly a b) :*: ListT a) (Bang (ListT b))
```

Haskell closure values are **structural** (HANDOFF Phase 13): an
existential `Closure (STy c) (Morph (c :*: a) b) (Val c)` — code identity
plus typed environment. Never opaque Haskell functions. Agda takes the
semantic denotation `⟦ A ⊸ B ⟧T = ⟦A⟧T → ⟦B⟧T` (totality definitional
under --safe); the Haskell `Closure` is its defunctionalization, agreement
re-checked pointwise by tests.

### Reuse rule

- Bare `Lolly a b`: affine. Apply consumes it; discard is free; copying is
  a type error (`Copyable` has no arrow case).
- Reusable closure = `Bang (Lolly a b)`, formed **only** by the existing
  `BoxValS` empty-context promotion of a *closed* closure. Runtime
  selection = `CaseS` over branches each ending in a promoted closed
  closure. Application of a boxed closure happens one level down
  (`BoxS ApplyS`, or `MapCS` per element). No new modal primitives; the
  no-general-`A ⇨ !A` discovery is restated for code and kept.

### Cost table

| construct | work | dup | fuel | depth |
| --- | --- | --- | --- | --- |
| `CurryS` | 0 | 0 | 0 | depth of body |
| `ApplyS` | 1 + body | body | step + body | 0 |
| `MapCS` | per element: 1 + body | per element: body | mapK shape | 1 |
| `DupS` at `Bang(Lolly)` | 0 | 1 | 0 | 0 |
| `sizeVal (Lolly)` | — | 1 (pointer model) | — | — |

Pointer model rationale: only *closed* closures can be duplicated, and a
closed closure duplicate is one code pointer — exact where duplication is
possible, documented undercount for linear-closure probes (revisit at R3).

### Machine boundary

`Lolly` is excluded from machine `State`/`Reply` this milestone
(first-order witness in `toLift`; compile error otherwise). Structural
closure equality (`styEq` + transport-node equality + env equality) serves
the evaluator-agreement checks.

### Self-application and bounds

`\x -> x x` is untypable by monomorphism (occurs check; also enforced on
transport artifacts). Totality is preserved: recursion stays fuel-is-data;
the monomorphic λ-fragment is strongly normalizing. Exact per-run grades
flow through closures (apply charges the dynamic body cost). Still absent
(unchanged, acknowledged): a machine-checked *a priori* bound theorem —
that is milestone R3 (static budget ≥ actual work/space, on the
`Abstract.agda` Shape/transfer machinery, which never mentions `Bang`).

## Stages

0. This document.
1. **R1a** Agda costed copy (copyS, Copyable sums/lists, `both` split).
2. **R1b** Haskell mirror + transport v3 (`NCopy`).
3. **R1c** elaborator implicit copy (demand threading); ttt/stdlib cleanup.
4. **FC1** Agda closure calculus (Lolly, curry/apply/mapC; relational
   G-val/adequacy/ε-factor with first-order corollaries — the long pole).
5. **FC2** Haskell mirror (Core/Denotation/Surface/Direct/Machine).
6. **FC3** transport v4 (`TLolly`, `NCurry`/`NApply`/`NMapC`).
7. **FC4** Tel2 source: `-o` types, lambdas, `apply(f, x)`.
8. **FC5** `mapc` runtime-mapper placement template + demo.
9. **FC6** docs (README/STORY/HANDOFF, this file finalized).

Deferred: R2 open/copyable seeds (`PromoteS`, multiplication, tic-tac-toe
fold retained-state), R3 bounds theorem, `FoldCS`/`IterCS`/`WhileCS`.

Frozen throughout: historical `.tel`, `src/Telomare/Compat/`, no Bend, no
game-specific compiler behavior; golden `tel2_ttt_*` transcripts stay
byte-identical.
