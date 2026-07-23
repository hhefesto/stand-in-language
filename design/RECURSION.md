# Bounded recursion: the `{test, rec, last}` triple (`RecS`)

Telomare0's recursion-triple notation `{ test, rec, last }` is being brought
to tel2 as a **bounded, certified** primitive. This document records the core
primitive (RT1); the surface notation (RT2) and the sizing pass that makes the
fuel invisible (RT3) build on it.

## The primitive

```
recS : STy a → STy b
     → (a ⇨ (unit ⊕ unit))        -- test:  inj₁ stops, inj₂ recurses (probes the input)
     → ((a ⊸ b) ⊗ a) ⇨ b          -- rec: gets recur : a ⊸ b (used ≤ once) and the input
     → (a ⇨ b)                     -- last: finalizer on the stopped/base value
     → (nat ⊗ a) ⇨ b               -- fuel ⊗ input → result
```

Semantics, structural on the fuel `n`:

```
recV 0       x = last x
recV (suc n) x = case test x of
                   inj₁ _ → last x                         -- test says stop
                   inj₂ _ → rec (recur , x)                -- recur = recV n (one fuel lower)
```

The `test` probes the input without consuming it (an implicit copy, priced
like `whileS`/`guardS`). Totality is manifest: `recV` recurses only on the
fuel, so it terminates even if `test` never stops.

## Why unboxed and linear

tel2's core has no dereliction (`! A ⇨ A`) — its absence is what fixes box
depth. Two consequences shape `RecS`:

- **Unboxed** (`nat ⊗ a → b`, not the boxed `nat ⊗ ! a → ! b` of the other
  loops). The Haskell mirror defunctionalizes closures (`Val (a ⊸ b)` is a
  code pointer + environment, never a host function), so `recur` must be built
  as a real closure whose body *is* `RecS` with the decremented fuel in its
  environment. That only type-checks at `nat ⊗ a → b`; a boxed `! b` result
  would need `! b → b` — the missing dereliction — to build `recur`.
- **Linear** (`recur : a ⊸ b`, applied at most once per body). A reusable
  `recur : ! (a ⊸ b)` could not be applied without dereliction either.
  This covers `d2c`, `map`, `foldr`, `range` (all single-call). Multi-call
  bodies (`quicksort` calls `recur` twice) need the reusable form and are a
  **documented v1 gap**.

## What is certified (RT1)

The full stack — Agda `spec/T3/` and the Haskell mirror — carries `recS` with:

- value / graded / execution semantics (`Sem/Value`, `Sem/Graded`, `Sem/Exec`);
- **value coherence** (`G-val` via `recG-rel`): the graded semantics computes
  the specification value; the recursion is carried by the recur closure's
  relatedness at one fuel lower;
- **adequacy** (`precise` via `rec-prec`): running the fuel machine with the
  work-grade budget finishes with exactly the leftover fuel — the recursion is
  carried by the recur closure's *precision* at one fuel lower;
- erasure/placement (`Place`: `ε`, `ε-rel` via `rec-rel`, `skelOfCore`,
  `core-solves`) and abstract-shape soundness (`Abstract`);
- transport (v7, `NRec`).

## What is NOT bounded yet (v1)

`costW`, `costD`, and `costSp` all report `recS` **unbounded** (`nothing` /
`topS`), in both Agda and Haskell. This is honest: the per-round cost is finite
and structural (test + body, with the recur application counted as the next
round), so `fuel × round` *is* a sound finite bound — but proving it in Agda
needs a closure-cost-compositionality lemma (the body-chosen `recur` argument's
cost is the recursion itself), which `whileC-bound` does not. Rather than a
finite Haskell bound that the Agda cannot certify, RT1 keeps both unbounded and
defers the finite bound to **RT3**: once the sizing pass supplies a concrete
fuel `N`, the bound is provable by a concrete-fuel argument.

The `min(fuel, input)` example in `test/BoundVectors.hs` pins the behaviour
(full fuel, fuel-limited, base) and the unbounded cost; `test/TransportVectors.hs`
pins the v7 round-trip.
