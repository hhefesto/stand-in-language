# R2 Data Promotion — `PromoteS` (M4 design)

## The rule

```
promoteS : Ground A → A ⇨ ! A
```

`Ground` is bang-free, arrow-free first-order data: `unit`, `nat`, and
products/sums/lists of Ground. It is deliberately **not** `Copyable`:
`Copyable (! A)` exists (dupS's license), and a promote at `! A` would be
`dig : !A ⇨ !!A` — exactly the operator whose absence fixes box depth
before reduction (T3.Core.Syntax header). Ground rules `!` out
structurally, so no dig arises by composition.

## Why it is sound now (and was not at R1)

The Syntax.agda objection to `A ⇨ !A` was that `dupS ∘ promote` would
copy an unboxed open input **without pricing it as data**. Since R3,
every duplication of first-order data is priced: `dupS` at `! A` follows
promotion of a *data* value, and each later `dupS`/`copyS` charges full
`sizeT` in the dup grade. Nothing is smuggled: the charge stays at the
duplication sites, the promote itself is free.

- work 0, dup 0, space `sz` (input live through the no-op).
- `depth (promoteS g) = 0`: promotion wraps a runtime **value**, not a
  code region (`⟦!A⟧T = ⟦A⟧T`); no code runs a level deeper, so
  `towerHeight` is untouched. Contrast `boxS`/`boxValS`, which wrap code
  and stay `suc`.

## What it unblocks (R2)

The elaborator's `requirePromotable` (loop seeds must be closed) relaxes:
an **open** seed whose type is Ground elaborates in context to `A`, then
`promoteS` lifts it to `! A` at the loop boundary — fold/iterate/while
with runtime-computed seeds, `multiplyNat`, and the deferred Prelude
`dTimes`/`dMinus` (design/PRELUDE_MIGRATION.md). Residual live context
after the loop keeps its existing restriction (unchanged in M4).

## Cross-stack checklist

- Agda: `Ground` predicate (T3.Core.Ty), `promoteS` constructor + depth
  (T3.Core.Syntax), `⟦_⟧V` identity, `⟦_⟧G` (charge-free leaf),
  `⟦_⟧K` (Exec), Adequacy case, Abstract transfer (`s ↦ bangS s`),
  Bound `costW`/`costD` cases + soundness (`(just 0 , bangS s)`;
  `γW (bangS s) = γW s` definitionally), SpaceBound `spaceS`
  (`(sizeS s , bangS s)`) + soundness, Everything untouched.
- Haskell: `Ground` witness + `PromoteS` in Core, `evalV`/`evalG`/`evalK`
  cases in Denotation, `evalSp` in Space, `costW`/`costD`/`costSp` in
  Budget, Ops if it enumerates constructors, Transport **v5** with an
  `NPromote` node, Compiler/Closed open-seed routing, Tel2
  `requirePromotable` relaxation + `groundOf :: SUTy a -> Maybe (Ground …)`.
- Tests: transport round-trip at v5, open-seed accept/behavior vectors
  (`multiplyNat`), dup-pricing vector (promoted seed duplicated in a loop
  charges at the dup site), rejection vectors stay for closure seeds.

## Open seeds in the elaborator (the bulk)

`compileAffineLoop`/`compileClosedLoop` currently `elaborateClosed` the
seed at `A` and route through `Compiler/Closed.hs` templates expecting a
`Morph 'Unit ('Bang …)` seed. With `PromoteS` the seed can be produced
from the live context: elaborate seed at `A` in-context, compose
`PromoteS` to get `! A`, and use the `(nat ⊗ ! A) ⇨ ! A`-shaped cores
(`IterS`/`FoldS`/`WhileS`) directly — the closed-seed templates remain
for the closed case (no behavior change, goldens stable).
