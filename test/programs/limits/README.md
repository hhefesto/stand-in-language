# tel2 limits — worked examples

Small tel2 programs that each hit **one boundary** of the language, so the
edges are concrete rather than abstract. Seven of them are *meant to fail to
compile* — the rejection is the lesson. Each file's header records the exact
message the compiler prints today, and the idiomatic workaround sits commented
out right next to the offending code. The eighth compiles and runs but shows a
*degraded certificate*.

These are exploratory. They are **not** wired into the test suite (the cabal
`test/programs/*.tel2` glob is single-level and does not reach this
subdirectory), so nothing here runs during `cabal test`.

## Running one

```sh
cabal run -v0 telomare -- test/programs/limits/<file>.tel2
# the certificate example also takes --certificate:
cabal run -v0 telomare -- test/programs/limits/recursion-triple-unbounded.tel2 --certificate
```

## The eight limits

| File | Limit | Outcome (today) |
|------|-------|-----------------|
| `no-general-recursion.tel2` | tel2 is total: no `fix`, and a definition may not call itself | **rejected** — `cyclic definitions: …` |
| `fuel-not-measurable.tel2` | the `{ test, rec, last }` triple needs fuel calculable from a **nat** measure; a `List` has none | **rejected** — `cannot calculate recursion fuel: … use fold/map for list recursion` |
| `closure-used-twice.tel2` | closures are affine — applied at most once, never copied (no dereliction) | **rejected** — `function f cannot be implicitly copied; a closure is applied at most once` |
| `no-dereliction-wall.tel2` | no `!a -> a`: an unboxed value cannot stay live across a loop | **rejected** — `unboxed context cannot remain live after recursion` |
| `no-polymorphism.tel2` | monomorphic: no type variables, no generics | **rejected** — `unknown type a` |
| `no-recursive-adt.tel2` | `data` = nullary enums only; constructors carry no payload | **rejected** — parse error at the payload field |
| `impoverished-primitives.tel2` | Nat has only `succ`/`add` (no `*`,`-`,`/`,`<`,`==`); Text has only literal-prefix `prepend` | **rejected** — `unknown variable mul` / `unknown variable prepend` |
| `recursion-triple-unbounded.tel2` | the triple is total but its **certified** work/space bound is `unbounded`, unlike `iterate`/`fold`/`while` | **compiles & runs**, but `--certificate` prints `unbounded` |

## Other sharp edges (no separate program)

- **Data reuse is not a limit** — reusing a first-order value is allowed; each
  extra use is a silently-priced copy (`copy` just makes the price explicit).
  The affine wall is closures only (see `closure-used-twice.tel2`).
- **`matchNat`'s default binds the value, not the predecessor.**
  `case n of { 0 -> …; k -> … }` binds `k = n`. For `n-1`, use the structural
  deconstructor `case n of { 0 -> …; succ k -> … }`.
- **Nested / dependent loops are rejected**, and a loop's bound, seed, and
  input must be closed (`… cannot capture or contain recursion`).
- **Enums erase to `Nat`**, so a `Bool` and a `Nat` are not kept nominally
  distinct after elaboration.
- **Imports share one unqualified namespace** — no qualified or selective
  imports.
