# Historical Prelude Migration Ledger

This ledger covers every top-level name bound by `test/programs/Prelude.tel`.
It describes migration status, not semantic proof. The old file is untyped,
higher-order, Church-encoded compatibility source; `.tel2` is monomorphic,
first-order, affine source over primitive `Nat` and finite nullary data.

Statuses mean:

- **exact**: same useful interface and behavior is available.
- **modernized**: mathematical behavior is retained with the modern data model
  or tuple calling convention.
- **specialized**: only an explicitly monomorphic instance is supplied.
- **shim**: a deliberately limited compatibility wrapper exists.
- **obsolete**: the old encoding bridge or workaround has no modern role.
- **deferred**: sound core support may exist, but source syntax or placement is
  not implemented.
- **impossible**: the behavior conflicts with the current total/first-order
  language rather than merely awaiting implementation.

No historical binding currently qualifies as exact or shim: currying,
polymorphism, and the old Nat/list representations changed every implementable
interface. `stdlib/LegacyPrelude.tel2` contains only the six rows that explicitly
name a current compatibility definition.

| Historical binding | Status | Current definition / rationale |
| --- | --- | --- |
| `id` | specialized | `LegacyPrelude.id : Nat -> Nat`; general polymorphic identity is unavailable. |
| `and` | modernized | `LegacyPrelude.and : Bool * Bool -> Bool`; canonical finite Bool and tuple argument. |
| `or` | modernized | `LegacyPrelude.or : Bool * Bool -> Bool`. |
| `not` | modernized | `LegacyPrelude.not : Bool -> Bool`. |
| `succ` | modernized | `LegacyPrelude.succ : Nat -> Nat`, implemented by `suc`/`SucS` rather than pair encoding. |
| `d2c` | obsolete | Primitive `Nat` is canonical; conversion to a higher-order Church numeral is neither needed nor representable. |
| `c2d` | obsolete | Primitive `Nat` replaces the Church/data conversion boundary. |
| `dPlus` | modernized | `LegacyPrelude.dPlus : Nat * Nat -> Nat`, implemented by `add`/`AddS`. |
| `plus` | obsolete | Church-numeral composition is higher-order; use `natAdd`. |
| `dTimes` | deferred | Needs multiplication primitive or sound dynamic iteration/placement. |
| `times` | obsolete | Church multiplication is higher-order. |
| `dPow` | deferred | Needs multiplication plus sound dynamic/nested iteration. |
| `pow` | obsolete | Church exponentiation is higher-order. |
| `dMinus` | deferred | Total truncated subtraction needs dynamic iteration or a primitive core morphism. |
| `minus` | obsolete | Church-facing subtraction wrapper has no modern interface. |
| `range` | deferred | Requires source list construction and dynamic recursion. |
| `map` | impossible | The historical general combinator requires higher-order values and polymorphism. Specialized maps may be added separately. |
| `foldr` | deferred | Closed whole-entry `FoldS` is available, but the historical reusable higher-order polymorphic API is not. |
| `foldl` | deferred | Requires a separately checked fold orientation and a reusable first-order interface. |
| `zipWith` | deferred | Requires synchronized list recursion and a specialized first-order operator interface. |
| `filter` | deferred | Requires list fold/recursion and an explicit first-order predicate interface. |
| `dEqual` | deferred | General Nat equality needs dynamic structural recursion or a primitive. |
| `dDiv` | deferred | Requires comparison, subtraction, dynamic recursion, and an explicit total zero-divisor result. |
| `listLength` | modernized | `Prelude.listLength : List Nat -> Nat`; reusable first-order `FoldS` placement over an affine runtime list. |
| `listEqual` | deferred | Requires list recursion and Nat equality. |
| `listPlus` | deferred | Needs a reusable fold over an open list argument; closed entry folding is insufficient. |
| `flip` | impossible | General function arguments and returned functions are outside first-order `.tel2`. |
| `con` | impossible | General function composition is higher-order. |
| `concat` | deferred | Needs nested-list syntax and reusable/dependent fold placement beyond independent closed entry folding. |
| `drop` | deferred | Needs modern Nat-bounded list recursion; the historical Church interface is obsolete. |
| `take` | deferred | Needs modern Nat-bounded list recursion. |
| `factorial` | deferred | Requires range/fold/multiplication and corresponding placement. |
| `dFactorial` | deferred | A modern Nat result is plausible after factorial support; the Church adapter is obsolete. |
| `quicksort` | deferred | Requires general structural list recursion, partitioning, and explicit duplication analysis. |
| `abort` | impossible | The total core has no bottom, exception, or unchecked abort morphism. Use an explicit sum in a future API. |
| `assert` | impossible | Historical failure uses `abort`; a modern assertion must return an explicit typed result and is not an alias. |
| `truncate` | deferred | Requires a checked bounded structural recursion form. |
| `min` | deferred | Requires total Nat comparison. |
| `max` | deferred | Requires total Nat comparison. |
| `fakeRecur` | obsolete | It is specifically a recursion workaround; `.tel2` will not preserve fake recursion. |
| `dMod` | deferred | Requires total division and multiplication/subtraction. |
| `gcd` | deferred | Requires modulo and sound dynamic while/iteration placement. |
| `lcm` | deferred | Requires multiplication, gcd, and total division. |
| `Rational` | deferred | A product alias is easy, but the historical normalized constructor requires gcd/division and explicit zero-denominator handling. |
| `fromRational` | deferred | Depends on the normalized Rational constructor. |
| `toRational` | deferred | Historical bundle semantics are ambiguous and depend on the unavailable normalized representation. |
| `rPlus` | deferred | Requires normalized Rational construction, multiplication, and addition. |
| `rTimes` | deferred | Requires normalized Rational construction and multiplication. |
| `rMinus` | deferred | Requires normalized Rational construction, multiplication, and subtraction. |
| `rDiv` | deferred | Requires normalized Rational construction, multiplication, and explicit zero handling. |
