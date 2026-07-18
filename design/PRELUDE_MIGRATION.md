# Historical Prelude Migration Ledger

This ledger covers every top-level name bound by `test/programs/Prelude.tel`.
It describes migration status, not semantic proof. The old file is untyped,
higher-order, Church-encoded compatibility source; `.tel2` is monomorphic,
affine source over primitive `Nat` and finite nullary data, with first-class
affine closures (`A -o B`, applied at most once; reusable closures exist only
as promoted closed lambdas, reached from source through `mapc`).

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
| `dTimes` | deferred | Runtime-bounded iteration exists, but multiplication still needs an affine state design that retains the multiplicand without promoting an open seed. |
| `times` | obsolete | Church multiplication is higher-order. |
| `dPow` | deferred | Needs multiplication plus sound dynamic/nested iteration. |
| `pow` | obsolete | Church exponentiation is higher-order. |
| `dMinus` | deferred | Runtime-bounded iteration exists, but truncated subtraction still needs predecessor/state support without promoting an open seed. |
| `minus` | obsolete | Church-facing subtraction wrapper has no modern interface. |
| `range` | deferred | Source list construction and runtime bounds exist, but range still needs affine state that carries an open endpoint/index through iteration. |
| `map` | specialized | Source `map input with mapper` is reusable, first-order, monomorphic, order-preserving, and backed by `MapS`; `Prelude.mapIncrement : List Nat -> List Nat` is concrete. `mapc input with mapper` additionally maps with a function value selected at runtime among closed lambdas (`MapCS`). The polymorphic interface remains unavailable. |
| `foldr` | specialized | `listLength` is an orientation-insensitive specialization. The current `FoldS` is a reusable named-step left fold, so historical right-associative higher-order `foldr` is not exposed. |
| `foldl` | specialized | Source `fold input from seed with step` is a reusable first-order left fold; `Prelude.listLength` and `Prelude.listSum` are concrete `List Nat` instances. Runtime function arguments and polymorphism remain unavailable. |
| `zipWith` | deferred | Requires synchronized list recursion and a specialized first-order operator interface. |
| `filter` | deferred | Requires list fold/recursion and an explicit first-order predicate interface. |
| `dEqual` | deferred | General Nat equality needs dynamic structural recursion or a primitive. |
| `dDiv` | deferred | Requires comparison, subtraction, dynamic recursion, and an explicit total zero-divisor result. |
| `listLength` | modernized | `Prelude.listLength : List Nat -> Nat`; reusable first-order `FoldS` placement over an affine runtime list. |
| `listEqual` | deferred | Requires list recursion and Nat equality. |
| `listPlus` | deferred | Reusable folding exists, but order-preserving append needs a right fold or additional affine list-state support for the open second list. |
| `flip` | modernized | `flipNat` swaps the pair argument of an affine `Nat * Nat -o Nat` closure. General polymorphic flip remains unavailable. |
| `con` | modernized | `composeNat` composes two affine `Nat -o Nat` closures; each is applied exactly once. General polymorphic composition remains unavailable. |
| `concat` | deferred | Needs nested-list syntax plus order-preserving append; sequencing dependent recursive results remains outside current placement. |
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
