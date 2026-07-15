# Direct Bend Backend

`Telomare.Backend.Bend` is an initial, direct, first-order source generator. Its
only compiler input is the opaque `ValidatedArtifact` produced by
`Telomare.Transport.validateArtifact`. It neither imports nor parses or
typechecks Tel2. The separate `telomare-bend ARTIFACT` command reads the stable
transport S-expression, validates it, and prints Bend source. It is intentionally
not an interactive backend of the existing `telomare` CLI; the Haskell runtime
and defaults are unchanged.

## Encoding and semantics

Generated source defines one named Bend function for every transport node and
specialized named helpers for recursion. Morphisms and loop bodies are never
passed as first-class values or copied closures. This follows the historical HVM
lesson that duplicating higher-order tuple functions inside recursion was both
fragile and unnecessary. Generation itself is pure, and the output is intended
to remain inspectable.

Values use the tagged `Value` type: `Unit`, `Nat { value }`, `Prod`, `Inl`,
`Inr`, `Nil`, and `Cons`. `telomare_run` recursively checks that the supplied
encoding has the artifact's input type and returns `Run/InvalidInput` on a tag mismatch.
Successful execution returns `Run/Ok(value)`; checked arithmetic failure
returns `Run/DomainError`.

The exact preserved value conventions are:

- Composition evaluates the right node and then the left node.
- Product keeps left/right order; sum case selects `Inl`/`Inr` without changing
  payload order.
- Lists are folded head-to-tail. `Fold` input is `(list, seed)` and its body
  receives `(accumulator, element)`.
- `Iter` input is `(count, seed)` and invokes its body exactly `count` times.
- `While` input is `(limit, seed)`. It is a bounded pre-test loop: `Inl Unit`
  stops with the current state, while `Inr Unit` takes one step. A zero limit
  performs neither test nor step.
- `Guard` passes the original value in `Inl` when its test returns `Inl Unit`,
  and returns `Inr Unit` when the test returns `Inr Unit`.
- `Box`, `BoxVal`, and `Merge` are value-transparent. Their generated comments
  retain modal metadata. This is not a claim that Bend or HVM enforces EAL.

## Checked natural domain

Bend's scalar is `u24`, not the unbounded `Natural` used by the core semantics.
This prototype therefore has the explicit domain `0..16777215`. Emission rejects
larger `NConst` values. Bend's parser/runtime supplies `u24` payloads, while the
generated tagged input checker rejects non-`Nat` payload constructors. `Suc` and
`Add` check for overflow before arithmetic and return `Run/DomainError`; the
backend makes no silent-wrap equivalence claim. Consequently exact Natural
semantics are preserved only for executions whose inputs and intermediate
results stay in this checked domain.

## Limits and running

This is value-only. It does not preserve or claim preservation of work, fuel, or
duplication grades. `NDup` and `NDupNat` preserve value results only. The backend
has no proof of correctness and no Agda-to-Bend proof bridge.

Generate a backend module with:

```sh
cabal run telomare-bend -- program.transport > program.bend
```

The generated module intentionally has no `main`: an invocation must supply a
closed encoded input without relying on Bend's command-line parser for ADTs:

```bend
def main():
  return telomare_run(Value/Nat(3))
```

Then run with a conservative timeout because runtime/toolchain regressions can
hang:

```sh
timeout 30s bend run-c program.bend
```

The flake also exposes that complete pipeline for a `.tel2` machine entry. The
input is a closed Bend expression in the generated `Value` encoding:

```sh
nix run .#bend -- init test/programs/bend-smoke.tel2 'Value/Unit'
```

The smoke program also exercises runtime-bound `IterS` placement end to end:

```sh
nix run .#bend -- step test/programs/bend-smoke.tel2 \
  'Value/Prod(Value/Nil, Value/Nat(3))'
```

The app compiles the selected `init` or `step` entry to transport, validates and
emits it through `telomare-bend`, supplies `main`, and applies the same 30-second
timeout.

The test suite always checks emitter coverage and source properties. External
execution is gated by `TELOMARE_BEND`; without it, the runtime differential test
is reported as an explicit skip rather than downloading or guessing a Bend
version.
