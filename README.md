# Telomare

Telomare is a total-language experiment built around one goal: programs should
have ordinary executable behavior and knowable resource structure. The current
implementation is the regular `telomare` package and executable.

For the long type-by-type narrative, see [`STORY.md`](STORY.md).

The repository now has one active implementation:

- `spec/`: the Agda source of truth, checked with `--safe` and no postulates.
- `src/Telomare/`: the Haskell core, formal surface mirror, direct compiler, and runtime.
- `src/Telomare/Compat/`: archived compatibility implementation retained temporarily for regression comparison.
- `app/Main.hs`: the `telomare` executable.
- `test/`: core and surface semantic vectors, laws, compiler checks, budget and placement checks, and `.tel2` transcript fixtures.

## Quick Start

Run tic-tac-toe through the typed formal core:

```sh
nix run . -- test/programs/tictactoe.tel2
```

Or use Cabal inside the development shell:

```sh
nix develop
cabal run telomare -- test/programs/tictactoe.tel2
```

The `.tel2` path compiles a declarative finite machine to typed `Morph`
artifacts and executes them with `evalV`, `evalG`, and `evalK`. It does not use
the compatibility frontend or `TelExpr`.

Useful runtime options:

```sh
cabal run telomare -- --certificate test/programs/tictactoe.tel2
cabal run telomare -- --meter test/programs/tictactoe.tel2
cabal run telomare -- --max-work 1000000 test/programs/tictactoe.tel2
```

Development checks:

```sh
cabal test telomare-test
agda --safe spec/Everything.agda
nix flake check
nix run .#format-lint
```

## The Telomare Spirit

Telomare is not trying to be a Turing-complete language with a bolt-on timeout.
It is trying to make bounded computation part of the meaning of a program.

The formal core is total. Recursion is structural or fuel-carrying, so a core
term denotes a total function. Resource observations are also semantic objects:
the same syntax can be interpreted as values, work, duplication pressure, space,
or fuel-metered execution.

The repository also has a box-free typed surface category and the first proved
compiler slice from that surface into the core. It is not connected to `.tel`
parsing yet, but it establishes the first executable and machine-checked part of
the future pointful `.tel2 -> UMorph -> Morph` path.

The executable now accepts `.tel2` only. It compiles a declarative program into
typed `Morph` values, then interprets those values through the formal value,
graded, and fuel semantics. The old compatibility implementation remains in the
tree temporarily, but it is not an executable fallback or a second meaning for
`.tel2`.

## Mathematical Core

The checked core is a first-order typed category.

Types include unit, naturals, products, sums, lists, and the modal type `!A`.
The value interpretation maps them to ordinary Agda sets:

```text
[[unit]]     = 1
[[nat]]      = Nat
[[A * B]]    = [[A]] x [[B]]
[[A + B]]    = [[A]] + [[B]]
[[list A]]   = List [[A]]
[[!A]]       = [[A]]
```

The last equation is deliberate: bang decorations do not change the value set.
They change the resource discipline. Agda proves that erasing those decorations
preserves value semantics.

The core is affine and EAL-inspired:

- Weakening is allowed.
- General contraction is absent.
- Structural duplication exists only at `!A` through `dupS`.
- Natural numbers have a separate atom-level duplication primitive.
- Promotion is restricted; there is no dereliction and no digging.

This is the resource idea behind the language: copying is not implicit ambient
power. Copying has a place in the syntax, and the semantics can charge for it.

`Telomare.Copyable` makes that principle reusable without restoring ambient
contraction. A `Copyable A` value is evidence for a concrete morphism
`A -> A * A`. Unit, naturals, products of copyable values, and boxed values have
such evidence; there is no catch-all instance. Haskell vectors check values and
duplication grades, while Agda's `T3.Core.Copyable.copyS-correct` proves that the
synthesized morphism denotes `(a, a)`.

## Formal Surface Compiler

`Telomare.Surface` mirrors `T3.Surface.Ty`, `T3.Surface.Syntax`, and
`T3.Surface.Sem` from the Agda specification. Surface types are box-free:

```haskell
data UTy
  = UUnit
  | UNat
  | UTy :**: UTy
  | UTy :++: UTy
  | UList UTy
```

`UMorph` provides ordinary categorical structure, products, sums, lists,
naturals, guards, free surface duplication, and explicitly bounded recursion.
`evalU` gives this syntax a plain total value semantics.

`Telomare.Compiler.Direct` implements the first surface-to-core compiler slice:

```haskell
compileDirect
  :: UMorph a b
  -> Either DirectError (Morph (Lift a) (Lift b))
```

The direct slice currently compiles:

- identity, composition, and tensor;
- product, sum, distributivity, unit, and weakening structure;
- list and natural constructors and destructors;
- constants, successor, and addition;
- refinement guards;
- natural duplication through the core's measured `DupNatS` exemption.

It explicitly rejects general surface duplication and `UIter`, `UFold`, and
`UWhile`. Those constructs require modal and recursion placement rather than a
placement-free translation.

`eraseMorph` maps core terms back to surface syntax. Haskell vectors compare
surface evaluation with compiled core evaluation and check that successful
results erase back to the original surface structure. In Agda,
`T3.Compiler.Direct` defines the matching elaboration relation and proves:

- `direct-erases`: successful elaboration erases exactly to its source term;
- `direct-factor`: successful elaboration preserves value semantics.

Both proofs are checked under `--safe` and are imported by `Everything.agda`.
This bridge begins at `UMorph`; general pointful `.tel2` elaboration into `UMorph`
remains future work. The deliberately smaller `.tel2` finite-machine frontend
described below lands directly in `Morph` without claiming to implement that
future pointful language.

## Core-Only `.tel2` Machines

`Telomare.CoreMachine` implements a line-oriented, typed finite-machine subset.
Its declarations are compositional machine data:

```text
telomare-finite-machine 1
initial "state-key"
global "q" stop "Goodbye.\n"
state "state-key" "display text"
on "1" goto "next-state"
on "2" stay "That square is occupied.\n"
default stay "Invalid input.\n"
```

The fixed ABI is `Text = List Nat`, `State = List Nat`,
`Input = Text * State`, and `Reply = Text * (Unit + State)`, where the left
continuation branch stops. Compilation resolves every declaration into closed
`Morph Unit Reply` and `Morph Input Reply` artifacts. Exact key matching is
built from `NatOutS`, `UnconsS`, sums, products, and affine reconstruction;
there is no filename dispatch, game primitive, embedded Haskell transition
function, semantic fallback, or `unsafeCoerce`.

`test/programs/tictactoe.tel2` contains the complete generated finite machine.
The small generator in `design/generate-tictactoe.hs` only maintains that
declarative fixture and is not linked into the compiler or executable. This
large table is an extensional normal form for the first milestone, not the final
pointful `.tel2` syntax. Its advantage is semantic transparency: every accepted
input/state pair and result is source data, while the compiler only supplies the
generic finite-machine interpretation into `Morph`.

This is a denotational choice: a deterministic finite machine denotes a total
function from input and state to output and optional next state. The source gives
that function extensionally; compilation builds it from sums, products, natural
and list observations, and constants. There is no source evaluator whose answer
must later be reconciled with the core.

Dispatch is affine. A failed text or state comparison reconstructs exactly the
value it consumed and passes it to the next branch. It neither copies the value
nor consults host equality. The resulting large linear search is intentionally
not hidden: `NatOutS` observations contribute to the formal work grade, making
the cost of this simple normal form visible. A later intensional pointful syntax
can optimize the representation while preserving this denotation.

## Resource Semantics

`T3.Sem.Graded` defines a generic graded interpretation. A cost algebra supplies
sequential composition, parallel composition, primitive charges, loop-step
charges, and probe charges. Agda proves that the value component of every graded
interpretation agrees with the ordinary value semantics.

Implemented grades include:

- Work: charges `natOutS` and each taken loop step.
- Duplication: charges `dupS`, natural-number duplication, and guard/while probes.
- Space in the Agda spec: charges by input/output word size with max for sequential composition and addition for parallel composition.

For the work grade, Agda proves precision with slack:

```text
evalK f a (work f a + extra) = just (evalV f a, extra)
```

With `extra = 0`, this is adequacy: running with exactly the computed work grade
returns exactly the denoted value and consumes exactly the supplied work.

## Placement And Budgets

Telomare separates two analyses that historically became tangled.

Placement is structural. A recursion skeleton records recursion sites and
call-offset edges. Agda proves that valid placements are meet-closed and that the
structural placement algorithm computes the least solution. This gives a
mathematical form to the intuition that iteration levels should be inferred by
syntax, not by runtime probing.

Budgets are value-sensitive. The abstract interpreter tracks shapes such as
bounded naturals, products, sums, bounded lists, and unknown top. It proves that
transfer soundly over-approximates output values. Recursion-site budget trees
record finite bounds when known and `top` when the analysis loses a finite
bound. Nested recursion joins inner budgets over every abstract outer unrolling,
matching the “maximum over outer iterations” behavior expected from the level
structure.

The spec also proves a stability fact for bounded while loops: once the test has
stopped, adding more fuel does not change the result.

## Runtime Model

The host only converts terminal lines to and from `List Nat` and
drives I/O. Initialization and every transition are evaluated as `Morph` by all
three core interpretations: value, work grade, and fuel execution. Their values
are checked for agreement at runtime. `--meter` reports accumulated core work,
and `--max-work` bounds that work across the interaction.

## Verification

The checked and tested evidence is intentionally layered:

- Agda: `spec/Everything.agda` imports the full specification and checks with `--safe` and no postulates.
- Haskell mirror: surface and core value semantics, direct elaboration, erasure, work, duplication, execution, placement, and budget functions mirror the spec.
- Tests: Agda example vectors, surface/compiler vectors, explicit-copy vectors, placement oracles, budget oracles, `.tel2` transcripts, and QuickCheck laws.
- Golden transcripts: `.tel2` fixtures exercise scripted core `Morph` machines; legacy fixtures remain temporary regression material.

The Haskell tests are regression evidence for the mirror and runtime. The Agda
proofs are the formal source of truth for surface elaboration and core semantics.

## Current Limits

The formal totality and adequacy theorems apply to every generated `Morph`.
`UMorph -> Morph` also inherits value semantics through the direct compiler's
erasure theorem. There is still no general pointful `.tel2 -> UMorph` frontend or
modal placement pass; the finite-machine frontend instead targets a small
auditable affine core fragment directly.

The archived `.tel` parser and Tier-2 runtime are still compiled and regression
tested during migration, but `app/Main.hs` neither imports nor invokes them.
Supplying a `.tel` file to the executable is an error.

The `.tel2` subset is intentionally first-order and finite: it has named states,
exact text inputs, global rules, and `goto`/`stay`/`stop` targets. It does not yet
provide pointful expressions, user-defined algebraic data, inferred copying, or
recursion. Its dispatch currently compiles to linear affine partitions, favoring
a small auditable core translation over compact or asymptotically fast code.

The Agda spec defines a space grade; the Haskell mirror currently implements
work and duplication. The spec also proves that simple additive word-size
majorization is not enough for the current fuel-carrying list-building
iteration, so richer resource models remain part of the research program.

The next source-language milestone is a typed pointful affine layer with explicit
`copy`, elaborating compositionally to `UMorph`; general copying and recursion
remain unavailable until modal realization can produce typed core syntax.

## License

Telomare is licensed under Apache-2.0. See `LICENSE`.
