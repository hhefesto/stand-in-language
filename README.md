# Telomare

Telomare is a total-language experiment built around one goal: programs should
have ordinary executable behavior and knowable resource structure. The current
implementation is the regular `telomare` package and executable.

For the long type-by-type narrative, see [`STORY.md`](STORY.md).

The repository now has one active implementation:

- `spec/`: the Agda source of truth, checked with `--safe` and no postulates.
- `src/Telomare/`: the Haskell mirror and runtime.
- `src/Telomare/Compat/`: the explicitly moved compatibility frontend needed to read existing `.tel` programs.
- `app/Main.hs`: the `telomare` executable.
- `test/`: semantic vectors, laws, budget and placement checks, and `.tel` transcript fixtures.

## Quick Start

Run an existing `.tel` program through the Telomare Tier-2 runtime:

```sh
nix run . -- test/programs/tictactoe.tel
```

Or use Cabal inside the development shell:

```sh
nix develop
cabal run telomare -- test/programs/tictactoe.tel
```

Useful runtime options:

```sh
cabal run telomare -- --certificate test/programs/tictactoe.tel
cabal run telomare -- --meter test/programs/tictactoe.tel
cabal run telomare -- --max-steps 10000 test/programs/tictactoe.tel
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

The current `.tel` executable is intentionally practical. It reuses the moved
compatibility parser, resolver, and type checker for existing `.tel` syntax,
then runs on a new metered runtime. This runtime does not use the old sizing
pass. Recursion sites become native demand-driven recursion nodes, so programs
that were previously rejected as unsized can still run, and `--max-steps` can
turn nontermination into an explicit runtime fuel error.

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

The active executable runs `.tel` programs as follows:

1. Load the entry module and imports relative to the entry file.
2. Parse, resolve, and type-check using the moved compatibility frontend.
3. Convert the old unsized recursion marker into Telomare's native runtime node.
4. Run the Tier-2 metered environment machine.

The interactive protocol is the existing `.tel` protocol: `main` is a closure
that receives an input/state value and returns display/state. The loop prints the
display string, reads a line when the state continues, and exits when the state
is zero. End-of-file exits cleanly.

The meter reports:

- function applications;
- gate selections;
- per-site recursion unroll counts.

## Verification

The checked and tested evidence is intentionally layered:

- Agda: `spec/Everything.agda` imports the full specification and checks with `--safe` and no postulates.
- Haskell mirror: core value, work, duplication, execution, placement, and budget functions mirror the spec.
- Tests: Agda example vectors, placement oracles, budget oracles, `.tel` transcript parity, and QuickCheck laws.
- Golden transcripts: tictactoe fixtures and small programs exercise the compatibility runtime.

The Haskell tests are regression evidence for the mirror and runtime. The Agda
proofs are the formal source of truth for the core semantics.

## Current Limits

The formal totality and adequacy theorems apply to the typed core, not yet to the
full `.tel` compatibility runtime.

The current `.tel` runtime is Tier 2: it deoptimizes instead of rejecting when a
finite bound is unknown. Without `--max-steps`, a genuinely unbounded `.tel`
program can keep running.

The compatibility frontend is still present because existing `.tel` syntax and
fixtures depend on it. It has been moved into `Telomare.Compat.*` so it is no
longer confused with the active semantic core.

The CLI `--certificate` report is currently the structural levels report from
the compatibility frontend. The newer budget and placement mirrors exist in
`Telomare.Budget` and `Telomare.Infer`, but they are not yet a single integrated
user certificate pipeline.

The Agda spec defines a space grade; the Haskell mirror currently implements
work and duplication. The spec also proves that simple additive word-size
majorization is not enough for the current fuel-carrying list-building
iteration, so richer resource models remain part of the research program.

Tier-1 labeled-fan execution and a proved fidelity theorem for the compatibility
runtime remain future work.

## License

Telomare is licensed under Apache-2.0. See `LICENSE`.
