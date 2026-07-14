# Telomare: Source, Surface, Core

Telomare separates a usable pointful language from a small typed semantic core.
The active path is now one path rather than a game frontend beside a future
compiler:

```text
.tel2 expressions
  -> affine typed UMorph
  -> placement-free compileDirect
  -> Morph
  -> value, work-grade, and fuel semantics
```

## Source

`.tel2` is single-file, first-order, monomorphic, and statically typed. It has
named product/sum aliases, nullary finite data, variables, tuples, `let`,
constructor cases, exact Nat/Text matching, literals, finite text prefixing,
named definitions, and explicit `copy`. `README.md` is the normative grammar.

The elaborator carries an ordered typed context. A variable projection returns
the variable and the context with that binding removed. Pairing elaborates the
left expression and feeds only its remainder to the right. `let` puts exactly
the produced value back into the context. Literal matching partitions once;
failed arms reconstruct the affine scrutinee. Branch-local leftovers are
weakened. There is no implicit duplication.

`copy` requires structural evidence. Unit and Nat are copyable, and products are
copyable exactly when both components are. Product copying is synthesized from
Nat duplication and product reassociation, not admitted as general contraction.

The terminal convention is deliberately separate from the language semantics:
a program chooses `State`, while `init` and `step` expose
`Text * (Unit + State)`. `Unit` means stop. The existential `Program` packages
the state witness with surface and compiled core morphisms. The host only codes
text, drives lines, accounts fuel, and checks evaluator agreement.

## Surface And Core

`UMorph` is the box-free surface category. `Morph` is the affine,
resource-aware core with explicit exponential structure and fuel-carrying
recursion. `compileDirect` covers the placement-free structural/data fragment
and the measured Nat-copy exemption. It still rejects general duplication and
recursion requiring modal placement.

Finite text literals, literal prefixing, and reconstructing Nat/Text partitions
are derived `UMorph` terms for this source slice. They expand into the original
unit, product, sum, Nat, and list surface constructors before `compileDirect`.
No unproved surface constructor or runtime equality callback is introduced.

The runner evaluates every initialization and step through `evalV`, `evalG`,
and `evalK`, compares those values structurally using the existential state
witness, and also compares the result with `evalU`. Work and fuel therefore
refer to the same core artifact that determines behavior.

## Tic-Tac-Toe

The example is ordinary source code, not compiler policy. Nine Nat values form a
named `Board` product and one Nat is the turn. Definitions implement line
classification, eight winning projections, tie detection, fixed-width
rendering, legal and occupied moves, invalid input, turn changes, and replies.
The repeated board uses are visibly enabled by `copy`.

Changing source strings changes denotation, and all win/quit/invalid/tie golden
transcripts pass through both `UMorph` and `Morph`. The removed frontend no
longer computes reachable positions, renders a board, or recognizes any game
declaration.

## Proof Story

The Agda core proves adequacy and graded laws. The Agda direct relation proves
erasure and semantic preservation for successful surface-to-core elaboration.
`T3.Compiler.Partition` gives the generic affine Nat-partition preservation
lemma. `T3.Source.Affine` states the central resource rules used by the pointful
elaborator: lookup, context splitting/weakening, product, let, explicit copy,
and case.

That last module is a formalized source judgment, not a proof of the Megaparsec
implementation. Parser correctness, alias resolution, enum coverage, and a full
simulation theorem from Haskell elaboration to the Agda relation remain open.
The repository states this boundary rather than treating tests as proofs.

## Current Scope

The implemented source is intentionally small: no modules, polymorphism,
recursion, higher-order values, arbitrary records, general append, or modal
placement. Named product aliases and tuple patterns provide record-like finite
state. Enums are nullary and currently erase to Nat; constructor coverage is
checked, but nominal separation is lost after representation erasure. These
restrictions are language-wide and contain no game-specific exception.
