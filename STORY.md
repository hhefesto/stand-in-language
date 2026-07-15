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

`.tel2` is modular, first-order, monomorphic, and statically typed. A module has
an explicit header and imports modules by name. Resolution prefers a sibling of
the entry file, allowing deliberate local shadowing, then uses Cabal's packaged
`stdlib` data independently of the working directory. Selected module headers
are always validated. Imported declarations share one namespace. The compiler loads the acyclic module graph, collects types
and definition dependencies, and compiles bodies in dependency order, so source
order is not semantically significant. Anonymous import-free snippets
retain a pure compilation path. The language has named product/sum aliases,
nullary finite data, variables, tuples, `let`, constructor cases, exact Nat/Text
matching, literals, primitive Nat successor/addition, finite text prefixing,
named definitions, and explicit `copy`. `README.md` is the normative grammar.

The recursive source slice is intentionally narrower than the surface syntax. A
whole `init` or `step` body may start with independent closed iteration, fold,
and literal-capped while bindings. Their steps/tests are non-recursive direct
morphisms; fold inputs and all seeds are closed. Each binding translates to
`BoxValS` plus an actual `IterS`, `FoldS`, or `WhileS`. The compiler combines
their boxed results with `MergeS` and promotes one final continuation with
`BoxS`. Capturing the entry input would require open promotion, so it is
rejected; dependent/nested loops and loops in helpers remain rejected pending a
real placement compiler.

The elaborator carries an ordered typed context. A variable projection returns
the variable and the context with that binding removed. Pairing elaborates the
left expression and feeds only its remainder to the right. `let` puts exactly
the produced value back into the context. Literal matching partitions once;
failed arms reconstruct the affine scrutinee. Branch-local leftovers are
weakened. There is no implicit duplication.

`copy` requires structural evidence. Unit and Nat are copyable, and products are
copyable exactly when both components are. Product copying is synthesized from
Nat duplication and product reassociation, not admitted as general contraction.

The terminal convention is deliberately separate from the language semantics.
Each compiled entry existentially packages its possibly decorated core endpoint,
an `STy`, and a proof that stripping boxes yields the source endpoint. Runtime
conversion follows the singleton structurally; boxes are never removed by a
core morphism. A program chooses `State`, while `init` and `step` expose
`Text * (Unit + State)`. `Unit` means stop. The existential `Program` packages
the state witness with surface and compiled core morphisms. The host only codes
text, drives lines, accounts fuel, and checks evaluator agreement.

## Surface And Core

`UMorph` is box-free typed surface syntax. `Morph` is affine,
resource-aware core syntax with explicit exponential structure and fuel-carrying
recursion. Their constructors present category-like operations, but raw syntax
trees are not quotiented by category, tensor, sum, or modality equations.
`Telomare.Ops` makes that distinction explicit: its capability classes expose
operations without asserting laws. `compileDirect` covers the placement-free structural/data fragment
and the measured Nat-copy exemption. It still rejects general duplication and
recursion requiring modal placement.

Finite text literals, literal prefixing, and reconstructing Nat/Text partitions
are derived `UMorph` terms for this source slice. Primitive `suc` and `add`
elaborate to existing `USuc` and `UAdd`, then `SucS` and `AddS`. They and the
derived forms use the original unit, product, sum, Nat, and list surface
constructors before `compileDirect`; no host arithmetic callback, unproved
surface constructor, or runtime equality callback is introduced.

The packaged `stdlib/Prelude.tel2` provides finite Bool operations, Nat
predicates/conversions, addition, successor, explicit Nat doubling, and a
reusable first-order `listLength` placed over an affine runtime list.
`stdlib/LegacyPrelude.tel2` contains only six honest monomorphic or modernized
aliases. `design/PRELUDE_MIGRATION.md` accounts for all 50 historical Prelude
names; Church encodings, higher-order combinators, partial abort, and unsupported
dependent recursion are not presented as migrated.

The runner evaluates every initialization and step through `evalV`, `evalG`,
and `evalK`, compares those values structurally using the existential state
witness, and also compares the result with `evalU`. Work and fuel therefore
refer to the same core artifact that determines behavior.

## One Syntax, Several Interpretations

The architecture follows a denotational pattern without forcing the core into
a cartesian closed category:

```text
Morph
  -> value interpretation
  -> graded work/duplication interpretations
  -> fuel-state execution
  -> versioned transport artifact
```

Each arrow is a separate structural interpretation with its own preservation
claim. Value semantics validates category laws extensionally. Erasure preserves
identity and composition by construction and its value square commutes in Agda.
Graded semantics is proved to project to value semantics, and precision relates
formal work to exact successful fuel. The raw syntax itself is not silently
normalized by those equations, because a value-preserving rewrite may change a
resource grade.

`Telomare.Transport` retains every core constructor and `Bang` in a stable
S-expression. An
independent unification pass validates untrusted artifacts but deliberately does
not reconstruct a trusted GADT with a cast.

`Telomare.Linear` is an additional, point-free Haskell frontend over the same
surface syntax. Linear arrows constrain local circuit-description use; affine
discard and copying remain explicit operations, and copying requires a witness.
Closed recursion uses the same `Telomare.Compiler.Closed` implementation as the
textual frontend. This is a host notation, not a replacement for `.tel2`, and it
does not expose `Bang` as a host source type.

## Tic-Tac-Toe

The example is ordinary source code, not compiler policy. It explicitly imports
the ordinary `Prelude.tel2` module and uses its player-transition and zero-test
definitions.
Nine Nat values form a named `Board` product and one Nat is the turn. Definitions
implement line classification, eight winning projections, tie detection, fixed-width
rendering, legal and occupied moves, invalid input, turn changes, and replies.
The repeated board uses are visibly enabled by `copy`.

Changing source strings changes denotation, and all win/quit/invalid/tie golden
transcripts pass through both `UMorph` and `Morph`. The removed frontend no
longer computes reachable positions, renders a board, or recognizes any game
declaration.

## Proof Story

The Agda core proves adequacy and graded laws. The Agda direct relation proves
erasure and semantic preservation for successful surface-to-core elaboration.
`T3.Compiler.ClosedRecursion` constructs closed and affine-controller iterate,
fold, and while core terms from directly compiled components and proves exact
erasure plus value preservation via `ε-factor`. Open fuel/list controllers stay
at orchestration level while only empty-context seeds are promoted. The module
also covers pairwise `MergeS` of independent boxed closed results, which
composes to the environment shape used by the implementation.
`T3.Compiler.Partition` gives the generic affine Nat-partition preservation
lemma. `T3.Source.Affine` states the central resource rules used by the pointful
elaborator: lookup, context splitting/weakening, product, let, explicit copy,
and case.
`T3.Categorical.Vocabulary` separates operation records, hom equality, and law
records. `T3.Categorical.Interpretation` packages Core and Surface operations,
proves category laws only under value-extensional equality, and exposes erasure,
direct compilation, and graded/value commuting statements explicitly.

These are categorical translations and a formalized source judgment, not proofs
of the Megaparsec implementation. In particular, the recursion theorem assumes
`Direct` evidence and does not verify Haskell's free-variable, modal-cut, or
source-helper recognition. Parser correctness, alias resolution, enum coverage,
closure-check correspondence, and a full simulation theorem from Haskell
elaboration to the Agda relations remain open. The repository states this
boundary rather than treating tests as proofs.

## Current Scope

The implemented source is intentionally small: modules currently form one
unqualified namespace with sibling-first, packaged-stdlib fallback, and there is
no polymorphism, general recursion, higher-order values, arbitrary records,
general append, or general multi-level modal placement. Independent closed
whole-entry loops and reusable first-order helpers with affine runtime fuel/list
controllers are accepted. Seeds remain closed; live unboxed context after a
loop, dependent/nested recursion, and captured loop bodies are rejected. Named
product aliases and tuple patterns provide record-like finite state. Enums are nullary
and currently erase to Nat; constructor coverage
is checked, but nominal separation is lost after representation erasure. These
restrictions are language-wide and contain no game-specific exception.
