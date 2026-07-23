# Telomare

Telomare is a total-language experiment with a machine-checked affine core,
graded resource semantics, and a small general-purpose typed `.tel2` language.

## Run

```sh
nix run . -- test/programs/tictactoe.tel2
# or, in nix develop:
cabal run telomare -- test/programs/tictactoe.tel2
```

`--certificate` prints certified static work and duplication bounds: a-priori
per-entry caps computed by abstract interpretation and proved sound in Agda
(`T3.Bound.costW-sound` and `costD-sound`). By adequacy, the work bound is
literally a machine fuel bound. A duplication bound may be unbounded for an
arbitrary variable-size input while remaining finite at a refined input shape.
`--meter` prints accumulated formal core work, and `--max-work N` bounds that
work. Static bounds are honest, not tight: loops are charged full fuel and
branches by max. The executable accepts `.tel2` only.
`--emit-transport init|step` prints one backend-neutral core entry and exits,
providing the explicit handoff to experimental runtimes.

## Active Pipeline

```text
entry .tel2 module + filesystem imports
  -> Megaparsec syntax tree
  -> module graph + definition dependency ordering
  -> name/type checking + affine context elaboration
  -> existentially typed UMorph init and step
  -> compileDirect or closed-recursion placement
  -> typed Morph init and step
  -> evalV / evalG / evalK agreement
  -> terminal text codec and I/O
```

`Telomare.Tel2` contains no board, grid, player, line, rendering, reachability,
or tic-tac-toe concepts. `Telomare.Machine` knows only the generic terminal ABI.
It converts terminal characters to `List Nat`, transports the source-selected
state existentially, runs the core evaluators, and checks surface/core and
value/grade/fuel agreement. There is no filename dispatch, host transition
callback, semantic fallback, `TelExpr`, or `unsafeCoerce`.

The historical `.tel` compatibility modules remain compiled for regression
tests, but the executable does not import or invoke them.

## Language

Whitespace, `--` line comments, and nested `{- -}` block comments are
ignored (see `design/SYNTAX.md` for the telomare0 convergence record; the
legacy `#` comments, `apply`/`def`/`matchNat`/`matchText` keywords, and
all semicolons and arm braces are gone). Identifiers start with a letter.
String escapes are Haskell-style. Layout is telomare0's: declarations
start at column 1, an expression continues on later lines only when
indented (application arguments must be indented past the head of the
application), `let` bindings separate by line, and `case` arms are
aligned at one column — the first outdented token ends the block.
Module files begin with a `module` header; `import`s precede declarations.

A top-level definition is `name : A -o B = \x -> body` — the mandatory
type sits where telomare0 puts its refinement annotation, and the body is
a lambda whose first pattern becomes the definition argument. Definitions
are monomorphic and take exactly one argument; they may refer to
definitions or type aliases declared later. Bodies are compiled in
dependency order; dependency cycles are rejected. Functions are
first-class: `A -o B` is an affine closure type, lambdas capture their
free variables, application `f x` consumes a closure, and definitions may
return or select closures at runtime. Source recursion is restricted to
manifestly bounded map, iteration, fold, while, and the higher-order
`mapc`, `iterc`, `foldc`, and `whilec`, whose reusable closure bodies are
selected among closed lambdas (dispatch by `case` over an affine
scrutinee); their seeds may be open first-order data (promoted at the
loop boundary), and `whilec`'s stepping selector must be closed.

There is one `case e of` form; the shape of its first arm picks the
dispatch. String-literal arms match text and nat-literal arms match
naturals, both ending in a binding (or `_`) default arm; constructor arms
eliminate a `data` enum exhaustively with no default. `if c then t else e`
is sugar for a nat case taking `else` at `0`; list literals are sugar for
`cons` chains; multi-binding `let`s and multi-argument lambdas nest
(lambdas curry). `succ`, `add`, `cons`, and `prepend` are builtin
functions applied by juxtaposition (`succ n`, `add (a, b)`,
`cons x xs`, `prepend "lit" t` — prepend's first argument must be a text
literal); a local binding or definition of the same name shadows them.
Application is by juxtaposition of atomic expressions, `f x y`, and is
left-associative: a head naming a local binding applies that closure, an
unshadowed definition name is a call — lexical scope wins. Keywords
cannot be identifiers, so chains stop at `in`, `with`, `then`, and their
kin (`f(x)` still reads naturally: `f` applied to a parenthesized atom).
`let` annotations may be omitted when the bound value's type is
synthesizable (variables, literals, tuples, calls and applications,
`succ`/`add`, `copy`, `prepend`, and loop results via their step
definitions); lambdas, injections, and `[]`/`mapc` results still need
one, and top-level signatures are always explicit.

`main` is the entry point, in either of two shapes. The telomare0-exact
shape `main : Text * State -o Text * State` (with `State` defaulting to
`Nat`) first runs with an empty input and state `0` and halts when the
returned state is `0` (a priced case performs the halt test). The general
shape `main : Text * State -o Reply State` works for any first-order
`State`: the fresh state comes from `start : Unit -o State` (defaulted to
`0` when `State` is `Nat`), the program encodes freshness in its state
exactly as telomare0's state-0 test, and halting is main's own `left ()`.
The machine's `init`/`step` pair is synthesized from `main`; declaring
`init` or `step` directly is an error.

```text
program   ::= ("module" ID)? ("import" ID)* declaration*
declaration
          ::= "type" ID "=" type
           |  "data" ID "=" ID ("|" ID)*
           |  ID ":" type "=" expr        -- type is an arrow, expr a lambda

type      ::= sum ("-o" type)?
sum       ::= product ("+" sum)?
product   ::= atom ("*" product)?
atom      ::= "Unit" | "Nat" | "Text" | ID
           |  "List" atom | "Reply" atom | "(" type ")"

expr      ::= ID | NAT | STRING | "()" | CONSTRUCTOR
           |  "[" (expr ("," expr)*)? "]"
           |  "(" expr "," expr ("," expr)* ")"
           |  atom atom+                  -- includes succ/add/cons/prepend
           |  "let" binding+ "in" expr
           |  "if" expr "then" expr "else" expr
           |  "copy" expr
           |  "\\" pattern+ "->" expr
           |  "map" expr "with" ID
           |  "mapc" expr "with" expr
           |  "iterc" expr "from" expr "with" expr
           |  "foldc" expr "from" expr "with" expr
           |  "whilec" expr "from" expr "testing" expr "stepping" expr
           |  "iterate" expr "from" expr "with" ID
           |  "fold" expr "from" expr "with" ID
           |  "while" expr "from" expr "testing" ID "stepping" ID
           |  "left" expr | "right" expr
           |  "case" expr "of" natArm* patternArm      -- nat dispatch
           |  "case" expr "of" textArm* patternArm     -- text dispatch
           |  "case" expr "of" constructorArm+         -- enum dispatch

binding   ::= pattern (":" type)? "=" expr
pattern   ::= ID | "_" | "(" ID ("," ID)+ ")"
natArm    ::= NAT "->" expr
textArm   ::= STRING "->" expr
patternArm ::= pattern "->" expr
constructorArm ::= CONSTRUCTOR "->" expr
```

Case arms are layout-aligned: every arm of one `case` starts at the same
column, and the block ends at the first token left of that column.

The CLI requires a module header. `import Foo` first checks `Foo.tel2` beside
the entry file, then asks Cabal for packaged `stdlib/Foo.tel2` data. A present
sibling deliberately shadows the stdlib and remains authoritative even if its
header is invalid; imports never silently fall through after selecting it. The
selected file's header must be `module Foo`. Imports are transitive, diamond
imports are loaded once, and cycles or missing modules are errors. Packaged
stdlib resolution is independent of the process working directory.
`compileTel2` remains a pure entrypoint for anonymous, import-free source used by
small tests; `compileTel2File` is the module-aware IO entrypoint used by the CLI.
Imported declarations currently share one unqualified namespace.

Closed recursion is accepted as a chain of bindings:

```text
main : Text * State -o Reply State = \request ->
  let (input, state) = request
   in case state of
        0 -> let _ = input
                 i = iterate N from closedSeed with iterStep
                 f = fold closedList from closedAccumulator with foldStep
                 w = while N from closedSeed testing test stepping whileStep
              in closedResultUsingOnlyIAndFAndW
        s -> directArmUsing input s
```

Any nonempty subset and order of these bindings is allowed, at the top of
the entry body or inside a dispatch arm (the placed-dispatch path:
recursive arms are placed independently, direct arms are promoted — their
results are first-order). Everything else live must be consumed or
dropped before the loops; the continuation may use only the loop results.
Every bound and input expression is closed. The bound is a `Nat`
expression, while map/iteration/while steps are directly compilable
non-recursive named definitions. A mapper has type `A -> B`; map
preserves ordinary list order. A fold step has type
`Accumulator * Element -> Accumulator`; the closed input has type `List Element`.
The current useful list literal is `Text`, or `List Nat`, so
`fold "ABC" from 0 with natAdd` is representative. A while test has type
`T -> Unit + Unit`: `left ()` stops and `right ()` takes a step, up to the bound.

The reusable affine-recursion slice also accepts a named helper whose
fuel or list input is open, provided its seed is closed and no unboxed context
remains live after the loop:

```text
repeat : Nat -o Nat = \n -> iterate n from 0 with increment
mapIncrement : List Nat -o List Nat = \values -> map values with increment
listLength : List Nat -o Nat = \values -> fold values from 0 with countListElement
```

Calls are retained at source level until these helpers are placed as
`Lift Input -> Bang (Lift Output)`. The controller remains affine at
orchestration level, the seed is introduced only by `BoxValS`, and the
post-loop continuation runs under `BoxS`. Open seeds and attempts to combine a
boxed result with a surviving unboxed value are rejected; nested recursion and
general multi-level placement remain unavailable.

Compilation emits actual `MapS`, `IterS`, `FoldS`, or `WhileS`
nodes, combines independent boxed results with `MergeS`, and applies one `BoxS`
to the closed final continuation. It never unboxes a loop result. Captured
inputs/seeds, captured entry arguments, nested recursion, recursive
mapper/step/test bodies, and definition cycles are rejected rather than promoted
from an open context.

Compiled entries carry an existential decorated core result, its `STy`, and an
explicit proof that `Strip` equals the source result type. The runner converts
and compares values structurally through that singleton; value equality is not
used as a type coercion. Surface/core and value/grade/fuel parity checks remain
active for recursive entries.

`Telomare.Ops` provides equation-free `*Ops` capability classes for category,
tensor, affine, sums, distributivity, Nat, List, guard, restricted Bang,
exceptional Nat/Bang copying, and bounded recursion operations. Instances expose
only constructors actually supported by `UMorph` or `Morph`; in particular the
core is not advertised as cartesian, closed, or a comonad.

`Telomare.Compiler.Closed` is the shared typed implementation of the formulas in
`T3.Compiler.ClosedRecursion`. It directly compiles each closed seed, fold input,
step, test, and continuation, then constructs the real `BoxValS`, `IterS`,
`MapS`, `FoldS`, `WhileS`, `MergeS`, and `BoxS` nodes. It does not route recursive
`UMorph` through `compileDirect`, promote an open context, or insert dereliction.
Its affine-controller variants accept an open fuel or list morphism while still
requiring a closed seed. `Telomare.Tel2` supplies the checked components.

`Telomare.Linear` is a smaller Haskell `LinearTypes` frontend. Its closed `Host`
family represents `()`, `Natural`, products, `Either`, and lists. Abstract
`Wire s a b` circuits are reified only through a rank-2 `Circuit a b`; no host
value, wire constructor, `Bang` source type, or unsafe coercion is exposed.
Composition, tensor, affine discard, sums, and Nat/List primitives map directly
to `UMorph` and ordinary `compile` remains the placement-free `compileDirect`
path.
`branch` accepts separately rank-2 branches, preventing either branch from
capturing a wire in the caller's live scope. Copying requires an explicit
`Copy` witness, available only for unit, Nat, and products of copyable values;
product copying expands to structural wiring and primitive Nat duplication.

This API enforces exactly-once use only for variables bound with a `%1` arrow.
GHC still permits unrestricted top-level circuit definitions to be referenced
multiple times, so the frontend does not claim that `LinearTypes` turns Haskell
itself into an affine language. It is intentionally point-free. Its separate
`closedIter`, `closedFold`, and `closedWhile` API takes only rank-2 closed
`Circuit` descriptions and returns an abstract, typed `Closed` decorated core
result. `HostType` supplies while's size witness without adding `Bang` to
`Host`; `closedCore` permits typed core inspection.

`*` and `+` associate to the right. `Text` is `List Nat`; `Reply S` is
`Text * (Unit + S)`. A `data` declaration is a finite nullary enum represented
by distinct natural tags. Constructor cases must be exhaustive, cannot repeat
constructors, and cannot mix constructors from different declarations. Nominal
enum separation is not yet retained after representation erasure. Exact Nat/Text
matches have an explicit final fallback pattern.
`prepend "literal" text` is finite text construction, not unrestricted list
append. `succ n` and `add (m,n)` elaborate directly to the existing `USuc` and
`UAdd` surface constructors, then to `SucS` and `AddS`; neither operation uses
host arithmetic semantics.

Every executable file declares a `main` entry (with `type State = ...`
defaulting to `Nat`); the machine's `init`/`step` pair is synthesized:

```text
main : Text * State -o Reply State = \request -> ...
start : Unit -o State = \u -> ...        -- required unless State is Nat
```

Affinity is the default costing discipline, not a prohibition. Reusing a
first-order variable just works: the elaborator threads a demand set, a
demanded lookup leaves the binding behind a priced copy (core `CopyS`,
charged the value's full size in the duplication grade), and the last use
consumes it. Every reuse is charged exactly once per extra use per
execution path; nothing data-shaped is duplicated for free. Explicit
`copy e` remains supported at every first-order type through the same
priced path. Closures are the exception: a function value is applied at
most once, and neither implicit nor explicit copying of a closure is
accepted — reuse of code is the modality's business (a reusable closure
is a `Bang`-promoted closed closure, as `mapc` requires). Failed literal
matches reconstruct the consumed value and pass it to the next arm.

A lambda's free variables are consumed from the ambient context into the
closure environment (captures interact with implicit copy like any other
use). Application synthesizes the function type from variable and
definition-call heads; other heads need an annotated `let`. Machine
`State` must remain first-order: closures cannot cross the machine
boundary.

`stdlib/Prelude.tel2` is an ordinary packaged importable module, not
compiler policy. It defines finite `Bool`, total boolean combinators, Bool/Nat
conversions and predicates, primitive-backed Nat addition, successor, doubling,
reusable `listLength`/`listSum` folds, and the order-preserving `mapIncrement`
specialization. `stdlib/LegacyPrelude.tel2` exposes only
six honest monomorphic/modernized historical names. The complete 50-binding
historical inventory and rationale is `design/PRELUDE_MIGRATION.md`.

`test/programs/tictactoe.tel2` explicitly imports Prelude and now uses both
`otherPlayer` and `natIsZero`; board and state reuse is implicit and priced.
The game's board is an ordinary nine-Nat product. Moves go through cell
lenses (`Nat * (Nat -o Board)`) handled by one shared `moveAt`, and one
`cellText` renderer takes per-square label/separator closures — the game is
the working demonstration of first-class functions over data. Line checks,
tie detection, turn changes, invalid input, and termination are all named
`.tel2` definitions. The compiler has no corresponding built-ins.
The fixed product scans remain direct: replacing them with a recursive fold
would require retaining an unboxed state copy after the boxed fold result, which
the current placement boundary intentionally rejects.

`test/programs/examples.tel2` imports both Prelude modules and independently runs
closed iteration, text folding, and bounded while. It explicitly copies the
iteration result and uses the legacy `dPlus` alias backed by primitive `AddS`.
The exact checked results are 5, 198, 3, and 15; initialization costs 21 formal
work units. Its compiled entry has nonzero depth and contains `IterS`, `FoldS`,
`WhileS`, and `AddS`.

## Formal Boundary

`spec/Everything.agda` checks under `--safe` with no postulates.
`T3.Bound` proves certified static work and duplication bounds. `costW` and
`costD` interpret `T3.Abstract` shapes, including closure body costs; the
type-sensitive `sizeS` bounds value words for copy and probe charges.
`costW-sound` and `costD-sound` prove every covered run stays below the
corresponding bound. With adequacy, a static work bound is a machine fuel
bound. Arbitrary-input duplication is necessarily unbounded when it depends on
an unrestricted list size; input-shape refinements can recover finite caps.
Certified space remains future work pending a precise decision on whether the
current graded `spaceAlg` denotes streaming-local peak or total live memory. The formal
surface/core bridge proves successful direct elaboration erases to its source
and preserves value semantics. `T3.Categorical.Vocabulary` separates operation
capabilities from law records; `T3.Categorical.Interpretation` bundles the raw
syntaxes without quotient claims and proves category laws only under explicit
value-extensional hom equality. `T3.Compiler.ClosedRecursion` defines the closed
`BoxValS`/`MapS`/`IterS`/`FoldS`/`WhileS`/`BoxS` translations from direct-compiled
components, proves that each erases to its corresponding surface composite, and
derives value preservation through `ε-factor`. It also proves the erasure and
value theorem for one `MergeS` combining two independent boxed results; repeated
application covers the right-associated environment used by the Haskell slice.
`T3.Compiler.Partition` proves that generic Nat literal partition reconstructs
its input. `T3.Source.Affine` formalizes the central variable,
weakening/splitting, product, let, explicit-copy, and sum-case resource rules.

The Haskell parser, alias expansion, closed/free-variable recognition, and
complete pointful elaborator are not proved equivalent to those Agda judgments.
The closed-recursion theorem assumes direct compilation evidence for every
seed, input, body/test, and continuation; it does not claim that Megaparsec or
the Haskell validator produces that evidence. Tests cover parser, type, affine and
copy errors, forward references, definition and import cycles, missing modules,
Prelude dependency, Bool helpers, reusable runtime-list map/fold specializations,
exact primitive addition, accepted `MapS`/`IterS`/`FoldS`/`WhileS` behavior,
exact modal shape, depth and work,
linear/Tel2 closed-loop value and erasure parity, actual `AddS` emission,
illegal captures/placement, source mutation, old grammar rejection, all game
transcripts, and runtime `UMorph`/core parity. These are regression evidence, not
a parser proof.

## Limits

- Modules expose an unqualified global namespace; there are no selective,
  qualified, or package imports.
- No polymorphism or general type inference; `apply` heads are limited to
  variables and definition calls. No general recursion.
- Closures are affine (applied at most once); reusable closures exist only
  behind `Bang` via empty-context promotion of closed closures, reached
  from source through `mapc`. There is no dereliction or digging.
- Source recursion supports independent closed whole-entry loops and reusable
  first-order helpers with an affine runtime fuel/list controller and closed
  seed. Open seeds, live unboxed values after a loop, nested/dependent loops,
  recursive helper chains, and general multi-level placement are not implemented.
- Nullary finite enums only; records are represented by named product aliases
  and tuple patterns.
- Products, sums, Nat, Text, and List types are present, with affine `[]`/`cons`,
  first-order map and left fold, but no general structural recursion or arbitrary
  text append.
- Enum cases check constructor coverage, but nominal enum separation is not yet
  retained after enums erase to Nat during elaboration.
- Multi-level modal placement remains unavailable; a `mapc` mapper must
  select among closed lambdas.
- The linear Haskell frontend is point-free; it has no host-value escape or
  general linear lambda elaborator, and GHC top-level bindings remain
  unrestricted.
- The core, direct-compiler, and closed-recursion categorical proofs apply to
  generated `Morph`; the parser, closure checks, and complete source elaborator
  remain at the explicit proof boundary above.

## Core transport

`Telomare.Transport` defines schema version 4, a backend-neutral first-order
tree with an explicit `TyCode` (including `Bang` and `Lolly`) and one tag per
current `Morph` constructor; closure values are never transported, only
morphisms are. `exportMorph` requires endpoint singletons because a bare
polymorphic GADT value does not retain them; `CoreEntry` and `Program` already
retain enough existential witnesses and can be exported directly. Program
transport contains the state type and compiled initial/step entries, not the
surface evaluator terms.

The stable wire form is the explicit S-expression produced by
`renderArtifact`, for example `(morph 2 nat nat (suc))`; derived `Show` is not a
wire protocol. Parsed or externally constructed values are untrusted until
`validateArtifact` succeeds. Validation independently infers and unifies the
untyped tree's constructor types, including polymorphic structural nodes,
composition intermediates, modal inputs, and recursion bodies. It returns an
opaque `ValidatedArtifact`; it intentionally does not reconstruct trusted
`Morph` and uses no unchecked cast.

```sh
cabal run telomare -- --emit-transport init test/programs/examples.tel2 \
  > init.transport
```

## Checks

```sh
cabal build all
cabal test telomare-test --test-show-details=direct
(cd spec && agda --safe Everything.agda)
nix flake check
nix run .#format-lint
git diff --check
```

## License

Apache-2.0. See `LICENSE`.
