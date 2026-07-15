# Telomare

Telomare is a total-language experiment with a machine-checked affine core,
graded resource semantics, and a small general-purpose typed `.tel2` language.

## Run

```sh
nix run . -- test/programs/tictactoe.tel2
# or, in nix develop:
cabal run telomare -- test/programs/tictactoe.tel2
```

`--certificate` prints core depth, `--meter` prints accumulated formal core
work, and `--max-work N` bounds that work. The executable accepts `.tel2` only.

## Active Pipeline

```text
entry .tel2 module + filesystem imports
  -> Megaparsec syntax tree
  -> module graph + definition dependency ordering
  -> name/type checking + affine context elaboration
  -> existentially typed UMorph init and step
  -> compileDirect
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

Whitespace and `#` line comments are ignored. Identifiers start with a letter.
String escapes are Haskell-style. Module files begin with a header; imports
precede declarations. Definitions are first-order, monomorphic, and take exactly
one argument. They may refer to definitions or type aliases declared later.
Definition bodies are compiled in dependency order; dependency cycles are
rejected. A restricted bounded iteration is the only source recursion currently
accepted.

```text
program   ::= ("module" ID ";")? ("import" ID ";")* declaration*
declaration
          ::= "type" ID "=" type ";"
           |  "data" ID "=" ID ("|" ID)* ";"
           |  "def" ID "(" ID ":" type ")" ":" type "=" expr ";"

type      ::= atom ("*" type)?
           |  product ("+" type)?
atom      ::= "Unit" | "Nat" | "Text" | ID
           |  "List" atom | "Reply" atom | "(" type ")"

expr      ::= ID | NAT | STRING | "()" | CONSTRUCTOR
           |  "(" expr "," expr ("," expr)* ")"
           |  ID "(" expr ")"
           |  "let" pattern ":" type "=" expr "in" expr
           |  "copy" expr
           |  "suc" expr
           |  "add" expr
           |  "iterate" NAT "from" expr "with" ID
           |  "fold" expr "from" expr "with" ID
           |  "while" NAT "from" expr "testing" ID "stepping" ID
           |  "prepend" STRING expr
           |  "left" expr | "right" expr
           |  "matchNat" expr "of" "{" natArm* pattern "->" expr ";"? "}"
           |  "matchText" expr "of" "{" textArm* pattern "->" expr ";"? "}"
           |  "case" expr "of" "{" constructorArm+ "}"

pattern   ::= ID | "_" | "(" ID ("," ID)+ ")"
natArm    ::= NAT "->" expr ";"
textArm   ::= STRING "->" expr ";"
constructorArm ::= CONSTRUCTOR "->" expr ";"?
```

The CLI requires a module header. `import Foo;` first checks `Foo.tel2` beside
the entry file, then asks Cabal for packaged `stdlib/Foo.tel2` data. A present
sibling deliberately shadows the stdlib and remains authoritative even if its
header is invalid; imports never silently fall through after selecting it. The
selected file's header must be `module Foo;`. Imports are transitive, diamond
imports are loaded once, and cycles or missing modules are errors. Packaged
stdlib resolution is independent of the process working directory.
`compileTel2` remains a pure entrypoint for anonymous, import-free source used by
small tests; `compileTel2File` is the module-aware IO entrypoint used by the CLI.
Imported declarations currently share one unqualified namespace.

Closed recursion is accepted only as a prefix of whole-entry bindings:

```text
def init(u: Unit): Reply State =
  let i: T = iterate N from closedSeed with iterStep in
  let f: A = fold closedList from closedAccumulator with foldStep in
  let w: W = while N from closedSeed testing test stepping whileStep in
  closedResultUsingOnlyIAndFAndW;
```

Any nonempty subset and order of these bindings is allowed for `init` or `step`,
but the entry input must be weakened. Every bound and input expression is closed;
`N` is a literal. Iteration and while steps are directly compilable
non-recursive `T -> T` definitions. A fold step has type
`Accumulator * Element -> Accumulator`; the closed input has type `List Element`.
The current useful list literal is `Text`, or `List Nat`, so
`fold "ABC" from 0 with natAdd` is representative. A while test has type
`T -> Unit + Unit`: `left ()` stops and `right ()` takes a step, up to the literal
cap.

Compilation emits `BoxValS` for every seed, actual `IterS`, `FoldS`, or `WhileS`
nodes, combines independent boxed results with `MergeS`, and applies one `BoxS`
to the closed final continuation. It never unboxes a loop result. Captured
inputs/seeds, captured entry arguments, nested recursion, recursion in helpers,
and recursive definition cycles are rejected rather than promoted from an open
context.

Compiled entries carry an existential decorated core result, its `STy`, and an
explicit proof that `Strip` equals the source result type. The runner converts
and compares values structurally through that singleton; value equality is not
used as a type coercion. Surface/core and value/grade/fuel parity checks remain
active for recursive entries.

`*` and `+` associate to the right. `Text` is `List Nat`; `Reply S` is
`Text * (Unit + S)`. A `data` declaration is a finite nullary enum represented
by distinct natural tags. Constructor cases must be exhaustive, cannot repeat
constructors, and cannot mix constructors from different declarations. Nominal
enum separation is not yet retained after representation erasure. Exact Nat/Text
matches have an explicit final fallback pattern.
`prepend "literal" text` is finite text construction, not unrestricted list
append. `suc n` and `add (m,n)` elaborate directly to the existing `USuc` and
`UAdd` surface constructors, then to `SucS` and `AddS`; neither operation uses
host arithmetic semantics.

Every executable file declares `type State = ...` and these definitions:

```text
def init(u: Unit): Reply State = ...;
def step(x: Text * State): Reply State = ...;
```

Variables are affine. Looking up a variable removes it from the context;
weakening is allowed, but writing a variable twice is a type error. `copy e` is
the only contraction syntax and is accepted for `Unit`, `Nat`, and products of
copyable components. It elaborates product copying from `UDup SUNat` plus
structural morphisms, so `compileDirect` reaches `DupNatS`; it does not invoke
general `UDup` or implicit host copying. Failed literal matches reconstruct the
consumed value and pass it to the next arm.

`stdlib/Prelude.tel2` is an ordinary packaged non-recursive importable module, not
compiler policy. It defines finite `Bool`, total boolean combinators, Bool/Nat
conversions and predicates, primitive-backed Nat addition, successor, doubling,
and small application helpers. `stdlib/LegacyPrelude.tel2` exposes only
six honest monomorphic/modernized historical names. The complete 50-binding
historical inventory and rationale is `design/PRELUDE_MIGRATION.md`.

`test/programs/tictactoe.tel2` explicitly imports Prelude and now uses both
`otherPlayer` and `natIsZero`. The game's board is an ordinary nine-Nat product.
Move selection, occupancy, eight line checks,
tie detection, turn changes, rendering, invalid input, and termination are all
named `.tel2` definitions. The compiler has no corresponding built-ins.

`test/programs/examples.tel2` imports both Prelude modules and independently runs
closed iteration, text folding, and bounded while. It explicitly copies the
iteration result and uses the legacy `dPlus` alias backed by primitive `AddS`.
The exact checked results are 5, 198, 3, and 15; initialization costs 21 formal
work units. Its compiled entry has nonzero depth and contains `IterS`, `FoldS`,
`WhileS`, and `AddS`.

## Formal Boundary

`spec/Everything.agda` checks under `--safe` with no postulates. The formal
surface/core bridge proves successful direct elaboration erases to its source
and preserves value semantics. `T3.Compiler.ClosedRecursion` defines the closed
`BoxValS`/`IterS`/`FoldS`/`WhileS`/`BoxS` translations from direct-compiled
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
Prelude dependency, Bool helpers, exact primitive addition, accepted
`IterS`/`FoldS`/`WhileS` behavior, shape, depth and work, actual `AddS` emission,
illegal captures/placement, source mutation, old grammar rejection, all game
transcripts, and runtime `UMorph`/core parity. These are regression evidence, not
a parser proof.

## Limits

- Modules expose an unqualified global namespace; there are no selective,
  qualified, or package imports.
- No polymorphism, inference, general recursion, or functions as values.
- Source recursion is limited to independent closed whole-entry iteration, fold,
  and literal-capped while bindings. Dynamic bounds, nested/dependent loops,
  recursive helpers, and general modal placement are not implemented.
- Nullary finite enums only; records are represented by named product aliases
  and tuple patterns.
- Products, sums, Nat, Text, and List types are present, but this syntax slice
  has no general list recursion or arbitrary text append.
- Enum cases check constructor coverage, but nominal enum separation is not yet
  retained after enums erase to Nat during elaboration.
- General sum/list copying and modal placement remain unavailable.
- The core, direct-compiler, and closed-recursion categorical proofs apply to
  generated `Morph`; the parser, closure checks, and complete source elaborator
  remain at the explicit proof boundary above.

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
