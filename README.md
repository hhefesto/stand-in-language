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
single .tel2 file
  -> Megaparsec syntax tree
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
String escapes are Haskell-style. Definitions are ordered, first-order,
monomorphic, non-recursive, and take exactly one argument.

```text
program   ::= declaration*
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

`*` and `+` associate to the right. `Text` is `List Nat`; `Reply S` is
`Text * (Unit + S)`. A `data` declaration is a finite nullary enum represented
by distinct natural tags. Constructor cases must be exhaustive, cannot repeat
constructors, and cannot mix constructors from different declarations. Nominal
enum separation is not yet retained after representation erasure. Exact Nat/Text
matches have an explicit final fallback pattern.
`prepend "literal" text` is finite text construction, not unrestricted list
append.

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

`test/programs/tictactoe.tel2` is a complete program in this grammar. Its board
is an ordinary nine-Nat product. Move selection, occupancy, eight line checks,
tie detection, turn changes, rendering, invalid input, and termination are all
named `.tel2` definitions. The compiler has no corresponding built-ins.

## Formal Boundary

`spec/Everything.agda` checks under `--safe` with no postulates. The formal
surface/core bridge proves successful direct elaboration erases to its source
and preserves value semantics. `T3.Compiler.Partition` proves that generic Nat
literal partition reconstructs its input. `T3.Source.Affine` formalizes the
central variable, weakening/splitting, product, let, explicit-copy, and sum-case
resource rules.

The Haskell parser, alias expansion, and complete pointful elaborator are not
proved equivalent to that Agda judgment. Tests cover parser, type, affine and
copy errors, source mutation, old grammar rejection, all game transcripts, and
runtime `UMorph`/core parity. These are regression evidence, not a parser proof.

## Limits

- One source file; no modules, polymorphism, inference, recursion, or functions
  as values.
- Nullary finite enums only; records are represented by named product aliases
  and tuple patterns.
- Products, sums, Nat, Text, and List types are present, but this syntax slice
  has no general list recursion or arbitrary text append.
- Enum cases check constructor coverage, but nominal enum separation is not yet
  retained after enums erase to Nat during elaboration.
- General sum/list copying and modal placement remain unavailable.
- The core and direct-compiler proofs apply to generated `Morph`; the parser and
  complete source elaborator currently have the explicit proof boundary above.

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
