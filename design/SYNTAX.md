# Tel2 Surface Syntax Convergence with Telomare0

Standing objective: tel2 surface syntax converges on telomare0 (the original
`.tel` language preserved on `master` and frozen on-branch as
`src/Telomare/Compat/Parser.hs`) wherever the resource model permits.
Resource-model syntax — structural types, `-o`, `copy`, `data`/`type`
declarations, and the bounded-loop keywords — is tel2's own and stays.

All surface syntax lives in `src/Telomare/Tel2.hs` (lexer, parser, affine
elaborator). Every convergence feature below is a parser-level desugaring into
the existing `Expr` AST unless noted; affine/demand accounting is inherited from
the desugaring targets.

## Mapping table

| telomare0 (`master`) | tel2 today | Plan |
|---|---|---|
| `-- line` and `{- block -}` comments | `# line` | S1: accept both `--` and `#`; nested `{- -}`. `--` preferred in docs. |
| `if c then t else e` (0 = false) | `matchNat c of { 0 -> e; _ -> t }` | S1: sugar to that `matchNat`. Sound for `Nat` and for `data` enums (tags are declaration-ordered, so `False` = 0). |
| `[e1, e2, …]` list literals | `cons e1 onto cons e2 onto []` | S1: sugar to nested `cons`/`[]`. |
| `\x y -> b` multi-arg lambdas | `\x -> …` single-arg only | S1: sugar to nested lambdas (curried; `-o` is right-associative, application is one argument at a time). |
| `let a = e1; b = e2 in body` multi-binding | single typed binding per `let` | S1: multi-binding sugar to nested `let` (`;`-separated, no layout). S3: type annotations optional where the bound value's type is synthesizable. |
| `f x y` juxtaposition application | `f(x)`, `apply(f, x)` | S2: application chains `f x y`; head resolves to a def call or closure apply during elaboration. Legacy forms stay valid. |
| `main` entry taking/returning `(Text, State)`; halt when next state is 0 | `init`/`step` ABI with `Reply State = (Text, Unit + State)` | S4: accept `def main(input: Text * State): Text * State` when `init`/`step` are absent; synthesize both, translating state 0 into `left ()`. |
| `$n` church numerals | numeric literals are `Nat` | Not planned: tel2 numerals are not church-encoded; plain literals cover the use. |
| `left e` / `right e` are **pair projections** | `left e` / `right e` are **sum injections** | **Deliberate divergence — kept.** See below. |

## The `left`/`right` divergence (read this)

In telomare0, `left`/`right` project the components of a pair. In tel2 they are
the injections of a sum type `A + B`. Tel2 keeps its meaning: pairs are consumed
by `let (a, b) = p in …` patterns (affine consumption is explicit), and sums
need their injections. A telomare0 program using `left p` to mean `fst p` must
be rewritten to a tuple `let`. This is the one place the same source text is
valid in both languages with different meanings.

## Feature notes

### S1 details

- Comments: `spaceConsumer` accepts `--` and `#` line comments plus nested
  `{- -}` blocks. `-o` does not clash: `--` requires the second dash.
- `if`: scrutinee is unavailable in the branches (as in telomare0); the
  discarded default pattern is affine-legal. `else` branch is the `0` arm.
- List literals type-check exactly like the `cons` chains they produce.
- Multi-arg lambda produces nested unary closures, **not** a tuple parameter:
  `\x y -> b : A -o B -o C`. Consuming one today requires binding each partial
  application (`apply` heads must be variables or calls until M5's apply-head
  synthesis): `let g: B -o C = apply(f, a) in apply(g, b)`.

### S2 details

- New AST node `EApp` with elaborator dispatch: head that names a definition
  (and is not shadowed by a local binding) compiles as a call; anything else
  synthesizes a closure and applies. Applying an enum constructor is an error
  (constructors are payload-free).
- Reserved words are excluded from identifiers so `let a = f x in …` does not
  consume `in` as an argument.

### S4 details and limits

- Only fires when neither `init` nor `step` is declared; declaring `main`
  alongside them is an error.
- State is Nat-encoded (`type State = Nat;` is implied if undeclared); halting
  is `next state == 0`, priced honestly through the `matchNat` on the state.
- First input of a session is the empty string, matching the CLI loop.

## Status

| Stage | Feature | Status |
|---|---|---|
| S1 | comments, `if`, list literals, multi-arg λ, multi-`let` | **done** |
| S2 | juxtaposition application | planned |
| S3 | optional `let` annotations | planned |
| S4 | `main` entry sugar | planned |
