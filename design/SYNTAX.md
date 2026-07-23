# Tel2 Surface Syntax Convergence with Telomare0

Standing objective: tel2 surface syntax converges on telomare0 (the original
`.tel` language preserved on `master` and frozen on-branch as
`src/Telomare/Compat/Parser.hs`) wherever the resource model permits, and the
convergent syntax is the ONLY syntax. Resource-model syntax — structural
types, `-o`, `copy`, `data`/`type` declarations, and the bounded-loop
keywords — is tel2's own and stays.

All surface syntax lives in `src/Telomare/Tel2.hs` (lexer, parser, affine
elaborator). Round 1 (S1–S4, 2026-07-21) and round 2 (S5–S8 plus the
main-only entry, 2026-07-22) are both complete; each round removed the
legacy forms it superseded.

## Mapping table

| telomare0 (`master`) | tel2 | Status |
|---|---|---|
| `-- line` and `{- block -}` comments | same | Done (2026-07-21); `#` removed. |
| `if c then t else e` (0 = false) | same, desugars to a nat case | Done (S1). |
| `[e1, e2, …]` list literals | same, desugar to `cons`/`[]` | Done (S1). |
| `\x y -> b` multi-arg lambdas, pattern lambdas | same (curried; tuple patterns destructure) | Done (S1/S5). |
| multi-binding `let` | same, layout-separated | Done (S1/S7). |
| `f x y` juxtaposition application | same; the ONLY application form | Done (2026-07-21; `apply` and `f(x)` production removed). |
| `name = \x -> body` top level, optional `name : check = e` | `name : A -o B = \x -> body` — the mandatory type sits in telomare0's refinement position | **Done (S5, 2026-07-22)**; the `def` keyword is removed. |
| one `case e of` with int/string/var/`_` patterns | one `case e of`; the first arm's shape picks nat/text/enum dispatch | **Done (S6, 2026-07-22)**; `matchNat`/`matchText` keywords are removed. |
| layout: no `;`, no braces, aligned bindings/arms, line-folded application | same | **Done (S7, 2026-07-22)**; semicolons and braced arm blocks are removed. |
| `succ`, `dPlus`, `concat` are Prelude functions | `succ`, `add`, `cons`, `prepend` are builtin functions applied by juxtaposition, shadowable like any name | **Done (S8, 2026-07-22)**; the `suc`/`add`/`cons…onto`/`prepend` keyword forms are removed. |
| `main = \input -> …`, state 0 fresh, next state 0 halts | `main` is the ONLY entry: telomare0-exact Nat shape, or `main : Text * State -o Reply State` with `start : Unit -o State` for any first-order state | **Done (2026-07-22)**; direct `init`/`step` declarations are an error. |
| `$n` church numerals | numeric literals are `Nat` | Not planned. |
| `{ base, \recur x -> …, stop }` recursion triples | bounded loops (`iterate`/`fold`/`while`/`mapc`/`iterc`/`foldc`/`whilec`) | **Deliberate divergence** — the bounded loops are the point of tel2. |
| `left e` / `right e` are **pair projections** | **sum injections** | **Deliberate divergence — kept.** See below. |
| `x : check` runtime refinements | `x : T` static types (same surface shape after S5) | **Deliberate divergence** — tel2's types are the resource model. |
| `abort`/`assert` | none: bounds are static | **Deliberate divergence.** |
| `[a, b] = e` list assignment, `import qualified … as` | none | Not planned (niche). |

## The `left`/`right` divergence (read this)

In telomare0, `left`/`right` project the components of a pair. In tel2 they are
the injections of a sum type `A + B`. Tel2 keeps its meaning: pairs are consumed
by `let (a, b) = p in …` patterns (affine consumption is explicit), and sums
need their injections. A telomare0 program using `left p` to mean `fst p` must
be rewritten to a tuple `let`. This is the one place the same source text is
valid in both languages with different meanings.

## Feature notes

### S5 — top-level definitions

`name : A -o B = \x -> body`. The type must be an arrow and the body a
lambda; the first lambda pattern becomes the definition argument (tuple
patterns destructure through a generated argument, as telomare0's
`buildMultiLambda` does), and any further lambda patterns stay in the body
as a closure result. Non-lambda right-hand sides are rejected — bind
constants in a `let`.

### S6 — the unified `case`

The first arm's shape picks the dispatch: string literals match text and
nat literals match naturals (both keep tel2's binding default arm — the
binder receives the scrutinee), constructor tags eliminate a `data` enum
exhaustively with no default. A case with only a default arm is rejected.
`if/then/else` still desugars to the nat form.

### S7 — layout

Modeled on the Compat parser: tokens consume only within-line space, and
newlines are consumed at explicit layout points. Application is a line
fold (arguments continue only when indented past the head — this is what
ends a declaration body at the next column-1 declaration); `let` bindings
separate by line; `case` arms align at one column and the block ends at
the first outdented token; nested cases at different columns nest
correctly. `module X` / `import X` take no terminator.

### S8 — builtin functions

`succ n`, `add (a, b)`, `cons x xs`, `prepend "lit" t` resolve during
application resolution when the name is not shadowed by a local binding
or a definition — lexical scope wins, as for every juxtaposition head.
`prepend`'s first argument must be a text literal (it is compiled
statically). `copy` and the loop keywords remain keywords: they are the
resource model. LegacyPrelude no longer defines `succ` — the builtin is
already telomare0's spelling, and a def would capture the name for every
importing module.

### The main-only entry

`expandMain` synthesizes the machine's `init`/`step` from `main`;
declaring them directly is an error. Two shapes, picked by main's
declared type:

- `main : Text * State -o Text * State` with `State` = `Nat`
  (telomare0-exact): first run gets an empty input and state `0`; the
  machine halts when the returned state is `0` (priced halt test).
- `main : Text * State -o Reply State` (general): works for any
  first-order `State`; the fresh state comes from `start : Unit -o State`
  (defaulted to `0` when `State` is `Nat`), freshness is encoded in the
  state by the program itself — exactly telomare0's `boardIn` zero test —
  and halting is main's own `left ()`.

The enabler is **placed dispatch** (`compilePlacedBody`): a match whose
arms contain recursion compiles by dispatching directly, placing each
recursive arm on its own (a chain of closed loop bindings reuses the
whole-entry bindings-and-merge path), and promoting direct arms through
the certified `PromoteS` (entry results are Ground, so promotion is free
in work and duplication and adds no depth). No new core constructors were
added, so every certified bound covers the compiled result unchanged.
Consequence: a single-entry program's certificate merges what used to be
separate init/step bounds (both entries route through `main`), so init's
bounds now match step's.

## Status

| Stage | Feature | Status |
|---|---|---|
| S1 | comments, `if`, list literals, multi-arg λ, multi-`let` | **done** (2026-07-21) |
| S2 | juxtaposition application | **done** (2026-07-21) |
| S3 | optional `let` annotations | **done** (2026-07-21) |
| S4 | `main` entry sugar (Nat shape) | **done** (2026-07-21) |
| S5 | signature-style top level, `def` removed | **done** (2026-07-22) |
| S6 | unified `case`, `matchNat`/`matchText` removed | **done** (2026-07-22) |
| S7 | layout, semicolons and braces removed | **done** (2026-07-22) |
| S8 | builtin `succ`/`add`/`cons`/`prepend`, keywords removed | **done** (2026-07-22) |
| — | main-only entry, general `Reply` shape, placed dispatch | **done** (2026-07-22) |
