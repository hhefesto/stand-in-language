# Telomare: The Type Story

Telomare is a language experiment about making computation executable without
making resource behavior mysterious. Its core claim is simple: a program should
not only compute a value; it should also expose enough structure to explain how
much work, copying, placement depth, and recursion budget it needs.

The active executable and formal layers are:

```text
.tel2 finite-machine source
  -> Morph Unit Reply + Morph (Text * State) Reply
  -> evalV / evalG / evalK
  -> host I/O driver

UMorph a b
  -> evalU
  -> compileDirect
  -> Morph (Lift a) (Lift b)
  -> graded work / duplication / fuel execution
  -> placement skeletons
  -> abstract recursion budgets
```

`UMorph` is the typed box-free formal surface, and `Morph` is the typed
resource-aware core. The current `.tel2` finite-machine frontend targets a small
affine `Morph` fragment directly. There is not yet a pointful `.tel2 -> UMorph`
frontend or a general placement pass, so this document keeps those boundaries
explicit.

The first part of that future bridge exists independently of `.tel2` parsing:
Haskell mirrors the formal box-free `UMorph` surface category and directly
elaborates its affine fragment to `Morph`. The compiler accepts ordinary
structure, data operations, guards, and natural duplication. It explicitly
rejects general duplication and recursion until modal placement is implemented.
Agda proves that every successful direct elaboration erases to its source term
and preserves value semantics.

This subset uses named finite states and exact text rules. It is not a filename
builtin and has no compatibility fallback; the tic-tac-toe source contains all
reachable states and transitions. Affine partition morphisms reconstruct failed
keys rather than copying them implicitly. Its generated transition table is an
extensional normal form for this first milestone, not the final pointful syntax.

That normal form is intentionally denotational. A deterministic finite machine
is a total function from input and state to output and optional next state. The
source lists the graph of that function, and `compileMachine` interprets the
graph compositionally into core sums, products, constants, and observations.
There is no separate source evaluator and no Haskell transition function in the
runtime.

EAL remains useful even though tic-tac-toe needs no recursion or boxes. Dispatch
is affine, failed comparisons reconstruct their consumed values, and the linear
search cost appears in the formal work grade. Explicit reusable copying is a
separate witnessed algebra in `T3.Core.Copyable` and `Telomare.Copyable`; it is
not implicit variable reuse.

## The Executable Path

The executable accepts a `.tel2` file and ends with an interactive transcript.

```haskell
compileMachine :: String -> Either MachineError Machine
runMachineIO   :: Maybe Natural -> Bool -> Machine -> IO (Either String ())
```

`compileMachine` resolves source declarations into typed initialization and step
`Morph` values. `runMachineIO` transports text and state values while all
transition behavior remains in those morphisms.

The CLI options line up with that path:

- `--certificate` prints the typed machine and core-depth summary.
- `--meter` prints accumulated formal work.
- `--max-work N` caps formal work across the interaction.

Supplying a historical `.tel` file is an error. The compatibility implementation
is retained temporarily for regression comparison, not as an executable fallback.

## Archived `.tel` Syntax

The parser produces located syntax:

```haskell
type AUPT = Cofree (UnprocessedParsedTermF PatternA) LocTag

newtype AnnotatedUPT = AnnotatedUPT
  { unAnnotatedUPT :: AUPT }
```

Each node carries a `LocTag`. Source locations contain file, line, column, and
offset information. This is why the meter can now print recursion sites like
`tictactoe.tel:42:7` instead of exposing an internal record constructor.

The surface syntax includes:

- integers, strings, lists, and pairs;
- lambda abstraction and application;
- `let` bindings;
- `if` and `case` forms;
- refinement checks;
- imports;
- unsized recursion triples of the shape `{ test, step, base }`.

The parser is not a tiny parser followed by a separate elaborator. It already
performs important desugaring. Pattern lambdas, list assignments, user-data
helpers, and some case forms become lower-level syntax before the resolver sees
them.

## Resolution

The compatibility resolver turns located surface syntax into older machine-like
terms in stages:

```text
AUPT
  -> Term1
  -> Term2
  -> Term3
```

The key types are:

```haskell
type Term1 = Cofree (ParserTermF (LamType String) String) LocTag
type Term2 = Cofree (ParserTermF (LamType ()) Int) LocTag
type Term3 = Cofree Term3F LocTag
```

`Term1` has resolved names and lambda openness. `Term2` replaces names with
De Bruijn indices. `Term3` is the environment-machine representation used by
the runtime lowering pass.

Two resolver tracks currently exist:

```text
main2Term3    -> type-checking term
main2Term3let -> executable term
```

The first is checked by the compatibility type checker. The second is lowered to
`TelExpr` and run. This split is historical and important: the formal core
proofs do not yet cover this compatibility path.

## Compatibility Types

The compatibility type checker uses partial structural types:

```haskell
data PartialTypeF f
  = ZeroTypeP
  | AnyType
  | TypeVariable LocTag Int
  | ArrTypeP f f
  | PairTypeP f f
```

The archived compatibility checker requires `main` to look like a closure that
accepts the transcript input shape:

```text
main :: (Zero -> Zero, Any)
```

This is the old `.tel` calling convention. A function is represented as a pair
of deferred code and a closure environment.

## Term3

`Term3` is the last compatibility IR before the new runtime:

```haskell
data Term3F f
  = Term3B (BasicExprF f)
  | Term3S (StuckF f)
  | Term3A (AbortableF f)
  | Term3Unsized UnsizedRecursionToken
  | Term3CheckingWrapper LocTag f f
```

The data language is intentionally small: zero and pairs. Everything else is
encoded with environment operations, deferred code, gates, projections, aborts,
and generated recursion tokens.

The important recursion constructor is:

```haskell
Term3Unsized UnsizedRecursionToken
```

Historically, the old runtime tried to replace each unsized site with a finite
Church tower. Telomare Tier-2 instead lowers it to a native runtime recursion
node and meters each demanded unroll.

## Runtime IR

The runtime IR is `TelExpr`:

```haskell
data TelExpr
  = TZero
  | TPair TelExpr TelExpr
  | TEnv
  | TSetEnv TelExpr
  | TDefer TelExpr
  | TGate TelExpr TelExpr
  | TLeft TelExpr
  | TRight TelExpr
  | TAbort
  | TUnbounded RecursionSite
```

`RecursionSite` pairs a stable token with source metadata:

```haskell
data RecursionSite = RecursionSite
  { rsToken :: UnsizedRecursionToken
  , rsLoc   :: LocTag
  , rsOwner :: Maybe String
  }
```

That is enough to give users readable runtime evidence while preserving stable
site IDs for generated or repeated locations. The owner is the best known
top-level binding whose parsed source location contains the recursion site, such
as `Prelude.foldr` or `tictactoe.whoWon`.

## Runtime Values

Evaluation produces machine values:

```haskell
data Value
  = VZero
  | VPair Value Value
  | VDefer TelExpr
  | VGate Value Value
  | VAbort
  | VAborted BasicExpr
  | VRec RecursionSite Value Value
```

The closure convention is:

```text
VPair (VDefer body) closureEnvironment
```

Application evaluates deferred code in an environment built from the argument
and saved environment. Gates select between zero and pair branches. Aborts are
values: they can propagate through demanded computation, but discarded aborts do
not end the run.

Native recursion is represented by:

```text
VRec site step savedEnvironment
```

When a `VRec` is forced, the runtime charges one unroll to `site`, evaluates one
layer of the step function, and forces again if needed. This is demand-driven
recursion, not static rejection.

## Transcript Protocol

A `.tel` program is interactive by convention. The runtime first applies `main`
to `Zero`. Later iterations pass:

```text
Pair encodedInput previousState
```

The program returns either:

- `Zero`, meaning abort/stop;
- `Pair display newState`, where display decodes to text and zero state ends the loop;
- a surviving abort value, meaning runtime error.

The loop itself does not know about games, prompts, or business logic. Prompts
are just part of the program's display string.

## Runtime Meter

The Tier-2 meter records:

```haskell
data Meter = Meter
  { mApplies :: Int
  , mGates   :: Int
  , mUnrolls :: Map RecursionSite Int
  }
```

It now renders as a source-aware table:

```text
-- Telomare Tier-2 work meter
function applications: 72,843
gate selections:        5,450
recursion unrolls:      1,288 across 14 sites

  site  source               function           unrolls
  #1    Prelude.tel:48:23    Prelude.foldr       2,788
  #6    tictactoe.tel:59:65  tictactoe.whoWon    1,440
  #3    Prelude.tel:67:42    Prelude.map         968
```

The table is sorted by hottest recursion site first. Site IDs come from
`UnsizedRecursionToken`, so they remain compact and stable. Source labels come
from the parser's `LocTag`. Function labels come from the parsed top-level
definition containing that source node. Generated, builtin, runtime, decompiled,
and unknown fallbacks are used when source metadata is unavailable.

`--max-steps` spends fuel on function applications and recursion unrolls. Gate
selections are counted but do not spend fuel.

## The Formal Surface Bridge

`Telomare.Surface` mirrors the Agda `T3.Surface` category. Its types omit `Bang`,
and its morphisms include free surface duplication and bounded recursion:

```haskell
data UTy = UUnit | UNat | UTy :**: UTy | UTy :++: UTy | UList UTy
data UMorph (a :: UTy) (b :: UTy) where
```

`Telomare.Compiler.Direct` implements the first placement-free compiler slice:

```haskell
compileDirect :: UMorph a b -> Either DirectError (Morph (Lift a) (Lift b))
```

It compiles identity, composition, tensor, product and sum structure, lists,
naturals, constants, guards, and natural duplication. Natural duplication uses
`DupNatS`, the explicit measured atom exemption. General duplication and all
three recursion constructors return `DirectError` because they need modal
placement.

`eraseMorph` removes core modal structure. The surface vectors compare `evalU`
with `evalV` after compilation and check that erasing each successful result
reproduces the source structure. They also check explicit rejection of the
deferred constructs and exercise `UIter`, `UFold`, and `UWhile` through their
surface semantics.

The Agda `T3.Compiler.Direct` relation mirrors the successful compiler cases.
`direct-erases` proves that successful elaboration erases exactly to its source,
and `direct-factor` derives semantic preservation from the existing core
factorization theorem. Both are checked under `--safe` through
`Everything.agda`.

This is not yet the pointful `.tel2` compiler: typed source elaboration, higher-order
lowering, general modal placement, and recursion placement remain separate
milestones.

## The Formal Core

The resource-aware formal story starts at a typed core, not at `.tel` syntax.

```haskell
data Ty
  = Unit
  | Nat
  | Ty :*: Ty
  | Ty :+: Ty
  | ListT Ty
  | Bang Ty
```

The value interpretation erases `Bang`:

```haskell
type family Val a where
  Val 'Unit      = ()
  Val 'Nat       = Natural
  Val (a ':*: b) = (Val a, Val b)
  Val (a ':+: b) = Either (Val a) (Val b)
  Val ('ListT a) = [Val a]
  Val ('Bang a)  = Val a
```

This is the central idea: `!A` is not a different runtime value. It is a
different resource permission.

Core programs are typed morphisms:

```haskell
data Morph (a :: Ty) (b :: Ty) where
```

The GADT indices say what input and output type each program has. Constructors
provide categorical structure, products, sums, lists, naturals, guards, modal
operations, and fuel-carrying recursion.

## Affine Use And Bang

Telomare's core is affine and EAL-inspired:

- Weakening is allowed.
- General implicit duplication is absent.
- Duplicating boxed values requires `DupS`.
- Duplicating naturals has a specific atom-level primitive, `DupNatS`.
- Promotion is explicit through box constructors.
- Recursion is bounded by natural fuel or finite lists.

This means resource-relevant structure is visible in the term. Copying is not
ambient magic; it appears where the semantics can charge for it.

## Value Semantics

The plain denotation is:

```haskell
evalV :: Morph a b -> Val a -> Val b
```

Every well-typed core morphism denotes a total Haskell function, mirroring the
Agda value semantics. Recursion is total because it consumes explicit finite
data: a natural fuel value or a list.

## Graded Semantics

The graded semantics interprets the same program as a value plus a resource
observation:

```haskell
evalG :: CostAlgebra m -> Morph a b -> Val a -> (m, Val b)
```

The Agda spec proves that the value component of every graded interpretation
agrees with `evalV`. Concrete grades include:

- work, charging natural case analysis and taken loop steps;
- duplication pressure, charging boxed duplication, natural duplication, and probes;
- space in the Agda spec.

The Haskell mirror currently implements work and duplication. The Agda spec also
defines the space grade.

## Exact Fuel Execution

Fuel execution is:

```haskell
evalK :: Morph a b -> Val a -> Natural -> Maybe (Val b, Natural)
```

The Agda theorem says the computed work grade is exact:

```text
evalK f a (work f a + extra) = just (evalV f a, extra)
```

With `extra = 0`, running with exactly the computed work returns exactly the
denoted value and consumes all supplied work.

This theorem applies to typed core `Morph` programs. It does not yet apply to
the shipped compatibility `.tel` runtime.

## Placement

Placement strips syntax down to a recursion skeleton:

```haskell
data Skel
  = Tip
  | Bin Skel Skel
  | Rec Skel
  | Call Natural Skel
```

A decoration gives each recursion site a level:

```haskell
data Deco
  = TipD
  | BinD Deco Deco
  | RecD Natural Deco
  | CallD Natural Deco
```

The Agda spec proves that valid placements are meet-closed and that structural
placement computes the least solution. In other words, the level assignment is
not a runtime guess; it is a structural fact about the recursion skeleton.

The archived compatibility `--certificate` implementation used a static placement report,
not the full newer budget pipeline. It groups source `{test, step, base}`
recursion sites, reports contextual inferred box levels, gives static dependency
witnesses, and shows binding depth pressure. It is deliberately labeled as a
compatibility approximation rather than a formal EAL typing or runtime budget.

## Abstract Budgets

Budget inference tracks abstract shapes:

```haskell
data ShapeH
  = TopS
  | UnitS
  | NatLE Natural
  | PairSh ShapeH ShapeH
  | SumSh (Maybe ShapeH) (Maybe ShapeH)
  | ListSh Natural ShapeH
  | BangSh ShapeH
```

It transfers shapes through typed core morphisms:

```haskell
transferB :: Morph a b -> ShapeH -> (BudgetT, ShapeH)
```

Known natural or list bounds produce finite recursion-site budgets. Unknown fuel
or unknown list length produces `top`: a useful notice that the analyzer lost a
finite bound, not a type error.

The Agda spec proves output-shape soundness. It does not yet contain a separate
theorem saying every emitted budget-tree number bounds every concrete runtime
site trace.

## Verification Layers

Telomare deliberately separates proof from regression evidence:

- `spec/Everything.agda` is checked with `--safe` and no postulates.
- The Haskell surface, direct compiler, erasure, and core mirror the Agda definitions and elaboration relation.
- QuickCheck laws test the Haskell mirror against Agda-proved properties.
- Core example vectors mirror Agda computations.
- Surface vectors check all direct compiler constructors, semantic parity, erasure, and deferred-feature diagnostics.
- `.tel2` golden transcripts test scripted typed `Morph` machines.
- Legacy `.tel` transcript and meter vectors remain temporary regression evidence.

The Agda proofs are the source of truth for the typed core. The Haskell tests
guard implementation drift.

## Current Boundary

The honest boundary is the most important part of the story:

- The executable accepts `.tel2` only; `.tel` compatibility code is archival.
- `.tel2` finite machines compile and run through typed `Morph` artifacts only.
- The formal totality and adequacy theorems apply to every generated `Morph`.
- The proved direct compiler covers the placement-free `UMorph -> Morph` fragment.
- There is not yet a pointful `.tel2 -> UMorph` frontend or general modal and recursion placement pass.
- The `.tel2` meter is the formal core work grade, not a compatibility event counter.
- Haskell does not yet mirror the Agda space grade.

Telomare today has a core-only finite-machine executable and a machine-checked
surface/core bridge. The next source-language step is typed pointful affine
`.tel2 -> UMorph` elaboration with explicit copying, followed by modal placement
for general duplication and bounded recursion.
