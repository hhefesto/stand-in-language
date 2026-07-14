# Telomare: The Type Story

Telomare is a language experiment about making computation executable without
making resource behavior mysterious. Its core claim is simple: a program should
not only compute a value; it should also expose enough structure to explain how
much work, copying, placement depth, and recursion budget it needs.

The current repository contains two connected but not yet unified stories:

```text
.tel source
  -> AnnotatedUPT
  -> Term1
  -> Term2
  -> Term3
  -> TelExpr
  -> Value
  -> transcript output + Meter

Morph a b
  -> Val a -> Val b
  -> graded work / duplication / fuel execution
  -> placement skeletons
  -> abstract recursion budgets
```

The first path is what the `telomare` executable runs today. The second path is
the typed formal core mirrored in Haskell and proved in Agda. There is not yet a
`.tel -> Morph` compiler, so this document keeps the boundary explicit.

## The Executable Path

The executable starts with a file path and ends with an interactive transcript.

```haskell
loadModulesFor :: FilePath -> IO (Either Tel3Error (String, [(String, String)]))
compileTel     :: [(String, String)] -> String -> Either Tel3Error TelExpr
runTelLoop     :: Maybe Int -> TelExpr -> IO Meter
```

`loadModulesFor` reads the entry module and textual imports. `compileTel` turns
loaded source into the runtime IR. `runTelLoop` evaluates the resulting program
under the `.tel` display/state protocol.

The CLI options line up with that path:

- `--certificate` prints the static compatibility placement report.
- `--meter` prints the Tier-2 runtime meter.
- `--max-steps N` gives the runtime a fuel cap.

## Surface Syntax

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

The CLI requires `main` to look like a closure that accepts the transcript input
shape:

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

## The Formal Core

The formal story starts at a typed core, not at `.tel` syntax.

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

The CLI `--certificate` currently uses a static compatibility placement report,
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
- The Haskell core mirrors the Agda definitions.
- QuickCheck laws test the Haskell mirror against Agda-proved properties.
- Example vectors mirror Agda computations.
- `.tel` golden transcripts test the compatibility runtime.
- Meter vectors test readable source-aware runtime evidence.

The Agda proofs are the source of truth for the typed core. The Haskell tests
guard implementation drift.

## Current Boundary

The honest boundary is the most important part of the story:

- `.tel` programs currently run through the compatibility frontend and Tier-2 runtime.
- The formal totality and adequacy theorems apply to typed `Morph`, not arbitrary `.tel` programs.
- There is not yet a `.tel -> Morph` compiler.
- Unknown `.tel` recursion is handled by native demand-driven runtime recursion and optional fuel.
- The runtime meter reports what happened; it is not yet the same object as the Agda work grade.
- Haskell does not yet mirror the Agda space grade.

Telomare today is therefore both a practical `.tel` runtime and a machine-checked
semantic core. The next major unification step is to make the practical path
land in the typed core, so the executable language inherits the full proof story.
