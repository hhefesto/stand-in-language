# Telomare, three ways: Haskell (master), Agda (`agda` branch), Bend (`bend-port`)

This document does two things:

1. gives a general assessment of the **Haskell implementation** on `master` —
   the production compiler, with `src/Telomare/Possible.hs` as its center of
   gravity;
2. compares it with the two sibling artifacts: the **Agda denotational
   design** built on the `agda` branch, and the **Bend port of the compiler**
   being built on this branch (`bend/`, see `bend/PORT.md`).

---

## 1. Assessment of the Haskell telomare

### What it is

A compiler + runtime for a language whose core bet is **bounded recursion as
a language primitive**: `{test, body, base}` is the only recursion form, and
the compiler statically infers how many unrollings every such site needs.
A program that cannot be bounded is rejected at compile time. The pipeline:

```
.tel source
  → Parser.hs      (megaparsec; layout-sensitive; UnprocessedParsedTerm)
  → Resolver.hs    (imports, case/pattern elaboration, church numerals,
                    lets→app brackets, de Bruijn, {x,y,z} → UnsizedRecursion
                    tokens; Term3)
  → Possible.hs    (sizeTermM: abstract interpretation infers every
                    recursion bound; Term3 → CompiledExpr)
  → Eval.hs        (evalLoop: main :: (input, state) → (output, state),
                    iterated against stdin until state = 0)
```

The IR is minimal and pair-based: `Zero | Pair | Env | SetEnv | Defer | Gate
| Left | Right | Abort` — closures are `Pair (Defer body) env`, application
is environment surgery (`SetEnv`), branching is `Gate`, and **all data is
nested pairs** (numbers are `(n-1, 0)` chains, strings are lists of those).

### Possible.hs — the sizing engine (the crown jewel)

`Possible.hs` (1430 lines) + `PossibleData.hs` (697) implement an abstract
interpreter over the same IR extended with analysis constructors:

- **`UnsizedStubF tok`** — a hole where `{x,y,z}`'s church numeral will go;
  during analysis it expands into a self-rebuilding *step stub* that counts
  iterations (`SizeStepStubF tok n`) and emits `SizeStageF (tok ↦ n)`
  records into a `StrictAccum SizedRecursion` monad when the recursion
  test says "stop".
- **`RecursionTestF tok`** — wraps each site's termination test so the
  analyzer can intercept the tested *value*.
- **`IndexedInputF`** — the program input is a symbolic binary tree of
  variables (`IVar n`, children `2n+1`/`2n+2`); refinement annotations
  (`x : check`) are evaluated *statically* (`getInputLimits`) to learn which
  input paths are guaranteed `Zero` — that is how `validInput = assert (not
  ($127 left x)) ...` in tictactoe.tel turns "unbounded user input" into
  "input of depth ≤ 127", which is what makes the game sizable at all.
- **`SuperPositionF` (EitherPF)** — when control flow branches on a symbolic
  input, the analyzer explores *both* branches as a tagged superposition,
  merging (`mergeShallow`) and pruning (branch-descendance filters on
  function application) as it goes.
- If a recursion test lands on an *unbounded* input variable the analysis
  aborts with `AbortUnsizeable tok` and compilation fails — the language's
  central promise, enforced.

The result (`SizedRecursion`: token → bound) is substituted back
(`setSizes`), producing a closed `CompiledExpr` in which every former
`{x,y,z}` is a concrete `SetEnv^n Env` church tower. Nothing at runtime can
recurse more than the analysis proved.

This design is unusual and genuinely valuable: it is a *whole-program,
per-call-site* termination analysis that produces exact operational budgets,
not just a yes/no totality check.

### Maturity map

| Component | State |
|---|---|
| Parser (764 LOC), Resolver (761), Possible/PossibleData (2127), Eval (364) | Solid; the working spine. ~4.4k LOC of tests (parser/resolver/sizing/eval/UDT/case suites) |
| LSP (1097) + Emacs modes | Mature; diagnostics, goto-def, references, semantic tokens, partial-eval code action |
| REPL, Evaluare TUI | Working developer tooling |
| TypeChecker.hs (188) | **Partial**: unification is variable↔type only; tests recently commented out (commit `15c9e06`) |
| Llvm.hs (530) | Stub, not wired into the build |
| showSizingInSource | TODO placeholders |

Honest overall read: the language core and its one big idea are implemented
and tested; the static-type story and the optimizing backend are aspirations.
Where guarantees exist, they come from the sizing engine, not from types.

---

## 2. The three artifacts, side by side

The three versions are not three implementations of one spec — they are
three different *kinds* of artifact around the same idea:

- **Haskell (`master`)** — the *production compiler*: parses real `.tel`
  syntax, infers recursion bounds, runs interactive programs.
- **Agda (`agda` branch)** — the *machine-checked denotational design*
  (Conal Elliott style): a typed syntax category `_⇨S_` with four
  denotation functors — execution `⟦_⟧K`, exact cost `⟦_⟧C`, work/span
  `⟦_⟧WS`, space `⟦_⟧SP` — and the `precise` theorem: **per-input exact
  cost is proved, not measured**. `{x,y,z}` appears as the `whileS`
  primitive (on-demand metering) and derived `whileD` (reserved-capacity),
  with agreement proofs; plus the ConCat bridge compiling the same
  morphisms to circuit SVGs and HVM2 programs.
- **Bend (`bend-port`)** — the *compiler re-hosted on HVM2*: a faithful
  port of the Haskell pipeline (parser → shared-let resolver → the
  Possible.hs abstract interpreter → evalLoop) written in fully-annotated
  Bend, so that telomare compilation itself runs on interaction nets.

| Dimension | Haskell `master` | Agda `agda` | Bend `bend-port` |
|---|---|---|---|
| **Artifact kind** | production compiler + tooling | verified denotational spec + ConCat backends | compiler hosted on HVM2 |
| **Recursion discipline** | `{x,y,z}` bounds *inferred* by abstract interpretation (Possible.hs); unsizable programs rejected | `whileS`/`iterS` primitives; bounds are *typed fuel*; `precise` proves exact per-input cost | same as Haskell — the sizing engine is ported, the guarantee is preserved through compilation |
| **Cost story** | implicit: bounds exist, no cost surfaced to the user | explicit & proved: `⟦_⟧C` exact ticks, `⟦_⟧WS` work/span, `⟦_⟧SP` space; resource-algebra 2×2 | inherited from source semantics; runtime cost = HVM2 interactions (empirically 45·cost+15 for the agda drainS pipeline) |
| **Typing** | partial unification checker (tests disabled); refinements via runtime-abort checks evaluated statically | full dependent types; everything total, every claim a theorem | Bend's checked annotations on the *compiler itself* (`bend check` clean); object language unchanged |
| **IO model** | `evalLoop`: `main (input, state) → (output, state)` against stdin | pure morphisms; IO deferred (MAlonzo mains print cost/space summaries) | same evalLoop protocol, replayed over an inputs file; interactivity via deterministic re-run wrapper |
| **Runtime** | GHC-compiled tree-walking evaluator | MAlonzo reference eval (~240 ns/tick, flat); ConCat→HVM2 emission for parallel demos | HVM2 (`bend run-c`) end to end — parser, sizer and object program all reduce as interaction nets |
| **tictactoe** | `tictactoe.tel`: interactive, board drawing, 2 players, input validation via `$127` refinements | `ticTacToeS : listT nat ⇨S nat` — moves list → winner, winners proved by `refl`, cost/reserved/space measured | same `tictactoe.tel`, same compiler semantics (see status below) |
| **What can fail** | compile-time: unsizable recursion; runtime: aborts | nothing at runtime — failure is a type error at design time | same as Haskell, plus HVM2 heap limits during analysis (see below) |

### Where each shines, in one sentence each

- The **Haskell** version proves the *feasibility* of the idea: a real
  compiler that infers exact recursion budgets for real interactive
  programs.
- The **Agda** version proves the *meaning* of the idea: cost is a
  denotation, `{x,y,z}` is `whileS`, and "the program costs exactly N" is a
  theorem checked by a machine.
- The **Bend** version tests the *portability* of the idea: the guarantee
  survives being re-hosted on a maximally-parallel, structurally-linear
  runtime — and doing so exposes exactly which parts of the Haskell
  implementation silently depended on lazy shared heaps.

### Bend port status (as of this branch)

Working end to end: lexer/parser (all of Prelude.tel + tictactoe.tel),
shared-let resolver (14 recursion tokens on tictactoe), the full sizing
engine — including `$127`-deep refinement-derived input limits (tictactoe's
whole main sizes correctly) — and the interactive evalLoop (refinement-
checked programs run, loop over stdin lines, and correctly abort on invalid
input; verified against oracle transcripts). Two exponential blowups vs the
Haskell oracle were root-caused to strictness-vs-laziness mismatches and
fixed (superposition env-filter materialization; strict Gate branches).
Known open item: the runtime evaluator's cost on real-character data under
large fuel towers — full tictactoe currently DNFs at runtime (the compiler
side completes); the identified fix is a WHNF-style demand-driven evaluator.
Everything is timeout-guarded; see `nix run .#telomare-bend` and
`bend/PORT.md` for the full log.

### What the comparison teaches

1. **The sizing engine is the language.** All three artifacts stand or fall
   on it: Haskell implements it, Agda *is* its semantics, Bend stress-tests
   its algorithmic assumptions.
2. **Laziness was load-bearing.** The Haskell analyzer freely superposes
   branches and filters environments because GHC shares thunks. On HVM2,
   duplication is physical: the same algorithm forced structural rewrites
   (prune-before-inline, shared lets instead of inlining, one pipeline stage
   per process) — all documented as "HVM2 lessons" in `bend/PORT.md`.
3. **Refinements are the bridge between open input and bounded cost.** In
   all three versions, interactive programs are only bounded because
   `x : check` annotations statically constrain the input shape — the Agda
   design makes this visible as the fuel argument of `whileS`; tictactoe's
   `$127` is that fuel written in .tel.
