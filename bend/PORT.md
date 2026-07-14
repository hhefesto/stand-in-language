# Porting the telomare compiler to Bend

This document is the running log of the port. It contains the approved plan
(verbatim), the engineering findings that constrain the design, and a progress
log updated as milestones land. Branch: `bend-port`.

**Goal**: a telomare compiler written in Bend (running on HVM2) that compiles
and runs `tictactoe.tel` — real telomare syntax, importing `Prelude.tel` —
with the same/similar observable behavior as the Haskell compiler
(`nix run . -- tictactoe.tel`). Full pipeline, including a faithful port of
the `Possible.hs` recursion-sizing engine. Maximal type annotations in all
Bend code. The Haskell implementation is the verification oracle throughout.

---

## The plan (approved)

### Context
We are on `master` — the Haskell implementation of telomare. Goal: a
**telomare compiler written in Bend** that can compile and run `tictactoe.tel`
(telomare syntax, importing `Prelude.tel`) with the same/similar observable
behavior as `nix run . -- tictactoe.tel`. User decisions:
- Full port, including a **faithful port of the Possible.hs sizing engine**
  (abstract interpretation, superpositions, indexed inputs, SizedRecursion) —
  not a runtime-fuel shortcut.
- Maximal type annotations in all Bend code (annotate every `def`, use ADTs).
- Separately deliver: a general assessment of the Haskell telomare + a
  three-way comparison (Haskell master / Agda branch / this Bend port).

Reference pipeline being ported:
`Parser.hs (764) → Resolver.hs (761) → Term3 → sizeTermM (Possible.hs 1430 +
PossibleData.hs 697) → CompiledExpr → Eval.hs evalLoop (input,state)→(output,state)`.
The Haskell implementation is the **oracle**: every milestone is verified by
diffing against `cabal run telomare` / existing test expectations.

Grammar subset actually needed (everything used by Prelude.tel + tictactoe.tel):
top-level defs, `import`, `let … in` (with `name : check` refinements), multi-arg
lambdas, application, `if/then/else`, pairs `(a,b)`, `left`/`right`, lists,
strings, numbers, church numerals `$n`, `{x,y,z}` limited recursion, `--`
comments. (Verify at implementation whether Prelude uses case/UDTs; add only if
needed — the full UDT/case machinery of Resolver.hs is out of scope unless
required.)

Bend constraints to design around: u24 numbers (tokens/indices fit); builtin
`Map` (u24-keyed tree) for `SizedRecursion` and zero-index sets; define own
`Option`/`Either` ADTs where builtins don't fit; no typeclasses/recursion-schemes
— the Haskell functor-composition (`basicStep (stuckStep (abortStep …))`)
flattens into one big `Expr` ADT with explicit match-chain step functions;
`StrictAccum SizedRecursion` monad becomes explicit `(result, sizes)` threading;
no `f(a)(b)` chained application; recursive helpers referenced as named globals;
use `bend run-c` for speed (sizing is compute-heavy), `bend check` for types.
**Never run bend without `timeout`.** Bend 0.2.37 from nixpkgs (`pkgs.bend`).

### Milestones

**M0 — Branch + scaffolding.** `bend-port` branch; `bend/` directory; driver
wrapper (flake app `.#telomare-bend`); smoke test; this PORT.md.

**M1 — Core IR + evaluator.** `Expr` ADT covering all constructor families:
Basic (Zero/Pair), Stuck (Defer idx/Env/SetEnv/Gate/Left/Right), Abort
(Abort/Aborted msg), plus the sizing families for M4: Unsized
(RecursionTest/UnsizedStub/SizeStepStub/SizeStage/RefinementWrapper), Super
(EitherP tag), Indexed (IVar/Any), Deferred (Barrier/ManyLefts/ManyRights).
Port `basicStep`/`stuckStep`/`abortStep` and the `eval` instance
(Possible.hs:109–160, 423–442, 1176–1188). Verify: hand-built IR terms
reproducing Spec.hs basics give the oracle's outputs.

**M2 — Lexer + parser.** Recursive-descent over `String` for the grammar
subset, producing a `ParsedTerm` ADT mirroring UnprocessedParsedTerm's used
constructors. Verify: parses `Prelude.tel` (162 lines) and `tictactoe.tel`
(117 lines); AST spot-checks against ParserTests.hs cases in scope.

**M3 — Resolver.** `import Prelude` (two-module resolution), name resolution →
de Bruijn/env paths (`Left (Right … Env)`), closure conversion of lambdas →
`Defer`/`SetEnv` per Resolver.hs conventions, church numeral elaboration,
list/string/pair sugar, `{x,y,z}` → UnsizedRecursion tokens + stubs,
`name : check` refinements → RefinementWrapper/abort checks. Verify: small
.tel snippets end-to-end (recursion sizes hardwired temporarily) match the
oracle.

**M4 — Possible.hs port (the centerpiece).** PossibleData types
(SizedRecursion as Map token→Option(u24) with max-merge monoid; GateResult;
InputRestrictions/zeroes). Stepping functions in dependency order:
`indexedInputStep`, `zeroedInputStepM`, `indexAbortIfUnboundStep`,
`superStep`/`superStepM` + `gateResult`, `unsizedTest*`,
`unsizedStep`/`unsizedStepM'''` (SizeStepStub counter, iteB test/body/base
synthesis, maxSize abort), `getInputLimits`, `capMain`,
`removeRefinementWrappers`. Then `sizeTermM` (Possible.hs:999) — the composed
evalStep chain with explicit `(Expr, SizedRecursion)` threading; `Either token
CompiledExpr` result; final conversion stripping sizing constructors. Verify:
SizingTests.hs bounds match the oracle; Prelude's `d2c`/`map`/`foldr`/`take`/
`drop` recursion sites size successfully on tictactoe's main.

**M5 — Eval pipeline + IO loop.** `compileMain` equivalent, `funWrap`-style
wrapping, evalLoop protocol (Eval.hs:216–258): read line, apply main to
`(input, state)`, print output, loop while state ≠ Zero. Verify: a trivial
echo .tel program runs.

**M6 — tictactoe.tel parity.** Scripted transcripts diffed vs the Haskell
compiler: p1 win (1,4,2,5,3), p2 win, tie, invalid inputs (letter, 0, occupied),
`q` quit. `timeout` on every bend run; `pgrep bend` clean afterwards.
Interactive play via `nix run .#telomare-bend -- tictactoe.tel`. Byte-identical
boards expected; benign divergences documented here.

**M7 — COMPARISON.md.** Assessment of the Haskell telomare + three-way
comparison (Haskell master / Agda branch / Bend port): what each artifact is,
recursion & cost guarantees, typing, IO model, runtime, how tictactoe exists
in each.

### Verification (overall)
- `bend check` clean on all .bend files (annotations everywhere).
- Golden diffs vs the Haskell oracle at every milestone (eval outputs, sizing
  bounds, game transcripts).
- `nix run .#telomare-bend -- tictactoe.tel` playable; scripted game diff vs
  `nix run . -- tictactoe.tel` matches.
- All bend invocations timeout-wrapped; no leftover processes; work stays on
  `bend-port`; no commits unless asked.

### Risks
- Large, multi-session effort; M4 dominates. Milestone order keeps every
  session's work verifiable in isolation (this file tracks state).
- Sizing performance under HVM interpretation unknown → `run-c`; if sizing
  tictactoe is impractically slow, surface measurements and options.
- Haskell's laziness/typeclass composition has no Bend analogue; flattened
  match-chains risk semantic drift → per-function golden tests against the
  oracle, not just end-to-end runs.

---

## Bend 0.2.37 findings (probed 2026-07-02, drive the driver design)

- Subcommands: `check`, `run-rs`, `run-c`, `run-cu`, `gen-*`, `desugar`.
  There is **no plain `run`**.
- ADTs (`type Cell: Empty ...`), field access (`res.val`), `match`/`switch`,
  and full `def f(x: T) -> T:` annotations all work and are enforced by
  `bend check` and at compile time in `run-c`.
- **`main` with parameters must be unannotated** — an annotated
  `def main(n: u24) -> u24:` fails the entrypoint type check; `def main(n):`
  works and receives CLI arguments (`bend run-c file.bend 21`). String args
  work as quoted Bend expressions: `bend run-c file.bend '"path.txt"'`.
  Consequence: `main` is the single unannotated def; everything else is fully
  annotated.
- **IO**: `run-rs` does not execute IO at all (returns the unevaluated IO call
  tree). `run-c` executes IO. `IO/input` does not exist. `IO/print(String)`
  works. `IO/FS/open(path, "r")`, `IO/FS/read_line(fd)`, `IO/FS/read_file`
  exist; `read_line`/`read_file` return `Result(List(u24), u24)` which must be
  `match`ed (`Result/Ok` carries bytes; decode with `String/decode_utf8`).
- **stdin is only readable when seekable**: `read_line(IO/FS/STDIN)` works
  with stdin redirected from a regular file, but returns `Result/Err` on a
  pipe (and presumably a tty) — the runtime appears to seek back after
  chunked reads. Sequential `read_line`s on a regular-file fd work correctly.
- Consequences for the driver (`nix run .#telomare-bend`):
  - The compiler (`bend/telc.bend`) takes two CLI args: the `.tel` program
    path and an inputs file path; it reads both via `IO/FS` (no source
    embedding needed) and replays the input lines through the evalLoop,
    printing the full transcript.
  - Scripted mode: pipe/redirect moves → wrapper writes them to a temp file →
    single bend run. This is the parity-testing mode.
  - Interactive mode: the shell wrapper owns the prompt loop — it appends
    each user line to the inputs file, re-runs the compiler, and prints only
    the new suffix of the transcript (replay is deterministic; telomare's
    main is a pure step function). If per-keystroke recompilation proves too
    slow, revisit (e.g. serialize the sized IR between turns).
- `Result`, `Option` (`Option/Some`/`Option/None`? verify when first needed),
  `Map`, `String`, `List` are builtin; `Tree` is a reserved builtin name
  (known from prior session — avoid).

## HVM2 lessons (things that OOM/crash and their idioms)

- **Long `with IO` bind chains that interleave heavy computation OOM the C
  runtime**: a 12-deep IO sequence of evaluator calls exhausted the heap
  (`OOM` × nthreads), while the same 12 evaluations computed *purely* and
  printed with a single `IO/print` at the end run fine. The monadic
  continuation appears to retain every intermediate tree. Idiom for the whole
  port: **compute pure, do IO only at the edges, cross the boundary with
  small fully-forced values (strings/u24s).**
- **Never write `match f(x): ...` and then call `f(x)` again in the arms** —
  bind once (`r = f(x)`), match `r`. Duplicated calls double the work at
  every recursion level (exponential in nesting depth).
- **Don't run a second heavy computation inside a `match` arm that holds
  another big result open.** `match pr: case MOk: r = parse(...); match r:
  ... pr.binds ...` OOMs even at 536M nodes (single-thread window); the same
  two parses complete instantly when each lives in its own top-level function
  that returns plain constructed data upward. Idiom: **one pipeline stage =
  one function; destructure early; pass fields, not open matches.** Flat
  strings dup cheaply — re-parsing a source string per case is cheaper than
  sharing a parsed tree across cases.
- **Eager inlining of unused definitions explodes**: Haskell's
  validateVariables can inline all 51 Prelude defs because its heap shares
  thunks; under HVM's eager dup-copying this OOMs. Haskell's own
  `pruneBindings` (resolveMain) is the fix — port it (only defs transitively
  reachable from `main` are resolved).
- `bend run-c`'s heap is `2^29` nodes split across 16 thread windows
  (`G_NODE_LEN/TPC` ≈ 33M nodes for a sequential workload). A custom
  `bend gen-c | gcc -DTPC_L2=0` runner gives one thread the full 536M
  window — useful headroom, but fix the structure first (the OOMs above were
  all structural, not capacity).
- One compile+eval pipeline per process: 13 chained compiles in one net run
  >10 min; the same cases finish individually. Shell-loop drivers
  (`bend/run_resolver_tests.sh`) keep each net small.

## Progress log

### 2026-07-02 (night) — E1: native-Bend emission backend ✅ (core verified)
The runtime interpreter is replaced by a code generator (`bend/emitter.bend`):
after sizing, the CompiledExpr is emitted as a standalone Bend program that
HVM2 executes natively. Getting there surfaced four deep findings:
- **Bend 0.2.37's C-runtime string OUTPUT is pathologically slow**
  (~0.13 s/character, linear — measured 6.1s for 50 chars, 116s for 800,
  via IO/print, IO/FS/write to file or stdout, AND the Result readback).
  Every mysterious "hang" this session was actually this. Bypass: programs
  RETURN their text as a pure result value and run under `bend run-rs`
  (the lazy Rust runtime), whose Result dump is fast; a tiny
  `decode_result.py` turns the dump back into text (it handles the quoted
  literal form, the run-rs Scott-chain form and hvm run-c's chain form).
  run-rs needs `ulimit -s unlimited` (deep recursion) and its lazy
  readback stops at nullary global refs in tail position — the emitted
  string is forced with a trailing `str_cat(x, "")`.
- **The whole COMPILER runs under run-rs in ~8s** for small programs
  (vs 90s+ on the multithreaded C path) — laziness beats 16 threads here.
  Stage-1 wrappers embed the .tel sources as ≤380-char chunk defs
  (`gen_wrapper.py`) because...
- **HVM's C backend caps every definition at 4095 nodes** ("Definition is
  too large") and bend then produces no output while exiting 0. All big
  string constants (the emitted prelude/driver) are chunked defs.
- **HVM2 cannot soundly duplicate non-affine functions flowing through
  data** — the agda-session "tuple-function cloning" bug in general form.
  Lambda-wrapped closures clone into silent erasers (`Result: *`); bare
  global refs are refused by run-rs and re-expanded-then-cloned by the C
  path on the repeatFunctionS frames (hand-built n=2 protocol OOMs while
  n=1 works). Since telomare's IR stores functions in frames pervasively,
  the emitter **defunctionalizes**: `TV/F` carries a plain slot NUMBER and
  a generated `tvDispatch(slot, env)` switch maps it to `d<fid>` — numbers
  duplicate freely, so every runtime is sound. (Also: bend `match` on a
  u24 silently always takes the first arm — use `switch`.)
- Pipeline now: stage 1 `bend run-rs` (compile+size+emit, pure result) →
  decode → `out.bend` → stage 2 `bend gen-hvm | hvm run-c` (the standalone
  C INTERPRETER: no gcc, no def cap in practice, sound ref semantics) →
  decode transcript. Driver: `bend/run_telomare_bend.sh`.
- **Verified end-to-end**: e1 ("hi"), `$2 id "ok"` church towers, `d2c 2`
  sized recursion, and mini31 ($31 refinement + capped input) all produce
  correct transcripts through the emitted backend.

### 2026-07-03 — toolchain hardening: no Python, cached compiles
- Per user instruction the driver is **shell/awk only**:
  `run_telomare_bend.sh` now contains `emit_chunks` (source embedding),
  `emit_inputs` (per-run `def inputs()` in TV encoding) and
  `decode_result` (Result-dump → text) as awk functions;
  `gen_wrapper.py`/`decode_result.py` are gone. Emitted/embedded text is
  ASCII by construction (the generated header lost its em-dash).
- **Input-independence + caching**: `emit_program` no longer embeds input
  lines — the compiled program only depends on Prelude + the .tel source,
  so stage 1 is cached under `~/.cache/telomare-bend/<hash>.bend` (hash of
  prelude + program + compiler sources). First run pays the sizing; every
  replay is stage-2 only — measured **0.83s** warm for e1. This is what
  makes interactive play viable (re-run per move at stage-2 cost).
- Mystery solved: `bend run-rs` shells out to `hvm run .out.hvm` in the
  CWD — the stray `.out.hvm` at the repo root (flagged in an earlier
  session) was bend's own temp file. Removed.

### 2026-07-03 — E3 status: tictactoe compile is the last wall (in progress)
- Two full attempts at tictactoe.tel's stage-1 (compile+size at `$127`,
  14 tokens) DNF'd at their caps: 83 min (pre-cache driver) and **4h 0m**
  (cached driver). The sizing itself is correct and converging (verified
  at every reachable scale; GHC runs the identical analysis in ~70s) —
  the cost is the interpretation tower: a compiler interpreted by HVM's
  Rust runtime, sizing a program 4× echo's size with 7× its tokens
  (echo-`$127` took ~11 min).
- A detached 12h attempt is running (`overnight_ttt.sh`, logs to
  scratchpad golden/overnight.log). Because stage 1 is cached by source
  hash, a single success makes tictactoe replayable in ~seconds forever
  after (e1 warm run: 0.83s).
- Speedup options if 12h doesn't land: stage-1 under 16-thread compiled
  `bend run-c` (compute ~5-10× faster, but pays the slow C-side result
  readback ~0.13s/char ≈ 54 min for the 25KB program — net win only if
  memory fits), or per-token sizing splits (deeper surgery).

### 2026-07-02 (night) — E2: echo at `$127` matches the oracle ✅
`printf 'a\nq\n' | bend/run_telomare_bend.sh echo.tel` produces exactly the
oracle transcript ("echo: " / "echo: a" / "bye") in 734s wall — dominated
by the one-time `$127` sizing analysis under run-rs; the generated program
itself runs in seconds on `hvm run-c`. This is the case that OOM'd or
timed out under every interpreter variant. Flake app `.#telomare-bend`
rewired to the two-stage driver (bend + hvm + python3 runtime inputs).

### 2026-07-02 — M0 scaffolding
- Branch `bend-port` created off `master`.
- Probed bend 0.2.37 (see findings above); settled the driver contract:
  `bend run-c telc.bend '"program.tel"' '"inputs.txt"'`.
- `bend/telc.bend` skeleton: reads the .tel source + inputs file via IO/FS,
  echoes source line count (pipeline placeholder). `bend check` clean.
- Flake app `.#telomare-bend` added (writeShellApplication, pkgs.bend,
  scripted + interactive wrapper modes, timeouts).
- Verified: `printf '3\n5\nq\n' | nix run .#telomare-bend -- tictactoe.tel`
  reports source/input line counts through the pipeline skeleton.

### 2026-07-02 — M1 core IR + evaluator ✅
- `bend/ir.bend`: the full `Expr` ADT (Basic/Stuck/Abort families plus the
  sizing families Unsized/Super/Indexed/Deferred carried for M4, and an
  `EvalError{code}` constructor standing in for Haskell `error`).
- Evaluator ported faithfully: `eval_expr` = `transformNoDefer step`,
  `eval_body` = the defer-body walk with `replaceEnv`, `step_expr` = the
  flattened `basicStep (stuckStep (abortStep _))` chain, including all abort
  propagation rules and `FillFunction Abort Zero -> Defer fid_abort Env`.
- FunctionIndex encoding: generated defers 1..9 (Haskell -1..-9), user
  indices from 16.
- Builders ported: `var_b`, `i2b`/`b2i`, `ite_b`, `lam_b`, `twiddle_b`,
  `app_b`; structural `expr_eq` follows Haskell's Eq1 (Defer compares fid
  only); debug `show_expr`.
- `bend/test_ir.bend`: 12 Spec.hs-style tests — pair projections, strict
  if/then/else, closure application through appB/twiddleB, curried closure
  capture (\x -> \y -> (y,x)), church-3 applied to successor, abort
  pass/abort/propagate, gate under defer. **All 12 pass** (`failures: 0`).
- Discovered the IO-bind-chain OOM (see "HVM2 lessons"); harness restructured
  to pure-compute + single print.
- Next: M2 lexer + parser.

### 2026-07-02 — M2 lexer + parser ✅
- `bend/util.bend` (shared string/number helpers), `bend/lexer.bend`
  (Token ADT; keywords per Parser.hs rws — `left`/`right`/`trace` are NOT
  keywords; `--` comments, `$n` church, string escapes), `bend/parser.bend`
  (PTerm ADT mirroring UnprocessedParsedTermF's used constructors; recursive
  descent for let/ite/lambda/application/pair/list/{x,y,z}/refinements;
  top-level plain + list assignments).
- **Layout replacement**: the Haskell parser is indentation-sensitive; this
  port discards layout and stops application chains before a lookahead match
  of `Ident (= | :)` or `[name,...] =`. The second form was added after a
  real bisected failure: `lcm`'s application chain swallowed the
  `[Rational,...] = ...` group header as a list literal.
- **List assignments** always use expandPlainListAssignment's intermediate
  + `left (right^i …)` accessor expansion. The Haskell UDT-flavored variant
  (uppercase first name + lambda body, i.e. Prelude's Rational group) is NOT
  ported — tictactoe never references those names. Divergence accepted.
- **HVM2 lesson #2**: never write `match f(x): ... f(x)` — bind the call
  once (`r = f(x)`) then match `r`; duplicated calls double work at every
  recursion level (exponential in nesting depth).
- Verified: `Prelude.tel` parses to 51 defs (44 plain + Rational-group
  expansion), `tictactoe.tel` to 12 defs + `import Prelude`; round-trip
  renders of d2c/map/foldr/abort/dEqual match the source structure.
  `bend/test_parser.bend` reports `failures: 0`.
- Next: M3 resolver.

### 2026-07-02 — M3 resolver ✅ (tictactoe-compile perf caveat)
- `bend/resolver.bend`: the full `process` path of Resolver.hs —
  `resolve` (validateVariables: inline ALL definitions; only lambda vars
  survive; `{x,y,z}` → `App (Recur t r b) Repeater`; Int/String/List sugar),
  builtins (addBuiltins + optimizeBuiltinFunctions: `App(left,x)` → `Lft x`
  syntactic rewrite, bare `left` → `\x -> Lft x`), **pruneBindings**
  (transitive-deps-of-main only — REQUIRED under HVM, see lessons),
  `debru` (de Bruijn, innermost = 0; the process path leaves every lambda
  Open → lamS), and `split` (splitExpr): state-threaded `(next_fid,
  next_urt)` in **exactly Haskell's monadic sequencing order** (appS
  allocates twiddle before arg before function; lamS/clamS body before
  defer; unsizedRecursionWrapper's bigApp before trb), `i2CB` church
  numerals via `repeat_function` (rf allocated twice, then 3 lambda defers),
  `repeaterAndAbort` (UnsizedStub token core + abort defer),
  `unsizedRecursionWrapper` (rWrap iteB_ with varB 4/3/2/1/0, tWrap
  RecursionTest positioning, trb frame), `Check` → RefinementWrapper.
- Haskell FunctionIndex starts at 0; ours at 16 (1..9 reserved for
  eval/sizing-generated defers). UnsizedRecursionToken numbering matches the
  oracle's allocation order.
- Verified (`bend/run_resolver_tests.sh`, one case per process): 12/13 PASS —
  literals, pairs, lambda application, ite, Prelude's succ/and/not inlined
  end-to-end, **church numerals evaluated through the ported
  repeatFunctionS machinery** (`$3 succ 0` → 3, `plus $2 $3 succ 0` → 5),
  and d2c/map/foldr `{x,y,z}` sites compile with the expected token counts.
- CAVEAT (resolved): compiling all of tictactoe.tel through the INLINE path
  exceeded 300s. Root cause: the inline path is `main2Term3`
  (validateVariables), which Haskell only uses for TYPE CHECKING; the real
  compile path is `main2Term3let` — definitions stay shared as
  `App (Lam name inner) def` brackets. Ported as `compile_shared`
  (l2a/letsToApps + annotateUnsizedCount, debru2/debruijinizeApp with
  LetBinding repeater application, close_lams, cap_top). tictactoe.tel now
  compiles in seconds: **14 recursion tokens**. All 12 small cases pass on
  the shared path too (`bend/test_shared.bend`).

### 2026-07-02 — M4 sizing engine (functionally complete; perf wall at $127)
- `bend/sizer.bend` (~1600 lines): the full sizeTermM machinery —
  SizedRecursion (max-merge assoc list), abort payload codecs
  (AbortRecursion/AbortAny/AbortUnsizeable), shallow-eq + mergeShallow,
  filter_left/filter_right superposition pruning, GateResult
  (basic/abort/indexed/super chain) + foldGateResult, unsizedTest
  (indexed/super), the sizing evaluator `sz_eval`/`sz_body`/`sz_step`
  (= transformNoDeferM over basicStepM/stuckStepM/abortStepM/
  indexedAbortStepM/indexedInputStepM/indexedSuperStepM/superStepM/
  superAbortStepM/unsizedStepM''', with StrictAccum as explicit (Expr, SR)
  threading), UnsizedStub 4-deep env destructuring + rf synthesis, lazy
  iteB, SizeStepStub unroll with maxSize abort, getInputLimits (il_eval +
  pure barrier evaluator pv_eval + extractInputRestrictions),
  removeRefinementWrappers, capMain/initialInput/uncap/setSizes/foldAborted,
  and `size_term` (doCap 0/1).
- **Bit-path IVars**: Haskell indexes the input tree with Integers
  (left = 2n+1); `$127 left x` reaches index ~2^128 — far beyond u24. IVar
  positions and EitherP tags are bit paths (List(u24), 0 = left);
  `decendant` becomes prefix testing.
- Verified (`bend/test_sizer.bend`, uncapped path): d2c/dPlus/foldr/map/
  dEqual/dMinus size correctly and EVALUATE to the right values after
  bound substitution (7/7 cases). Capped path verified at small depth:
  a `$3`-bounded input refinement extracts zeros, sizes, uncaps, and the
  full telc pipeline runs a refinement-checked interactive program
  (scale tests at $7/$15/$31 pass, ~85s wall each, constant memory).
- The end-to-end driver `bend/telc.bend` now implements evalLoopCore:
  s2b/b2s, funWrap iteration, input-line replay, "done" on Zero state —
  M5's core is functional (echo program runs; correct runtime aborts on
  refinement violations).
- **PERF WALL — root-caused and fixed** (two strictness bugs vs Haskell's
  lazy heap, found by phase-isolated ITRS measurements):
  1. **Superposition env filters materialized**: `sz_fill` on an applied
     `EitherP` closure strictly rebuilt TWO filtered copies of the env per
     unroll level (Haskell leaves `filterLeft/filterRight` as thunks that
     mostly die unforced) → env doubles per level → 2^k. Fix:
     `super_filter_work` one-pass scan; filter only when the env actually
     contains matching-tag superpositions, else pass the shared env
     through. (mini d2c @$31: 123s → 68s; capped unrolls flat.)
  2. **Strict Gate branches in the RUNTIME evaluator**: `splitExpr` builds
     user if/then/else with the STRICT `iteB_` (`SetEnv(Pair(Gate(e,t),i))`,
     Telomare.hs even carries the "doesn't incorporate laziness" warning).
     Haskell's transformNoDefer evaluates children lazily, so the
     GateSwitch discards the unpicked branch unforced; my strict bottom-up
     eval evaluated BOTH branches — on the compiled recursion towers the
     continue-branch is evaluated even at termination → 2^n runtime.
     Measured: sizing+setSizes at $36 = 258M ITRS (fine); the eval phase
     alone exploded >2G. Fix (ir.bend): Gate children stay CODE — eval_body
     substitutes the env structurally (`subst_env`, defer-bodies skipped),
     eval_expr leaves Gate branches untouched, and step_setenv evaluates
     only the branch the switch picks. (mini d2c: $39 52s, $63 66s —
     previously OOM at >536M nodes.)
- Sizing engine measured healthy standalone: linear result size
  (+442 nodes/level) and near-linear ITRS to $63 (464M, correct bound 64).
- Post-fix status by phase (all measured):
  - sizing at `$127`: fine — mini d2c sizes + runs in 146s under plain
    run-c (fits the 33M window).
  - runtime on ZERO/small values: fine at any bound.
  - runtime `dEqual` on a real character under a large bound: correct
    results at bound ≤ 47 (`ne|ne|abort` transcripts match oracle
    semantics), but cost grows steeply with the BOUND (tower height) —
    bound 128 with a 35-deep char OOMs 536M nodes. This is the open
    constant/complexity item for full-`$127` interactivity; suspicion is
    strict full evaluation of accumulator values that Haskell only forces
    to WHNF through the reserved-capacity surplus levels. Timings above
    are noisy (concurrent parity run); to be re-measured on a quiet box.
- The oracle itself needs 74s to compile+run tictactoe (its own analysis
  is heavy) — the port being within ~an order of magnitude of GHC on the
  sizing side is consistent with measurements so far.
- **M6 result: DNF (honestly recorded).** tictactoe parity at bound `$63`
  (chars '1'-'9' are ≤57 deep, so gameplay is identical for valid moves;
  both compilers got the same `$63` file): the oracle produced its golden
  transcript in 67.5s; the Bend run hit the 536M-node ceiling after ~2.5h
  on the single-thread binary. The pipeline stages are all individually
  verified (sizing of full tictactoe works; the evalLoop runs real
  interactive programs; `dEqual` on real chars verified correct at bound
  ≤47) — the remaining blocker is purely the runtime evaluator's cost on
  real-character data under large fuel towers: strict full evaluation of
  every intermediate value where GHC forces only WHNF through the
  reserved-capacity surplus. The identified fix is a WHNF-style
  (demand-driven) evaluator for ir.bend — a structural rewrite of
  eval_expr/eval_body (explicit thunks or CPS), left as the top TODO.
- **HVM2 lesson #6**: the C runtime does NOT exit on OOM — it loops
  printing `OOM` forever (one parity run wrote an 8.5GB transcript of
  "OOM" lines before being killed). Always cap output (`head`/`grep -m`)
  and never trust exit codes alone; check for the OOM marker.

## 2026-07-03 — H: the hybrid pipeline (Haskell front end, HVM2 runtime)

Direction change (user): stop self-hosting the front half. GHC runs
parse → resolve → Possible.hs sizing (the part that needs lazy graph
reduction — 68s for tictactoe where the Bend port DNF'd at 4+ hours),
then a new Haskell emitter produces the same defunctionalized generated
program this port's `bend/emitter.bend` pioneered, and HVM2 executes it.

- `src/Telomare/HvmBackend.hs` — Haskell twin of `bend/emitter.bend`
  (same TV encoding, per-fid `d<slot>` defs, lifted gate matches,
  tvDispatch switch, evalLoop driver). Emission is instant under GHC.
  `telomare --emit-hvm foo.tel` prints the program; split point is the
  `CompiledExpr` right after `findChurchSizeD` in `Telomare.Eval.compile`.
- `bend/run_telomare_hvm.sh` + flake app `.#telomare-hvm` — same
  two-stage driver contract as the self-hosted version, but stage 1 is
  the GHC binary (cached by source+binary-content hash). Runners:
  `gen-hvm` (default), `bend-run-c`, and `gen-c-big` (gen-c + gcc,
  single thread, arena raised to 1<<30; binary cached; avoids HVM2
  lesson #6's OOM print-loop).
- `src/Telomare/HvmBackendCcc.hs` (`--emit-hvm-ccc`) — the ConCat-style
  experiment patterned on agda:ctc/src/HVM.hs: CompiledExpr interpreted
  into a Bnd combinator term over a closure-based prelude (Defer=curry,
  SetEnv=apply, TV/L holds real lambdas). Outcome exactly as predicted
  by this port's defunctionalization story: e1 (affine) works; echo's
  church towers die on BOTH runtimes (`Result: *` erasure on run-c,
  "clone a non-affine global reference" on the lazy runtime). That is
  the definitive "why defunctionalize" data point.

Results (oracle-diffed): e1 0.15s end-to-end; simpleplus parity;
echo-`$127` parity 15s cold / 1.6s warm (was 734s self-hosted).

**Tictactoe: understood, not fixed.** One evalLoop iteration of the
sized game does not complete on any HVM2 configuration: interpreter and
134M-node/thread compiled binaries OOM-loop; a single-threaded 1B-node
(~13GB) binary stops OOMing but produces no result in 30 min ($127) /
40 min ($63); the lazy Rust runtime refuses the encoding outright
(cloning refs to non-affine defs — every `d<slot>` uses env non-affinely).
GHC evaluates the same CompiledExpr in under a second. Root cause is the
interaction-net cost model: shared reads COPY structure through dup
nodes, and tictactoe re-reads its board through hundreds of gate checks
inside `$127` abort towers — copies of copies, a ~10^4–10^5 interaction
gap. Same wall the tree-walking interpreter hit (536M-node OOM at $63),
so it is intrinsic to this program shape on HVM2, independent of
encoding. Future leverage: emission strategies that keep bulk state out
of the copied path, or an HVM with by-reference shared reads.

Driver/emitter hardening landed with the diagnosis: `tel_main()` is
computed once, forced/rebuilt in `main` (dup lands on data, not on a
bare nullary ref), and threaded through the loop — HVM2 re-unfolds
nullary global refs at every reference site otherwise.
