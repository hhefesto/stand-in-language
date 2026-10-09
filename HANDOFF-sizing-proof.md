# HANDOFF — sizing-proof: proving sizing sound for every program

Written 2026-10-08. Branch `sizing-proof`, cut from `bend-port` at
`e3480b1`. Its work merges back into `bend-port`.

**What this branch is for.** On bend-port, sizing's counts are trusted.
Since P7.6 (`e64b80a`), a program sizing proves gets inert chain bottoms,
and its discharged refinement checks become plain values. Nothing proves
that sound. This branch builds a machine-checked proof, in Bend 2, that
every such erasure is sound:
- no input the session can give main reaches an erased bottom or an
  erased check;
- so erasing them changes nothing;
- and the sized program computes what the unbounded program computes.

**This file is committed only so it travels**, like bend-port's HANDOFF.md.
Drop its commit ("Hand off sizing-proof …") before merging into bend-port.

That commit also does two other things:
- It adds `bend/dev/gate.sh`.
- It deletes bend-port's HANDOFF.md, which this file replaces on this
  branch. Dropping the commit brings it back untouched.

When rebasing onto a bend-port whose HANDOFF.md has changed since, git
reports a modify/delete conflict. Keep the deletion (`git rm HANDOFF.md`).

**The port handoff** is bend-port's HANDOFF.md as it stood at the cut:
`git show e3480b1:HANDOFF.md`. It holds the P1–P7 history and the research
behind it. The parts this branch needs are carried over in §10–§15.

Line numbers are as of `e3480b1`. Search for the definition named when
they drift.

Contents:
0. Status
1. Working rules
2. The goal, stated exactly
3. Where things stand
4. The approach
5. The plan: S0–S5
6. Decisions for the user (and Sam)
7. Reference: sizing, read as a prover must
8. Reference: proofs in Bend 2
9. Risks
10. Setting up a machine
11. Verifying
12. Dev tools and the parity corpus
13. Layout
14. Bend 2 gotchas
15. Nix gotchas

---

## 0. Status (2026-10-09)

The user asked to run the plan, stopping at decisions. bend-port is the
Bend version that keeps up with master's behaviour, so D2 was settled
that way. Committed on `sizing-proof`:
- "Add Sem, the core's meaning, and an erasure checker": Sem, the
  checker, `chain.over`, and the parity test;
- "State sizing's soundness laws, …": the laws, and the proof of
  `fuel_more`;
- "Prove sizing's semantic laws": the proofs of `what_runs`, `erasure`
  and `counts_suffice`;
- "Prove the certificate laws": the proofs of `certificate_opening` and
  `certificate_guarded`. With them every law in `bend/LAWS.bend` is
  proven, and `PROOF.bend` joins `Everything.bend`.

Each passed the gate and `nix flake check`. Nothing is pushed.

**D1 decided (2026-10-09).** The user approved `bend/LAWS.bend` as it
stood, with one amendment. Checking the laws for counterexamples before
proving them showed `what_runs` false as written: it took any `E.X` as
input. Take an input that is itself an `XCheck` numbered like one of
main's erased checks, with a failing test, and main the identity. The
witness erases the input's check and answers 0. The program that runs
erases nothing in its input, so it runs that check and aborts, at any
fuel. A run in Bend confirmed it. The user chose to take only data
inputs (`Co.D`, run on `Sm.of.data(input)`). That is what the session
gives main, and what the certificate laws already quantify over. The
amendment is folded into the laws commit.

**Done:**
- **S0.1:** the filter fix landed on bend-port as `822f0c5` (plus a
  handoff fixup, `c66e7e0`), and sizing-proof was rebased onto it. Not
  pushed.
- **S0.2:** `bend/dev/fastdiff.sh`, run on 100 generated sessions each
  of tictactoe and simpleplus: no sized/`--fast` difference.
- **S1:**
  - `bend/Sem.bend`, the meaning. It is strict like the IC, not lazy as
    first planned; §2 says why.
  - `bend/tests/sem.bend`: Sem and the IC show the same displays on tc,
    three simpleplus sessions (one aborting at the guard) and three
    tictactoe games, in about 3 s.
  - `bend/LAWS.bend`: six laws, a draft waiting on D1.
- **S1 spike:** `fuel_more` is proven in `bend/PROOF.bend`, about 200
  lines, in a few rounds against the checker. A planted error is caught.
  It also passes `--verdict`, BendTT's Lean-proven kernel (built as §8
  says). So does `Sem.bend` with its imports.
- **S2:** `what_runs`, `erasure` and `counts_suffice` are proven in
  `bend/PROOF.bend` and rechecked with `--verdict`. One simulation lemma,
  `sim`, covers laws 3 and 4. A second, `runs`, with `prog_witness`,
  covers law 2 (§5). `bend/dev/gate.sh proofs` checks the proofs, and
  the kernel too when `BENDTT` is set.
- **S4:** `certificate_opening` and `certificate_guarded` are proven for
  checker v1, and rechecked with `--verdict` (§5). All seven laws hold:
  `bend bend/PROOF.bend --verdict` prints ALL PROOFS CHECK. PROOF.bend is
  about 7,700 lines.
- **S0.3, tictactoe:** the 5,000,000-run check (`check tictactoe
  5000000`) hit its 10-hour limit without a verdict (exit 124). Earlier,
  50,000 runs had found no input that fires a site. So no counterexample
  is known (D4 does not arise), but checker v1 cannot prove tictactoe
  within any budget a compile could afford. That is D3.
- **S3, executable half:** `bend/Check.bend`, with `bend/dev/check.bend
  MODULE [RUNS]` to run it. Every erasure is proven, without counting the
  checker's own soundness, which is S4:
  - tc_ultra_minimal: 7 runs;
  - simpleplus: 14,163 runs, 3.6 s;
  - all 15 corpus programs: 1 run each, since they ignore their input.

  The checker is not yet wired into `Sz.discharged`, which would change
  outputs.

**Next** (each waits on the user):
- **S3, the rest:** wire the checker into sizing. Then the compiler
  erases only what the checker proves, and the theorem covers what runs.
  tictactoe would keep its bottoms (D3), which changes its outputs back
  to P7.5's.
- **A `--verdict` check in `nix flake check`.** It needs BendTT's kernel,
  which needs Lean 4.34 (§8), so a new nixpkgs input. Until then
  `gate.sh proofs` runs it by hand, and `bend-check` checks the proofs
  without the kernel.
- **The README's "Design" note** on the theorem and its trusted base,
  once the checker is wired in.

## 1. Working rules

These are the user's standing instructions. Claude's memory directory
(`~/.claude/projects/-home-hhefesto-src-telomare/memory/`) does not travel
with the repo, so they are repeated here.

- **Never** add a Claude co-author or attribution line to commits or PR
  bodies.
- "Success" means local success. Ask before every `git push`; one approval
  covers one push. Open a PR only when asked.
- Keep this file current as work progresses.
- Make few, well-designed commits with succinct messages: one per step,
  each gated.
- Bend comes only from the flake input (`github:bendlang/bend`), and the
  only oracle is haskell-final. Use nothing from `~/src/formalTransformer`
  or `~/src/bend2`.
- Code must be elegant and fit the existing design naturally. Backtracking
  is fine.
- DESIGN.md is Sam's (sfultong). Don't edit it. Record resolutions in the
  README's "Design" section and here.
- Outputs stay byte-identical to haskell-final's unless a difference by
  design is listed. A difference gets a `test/golden/port/NAME`
  expectation and a line here. The earlier ones are in the port handoff's
  §7.
- Changes to this file go in `fixup! Hand off sizing-proof: …` commits.
  Shipping commits touch only `bend/`, `README.md`, `test/` and `nix/`.
- Run memory-heavy jobs one at a time, and cap the oracle with
  `GHCRTS=-M8G`. Nix builds take `--out-link` GC roots.
- Give `tail -F` commands for background jobs.
- `notes.md` is private. Never commit it.

**The gate** for a shipping commit:
- `bend/dev/gate.sh`, which does build, the bend tests, the goldens and the
  corpus, exactly as P1–P7 ran them (§11, §12);
- `nix flake check`;
- the pre-commit hook (`bend bend/Everything.bend --check-only`).

`gate.sh` (in `all`, or `gate.sh proofs`) also checks `bend
bend/PROOF.bend`. It must print ALL PROOFS CHECK, or exactly the open
laws as TODOs. With `BENDTT` set (§8), it rechecks the proven laws with
`--verdict`.

## 2. The goal, stated exactly

**The objects, as built:**
- `x`: main as sizing receives it (`E.of.term3(run)`), with an `XStub`
  per recursion site and an `XCheck` per refinement check.
- `counts`: sizing's counts.
- **The witness**, `Ck.witness(counts, x)` (Check.bend):
  - each `XStub` becomes its chain of `count + 1` links
    (`E.chain.over`, Expr.bend) over the `XStub` itself, which stands for
    the rest of the recursion;
  - the `XCheck`s stay.
- **A policy**, `Sm.Pol{mode, checks}`, says what the erasable sites
  mean. The erasable sites are the checks sizing erases
  (`Ck.erasable(x, left)`, i.e. every check not left to run time) and
  every chain's bottom. The modes:
  - Watch: a mark (below);
  - Erase: the check's value, and 0;
  - Limit: the check's value, and the recursion unbounded.
- **What runs** is `Sz.program(counts, Some{left}, True{}, x, False{})`:
  the program the compiler hands the runtime when sizing proves main.
- **Admitted inputs:** 0, the opening call, and every datum the session's
  guard passes.

**The meaning, `Sem`** (bend/Sem.bend):
- It evaluates in the IC's order. Every value is computed once, except the
  strict `if`'s branches: only the chosen one runs, as the IC has done
  since P4.
- Aborted and stuck values are values.
- It is indexed by fuel (the depth of evaluation), because Bend demands
  termination.
- An `XVar` is an input position not yet known. A run that needs its shape
  stops with `Needs`.
- Watched, a bottom, and an erasable check whose test does not give 0,
  become a **mark**. A mark travels as an aborted value does, and ends the
  run with `Fired` if it reaches the result.
- It is shaped for proof. Each step is a value, `sem` on a job a pure
  helper picks, or a pure function of `sem`'s results. That is what kept
  `fuel_more` to about ten cases.

**Why strict, not lazy as first planned:**
- The call-by-name draft re-evaluated shared work without bound. It never
  finished tc_ultra_minimal.
- Strict evaluation is what the IC, the one runtime, does, and it computes
  each value once.
- The cost: under strict evaluation `--fast` can loop in dead code that the
  sized program finishes. The IC has the same limitation.

**Why marks travel instead of firing when used.** Under strict evaluation
dead code uses values. A let's argument, for instance, is computed whether
or not it is used. In simpleplus the opening call computes `left inString`
from a failed check and then discards it. So a mark matters only if what
is computed from it reaches the result. That is sizing's own rule: an
abort counts only if it reaches the result. A mark inside an abort's
message makes the whole aborted value a mark, so `trunc` cannot swallow
it.

**The laws** (bend/LAWS.bend, approved at D1):
1. `fuel_more`: more fuel never changes an answer. **Proven.**
2. `what_runs`: on a data input, what runs answers as the witness does
   under Erase, given enough fuel. **Proven.**
3. `erasure`: if the watched witness answers (so no mark reaches the
   result) and the erased one answers too, they give the same answer.
   **Proven.**
4. `counts_suffice`: the same for Limit, i.e. the recursions unbounded
   past their chains. **Proven.**
5. `certificate_opening` and `certificate_guarded`: if the checker proves
   main, the watched witness fires on no admitted input, at any fuel.
   **Proven.**

Together they say: on every input the session can give main, what the
compiler erased could not have mattered, and the recursions had all the
links they needed.

Laws 3 and 4 compare answers where both runs give one. Under strict
evaluation, the erased run may compute dead values the watched run never
does. That every run of a certified program ends is EAL's promise (C2),
not these laws'.

Law 4 is about the witness under Limit, not `E.unbounded(x)` itself. A
chain link and `limit.code` are different closures. A program that takes a
recursion value apart instead of applying it could tell them apart, so
equating the two needs a representation lemma, which is not attempted.

"Every program" means every program the compiler builds. A program the
checker cannot verify keeps its bottoms and checks. That is P7.5's
behaviour, DESIGN §10's part 2, and the laws then hold trivially.

**Not covered: the trusted base.**
- `Sem` is the meaning. It is checked against the IC by tests
  (`tests/sem.bend`), not by proof. Proving the IC sound (optimal
  reduction of EAL-typable nets, §7) is a separate, larger project.
- Termination is EAL's promise (C2 through §5).
- The front end (parse to Term3), and the session loop.
- Bend's checker. `--verdict` re-checks with BendTT's kernel, which has a
  proof in Lean.

## 3. Where things stand

**The evidence today is testing:**
- The goldens (38 checked) and the 15-program corpus pass, with displays
  and counts as haskell-final's apart from the differences by design
  (the port handoff's §7).
- Sizing is a transcription of haskell-final's, which was never proved
  either.

**The re-run P7.6 removed.** Until P7.6, a second symbolic run confirmed the
bottoms dead before erasing them. The code is `bottomed`, `as.ran` and
`opening.bottomed`, visible with
`git show e64b80a^:bend/Size.bend | sed -n 1195,1257p`.
- It confirmed tc, simpleplus and every corpus program.
- It reached two of tictactoe's bottoms:
  - #0, Prelude:30:18, the `d2c` in `minus`, `<= 79`;
  - #13, tictactoe:96:45, `d2c nextPlayer`, `<= 2`.
- It used sizing's own evaluator, so it was a consistency check, not an
  independent one.

**Over-run since P7.6:**
- An erased bottom is 0, and applying 0 gives a stuck value.
- If that value is demanded, the session prints
  `IC runtime: ICStuck "applied value is ICZero, not a function: 0"`.
- So an over-run is still an error, just one that doesn't name the
  recursion.

**Found 2026-10-08: the port's left-branch superposition filter is
inverted.**
- haskell-final's `filterLeft n` keeps the left alternative of a
  superposition at or below the choice position `n`, and leaves every other
  superposition alone (`src/Telomare/Machine.hs:211-214` at `haskell-final`;
  `decendant x d` is "x is d or below it", 673).
- The port's `filter.at` (Size.bend:376) does the opposite:
  `merge.pick(Bool.not(below(q, n)), …)`.
- The comment above `filter` describes Haskell's behaviour. The code
  disagrees.

A probe of `Sz.filter.at`, with the left alternative `a` and the right `b`:

| branch | choice at | superposition at | haskell-final | port |
|---|---|---|---|---|
| left  | L  | R (unrelated) | both | **a** |
| left  | L  | L (same)      | a    | both |
| left  | L  | LL (below)    | a    | both |
| left  | LL | L (above)     | both | **a** |
| right | L  | L (same)      | b    | b |
| right | LL | L (above)     | b    | b |
| right | L  | R (unrelated) | both | both |

What the rows mean:
- The **a** rows drop an alternative some input takes. Sizing can then miss
  a path, which can make a count too small. It can also discharge a check
  wrongly, since `reaching` decides which checks are discharged.
- The "a → both" rows only lose precision.
- The only way in is applying a superposed closure (an `XEither` in
  function position, Size.bend:834-836).
- The goldens and the corpus still pass, so on every tested program the
  inversion changes no count and no check. Which programs reach it is
  unknown.

## 4. The approach

**Translation validation, not a verified sizer.** Prove a *checker* that
looks at the program sizing produced, not sizing itself. CompCert validates
its register allocator this way, and CeTA checks termination proofs this
way. The reasons:
- Sizing must keep matching haskell-final's counts and certificates byte
  for byte, so it can't be reshaped for proof.
- Sizing leans on Strings, Maps and U32 tokens, and has approximations
  (§7) whose soundness argument has never been written down.
- A checker is new code, free to take whatever shape a proof wants.
- A checker that fails is safe: the program keeps its bottoms and checks.
  Soundness holds from day one, and completeness can grow program by
  program.
- The certificate stays the counts. Sizing emits nothing new.

**One lemma does most of the work: what never reaches the result never
mattered.** A watched run carries a mark wherever an erasable site would
make a difference, and the mark travels with everything computed from it.
If no mark reaches the result, then putting the check's value or 0 there,
or the unbounded recursion, gives the same answer wherever that run gives
one. The lemma is a simulation between two runs of `sem`, in which a mark
on one side stands for any value on the other. It is used three times:
1. **Erasure** (law 3): the marks at erased checks and bottoms.
2. **The counts suffice** (law 4): the marks at bottoms, with Limit.
3. **The checker** (laws 5): input holes. Suppose a run on a partial input
   never needed a hole's shape. Then it gives the same answer on every
   input that fills the hole.

**Checker v1, built: forking symbolic execution on `Sem` itself**
(Check.bend).
- It runs the watched witness on a partial input, starting from `XVar ""`.
- A projection of a hole is a hole: the left of input position `p` is
  `pL`, as with sizing's `XVar`. This holds because `Left 0 = 0`.
- When a run needs a hole's shape (`Needs p`), it splits the hole on the
  way to `p` into 0 and a pair, and runs each side again.
- The guard runs first on the same partial input and prunes what it
  refuses. That handles the boundary exactly, with none of the limits
  pass's `extract`/`exact` (§7).
- It accepts when no leaf's run lets a mark reach the result. A leaf where
  one does names a concrete input. A budget that runs out (runs, or depth)
  gives "unknown".
- Proof: the lemma, plus "the leaves cover every input" (induction on the
  split tree).
- Cost: exponential in the input positions inspected.
  - Characters are unary numbers, so the guard's digit test splits once
    per level, and strict evaluation looks at every character before the
    guard decides.
  - simpleplus takes 14,163 runs.
  - tictactoe (board, player and line) is in the millions.

**Checker v2, only if tictactoe-class programs must be erased:
decision-tree values.**
- Fork locally instead of at the top. An abstract value is a decision tree
  over input positions, `If(p, zero-case, pair-case)`, with every node
  tagged by its position.
- An environment handed to a branch is restricted by that branch's path
  condition.
- This is sizing's `XEither` domain made exact:
  - no untagged nodes (`fold.gate`'s `XEither{None{}, …}`, Size.bend:348);
  - no `test.pick` collapse;
  - a filter that is proven.
- The relation: `select(d, X)` resolves each node by the shape of `d`. The
  law: `Sem` on `d` agrees with `select(d, AbsEval(…))`. The proof is
  medium to large.

**Not chosen: verifying Size.bend directly.** It would need sizing's run
related to the run of the chains: stub unrolling, depth recording, `XTest`,
`test.pick`, the `XError` fallbacks and the limits pass. All of that lives
in code pinned to haskell-final. Keep it as the fallback if the checkers
can't reach the programs that matter.

## 5. The plan: S0–S5

Each step is one or a few gated commits. Stop at the decisions in §6.

### S0. Ground truth, no proofs (small; first)

**S0.1. Fix the filter inversion. Done:** bend-port `822f0c5`.
- The `Bool.not` was replaced by a `filter.left` that mirrors
  `filter.right`.
- The `size-filter` group pins the seven cases of §3.
- No golden or corpus output changed. The full gate and `nix flake check`
  passed.

**S0.2. Differential test, sized vs unbounded. Done:**
`bend/dev/fastdiff.sh BIN [SESSIONS [SEED]]`.
- 100 generated sessions each of tictactoe and simpleplus (seed 7): no
  difference.
- A difference would mean an over-run (the erased bottom's stuck error) or
  a wrongly discharged check.
- It reaches only the states a session reaches. The laws cover every state
  the guard admits.

**S0.3. tictactoe's #0 and #13. In progress, by checker v1 rather than by
the old re-run.** The checker answers the question directly. A leaf where a
mark reaches the result is a concrete input that over-runs, and "proven"
rules every such input out. 50,000 runs found nothing. The 5,000,000-run
check is in §0. If it fires, that input is a sizing bug: fix sizing, and
see D4.

### S1. The specification (medium; ends at D1). Done but D1

- **`bend/Sem.bend`:** the meaning (§2). It joins `Everything.bend`, as
  `Check.bend` does.
- **`bend/LAWS.bend` and `bend/PROOF.bend`:**
  - `bend bend/PROOF.bend` prints SOME PROOFS FAIL with "5 TODOs" until the
    other laws are proven.
  - Both were kept out of `Everything.bend` while laws were open, since
    its check and the pre-commit hook expect ALL PROOFS CHECK. Since S4,
    PROOF.bend is in it.
  - The law statements use `Sm.answered(r)` (Unit for an answer, Empty for
    Spent) instead of `r != Spent`. Bend uses a function at most once, but
    a Data witness can be reused.
- **`bend/tests/sem.bend`:** sem-tc_ultra_minimal, sem-simpleplus and
  sem-tictactoe (listed in `nix/bend.nix`, run by `gate.sh`). It compares
  against the IC unguided, which shows the same displays.
- **The spike:**
  - `fuel_more` is proven, and passes `--verdict`.
  - Lessons:
    - Shape definitions for proof: no deep or default patterns in what a
      proof must unfold.
    - Hypotheses that are used twice must be Data.
    - A curried application must stay on one line.
    - "fin"-style helpers match computed results, as Bend's
      insertion-sort demo does.

### S2. Semantic lemmas, proven (medium). Done

- `what_runs`, as built (PROOF.bend, "Law 2: what runs"). `Sem` under
  Erase reads an erasable `XCheck` as its value and an `XStub` as 0,
  exactly what `E.resolve.checks` and an inert `E.bottom` write.
  - `prog(es, x)` translates the witness into the program: an erased
    check is its value, a kept one `E.check.of(True{}, …)`, a stub 0.
    `prog_witness` proves `prog` of the witness equal to `Sz.program(…)`,
    by induction on x.
  - That needs `Sm.has(Ck.erasable(x, left), site)` to be
    `Bool.not(Ck.kept(left, site))` for each kept site of x
    (`erased_iff`, `cov_x`). So `U32.is_eq` must reflect equality
    (`u32_eq`, `u32_refl`), by induction over `Word.cmp`'s 32 bits.
  - `runs`: where the witness's run under Erase answers a value, the
    program's run under `Sm.plain()` answers it too, on the same fuel.
    The program is a step ahead at each check (`fm_step`).
  - One case needs care: erasing a check can give the program the strict
    if's shape (`ifx`) where the witness has a general application. Then
    the program runs the strict if. `if_gen` proves the two agree
    wherever the general one gives a value.
  - A data input has no check or stub, so `prog` leaves it as it is
    (`prog_data`).
- `erasure` and `counts_suffice`: the mark simulation (§4), as built
  below.
- After S2, P7.6's erasure is proven correct on every input where the
  watched witness answers. What remains is knowing that for all inputs
  statically: S4.

**The mark simulation, as built** (PROOF.bend, "The mark simulation").
- `fil(w, v)` is w with each mark replaced by what stands at its place
  in v. w stands for v when `fil(w, v) == v`. `rfil` lifts that to
  results: a watched result that is not a value stands for any result,
  and anything stands for a result that is not a value. The relation is
  an equation rather than an inductive one, so it can be reused (`+`) and
  rewritten with.
- `mj(j, ee, re)` is the job the other mode runs where the watched run
  runs j. It is the same job over ee's filling of j's environment and
  re's of its result. A watched check (`JWatch`) is its value there.
- `sim(f, lim, checks, jw, ee, re, k)`: the watched run of jw on fuel f
  stands for the other mode's run of `mj(jw, ee, re)` on fuel f + k. The
  other mode is Erase, or Limit if lim. The slack k is for watched
  checks: the watched run spends a step on the test, so the other run's
  value is compared one step later (`add_succ`).
- `set_step` and `if_step` take the cases that inspect two results
  (`JSet`, `JIf`). They take the induction hypothesis as an argument
  (`@j: Sm.Job -> …`), because matching `re` in `sim` after the job's
  fields would consume them (§14).
- `no_obs`: `sem` never answers `Obs`, which only readback does. Without
  it the related results could be two unrelated readings.
- `fuel_plus` is `fuel_more` k times, so both runs compare at
  wfuel + mfuel. `agree(lim, …)` then gives both laws.

**The original sketch** (kept for the reasoning behind the cases).

`vw ~ ve` ("the watched value stands for the erased one") holds when:
- `vw` is a mark: then any `ve`;
- or both are the same leaf (`WZero`, `WGate`, `WAbort{at}`, `WStuck`,
  `WHole{p}`, `WAborted{at, m}`, `WCode{fi, body}`, with the same body);
- or both are pairs, related part by part.

Without marks, `~` is equality, and that is how the conclusion's readbacks
come out equal. A mark in the result fires, so the watched answer has none.

Jobs are related the same way: the same constructor over related
environments and results. There are three extra pairs, for the places
`step` reads the policy:
- `JWatch{site, tc, c, envw} ~ JE{c, enve}`;
- `JDone{Val{WMark…}} ~` any job (the bottom, and a failed check);
- `JE{E.check.of(…), envw} ~ JE{E.check.of(…), enve}` for kept checks.

The lemma: if `sem(f, Watch, Jw)` and `sem(f', Erase, Je)` both answer (not
Spent and not Needs), their results are related. The induction is on `f`,
case by case on the job, as in `fuel_more`. The cases that do the work:
- **Eliminating a mark:** `left.of`, `set.of`, `branch.of` and `abort.of`
  of a mark give a mark, which is related to whatever Erase computes.
- **A strict `if` on a mark:** Watch gives the mark. Erase runs a branch,
  and since the erased run answered, that branch gave a value.
- **`checked`:** the test gave 0, so the value is `c`'s on both sides;
  otherwise the result is a mark.
- **`abort.of` on a pair holding a mark:** a mark (`marked.or`).

Answers do not depend on fuel once given (`fuel_more`, extended by
induction to any larger fuel), so the two runs can be compared at the
larger of the two fuels.

### S3. Checker v1, executable (medium). Built; wiring left

**`bend/Check.bend`** is built (§4), and so is its dev tool. Wiring is
left:
- Call it from `Sz.discharged` (Size.bend:1210), or from Main after
  sizing, with the guard's sized program.
- Erase only when sizing says `proven` and the checker says proven.
  Otherwise keep every bottom and every check, as P7.5 did for tictactoe.
- Budget: simpleplus needs about 15,000 runs. Pick one that keeps compile
  time sane.

**Gate.**
- Outputs are unchanged for the programs it proves.
- Re-pin where it does not. If tictactoe is unknown:
  - `ic-meter-tictactoe` and `port/tictactoe.ic-meter` go back to
    5,938,558;
  - `size-erased`'s tictactoe line goes back to "Abort";
  - the `.compile` digest changes.

**Also:**
- Measure compile time. Sizing is meant to be paid once (DESIGN §4), and
  the checker joins it.
- Whether `--certificate` should say which erasures are proven is an output
  change. Ask the user.

### S4. Checker v1, proven (small to medium, given S2). Done but the flake check

As built (PROOF.bend, "Laws 5: the certificate"):
- `certificate_opening`: the checker's opening run read back an answer
  (`opened_v`, `opening_obs`). Two runs that both answer agree
  (`fuel_agree`), so no run on any fuel fires.
- `certificate_guarded` rests on a second simulation, `hs`: the run on a
  partial input against the run on any data under it (`refines`). A hole
  stands for data or a hole, and an aborted value for one with any
  message (`hf`). Both runs use the same policy, so it is lockstep.
  - The input itself is evaluated in different numbers of steps, so the
    runs are joined job by job through `E.app` (`app_rel` … `app7`,
    `in_rel`). The data's run gets the extra fuel.
  - A reading on the partial input means the data's run never fires
    (`no_fire_rel`). That needs `no_fired`, beside `no_obs`: `sem` never
    answers `Fired`.
  - A guard that refuses the partial input refuses the data
    (`guard_leaf`, `bad_rel`, `wbad`).
  - `tree` follows `Ck.explore`. Every input under a node lies under one
    side of its split (`split_cover`), and `good` says what each job
    promises.
- Still open: a `bend-proof` check in `nix flake check`, so that
  `bend bend/PROOF.bend --verdict` must print ALL PROOFS CHECK. It needs
  the kernel built in Nix (§0).
- The README's "Design" section records the theorem and its trusted base.
  DESIGN §10's second conflict ("the chain relies on a runtime abort as its
  safety net") is then resolved by proof, for every program the checker
  accepts.
- Merge into bend-port, dropping this file's commit first.

### S5. Checker v2 (large; only if D3 asks for it)

- Build the decision-tree domain (§4) and prove it behind the same law 3.
- Then tictactoe, and programs like it, lose their bottom aborts with a
  proof.

## 6. Decisions for the user (and Sam)

**D1 (decided 2026-10-09): the laws' wording,** `bend/LAWS.bend`.
Approved as drafted, except `what_runs`, which was false as written and
now takes data inputs only (§0).
- The meaning is the IC's evaluation order (§2), not a lazy one.
- The inputs are 0 plus whatever the guard admits, not only the states a
  session reaches. Sizing claims every input, and DESIGN §6 keeps the
  session out of totality ("each turn is a total function call").
- The observation is the full readback, with abort sites and messages. A
  closure shows only as its function index.
- Erasure and the counts are stated where both runs answer, leaving
  termination to EAL.
- These pin down what a Telomare program means, so Sam should see them.

**D2: decided** (2026-10-08). The fix landed on bend-port, which keeps up
with master's behaviour.

**D3 (after S3): residual aborts.** Is it acceptable that programs the
checker cannot verify keep their bottoms, as a residual runtime abort
(DESIGN §10's part 2)? If tictactoe stays unknown and must lose its
aborts, S5 is needed.

**D4 (only if the tictactoe check fires): revert P7.6** on bend-port, and
go back to P7.5's confirming re-run until the checker is wired in.

## 7. Reference: sizing, read as a prover must

**Sizing's three runs** (Size.bend:7-25):
1. The limits pass: recursions opaque, checks evaluated over the symbolic
   input to learn which input positions must be 0 or pairs (`extract` 665,
   `exact` 712).
2. The main run over the symbolic input (`initial.input` 951,
   `main.run` 1249).
3. `set.sizes` (1126) turns each site into `count + 1` links (`count.of`
   1114). A site never reached gets 1.

**The evaluator** (`eval` 759-898):
- It is strict: children first, outside Defers. So both branches of the
  strict `if` are evaluated, because `XPair` evaluates before the gate
  selects.
- Recursion unrolls lazily through `ite` (`E.step.body`, Expr.bend:167).
- Its fuel is 2^32−1 (`fuel` 399). Running out gives `XError`.

**The approximations, every one of which a proof must justify or avoid:**
- **Poison.** Aborted values (`XAborted{site, m}`) and `XError` flow as
  values. Only those in the final result count (`fold.aborted` 1019).
  That's right for a lazy meaning, except where `trunc` (479) swallows
  them inside an abort message (§4).
- **Superpositions** (`XEither{name, a, b}`):
  - created by a gate on an input position (`gate.var` 495);
  - merged when shallowly equal (`merge.shallow` 282);
  - folded at gates (`gate.result` 317, `fold.gate` 359). An aborted
    outcome there joins with an **untagged** `XEither{None{}, …}`, and
    correlation is lost.
- **Path correlation.** Applying a superposed closure filters its
  environment (`filter.side` 402, `filter` 386, `filter.at` 371):
  - only through `XEither` and `XPair`, never under a Defer;
  - with the left branch inverted (§3).
- **Tests on unbounded input.** `unsized.test` (441) turns them into the
  unsizeable marker. `test.pick` (420) makes the whole test that marker
  when either alternative is one, which sets the other alternative aside.
- **Give-ups.** `stub.expand` (452) and `step.next` (460) return `XError`
  on shapes they don't expect, and that matters only if it reaches the
  result.
- **The budget.** `step.over` (467) marks an unrolling past `max` (65536)
  with the recursion abort, which becomes `FuelExhausted` if it reaches the
  result.
- **The limits pass.** It is trusted only when `exact` (712) and
  `checks.of` (1094) agree, and that decides `proven`.

**The chains** (Expr.bend):
- `approx.body` (174) is the strict `gate.switch`.
- `chain` (188) and `sized.chain` (197).
- `bottom` (180): an abort closure tagged `AtRecursion{tok}`, or 0 when
  inert.
- `limit.code` (208), `limit` (215) and `unbounded` (219).
- Checks: `check.of` (244) and `resolve.checks` (256).
- `core` (367) turns `X` into `Co.V` and forgets the sites.

**What the IC does with these:**
- After P4 the IC runs only the chosen branch of the strict `if`
  (the port handoff's P4). Everything else it speculates.
- A stuck value is erased when it isn't demanded, and is a readback error
  when it is (DESIGN §7).
- For certified programs, that agrees with a lazy meaning on results.

## 8. Reference: proofs in Bend 2

The source is the flake input: `nix flake archive --json` →
`inputs.bend.path`. For release 2.0.34 it is
`/nix/store/mirj9jkif1lnsqj1n7g3645fwscl42hp-source`.

**The language:**
- `guide/GUIDE.md`, "Laws and Proofs":
  - `law name: for x: A … {lhs == rhs : T}` states a claim, and
    `def name(x…)` proves it.
  - There are no tactics. A proof is a def of the claim's type.
  - `{==}` holds when both sides compute to the same term.
  - Matching refines the goal, and a recursive call is the induction
    hypothesis.
  - `%e : P` rewrites with an equation. `exs y: T` asks for a witness,
    returned as `(y, proof)`.
  - `?name` prints the goal, and `?TODO` leaves it open.
  - `{a != b : T}` is `{a == b : T} -> Empty`. `Equal.sym`, `Equal.trans`
    and `Equal.cong` are in Base.
- A law left open in one file may be filled in another, as
  `def M.name(..)`.
- Termination is mandatory and there is no mutual recursion, so non-
  structural loops count down a `Nat` fuel. `@unsafe` defs fall outside the
  proofs, and `--verdict` refuses them.
- `--verdict` re-checks with the kernel in `bend2/bendtt.lean`, which has a
  Lean proof that no accepted def has type `Empty` and that live code
  halts. The paper is `paper/BendTT.pdf`.

**The kernel, for `--verdict`.**
- `bend --verdict` re-checks with BendTT's kernel, a Lean program bend
  builds on first use. That build needs Lean v4.34.0 on PATH or under
  elan.
- nixos-unstable's Lean 4.34.1 builds it in about a minute:
  ```sh
  nix build github:NixOS/nixpkgs/e7439b6b14ad3cc35d05608ebca9bce01a25f5f8#lean4 --out-link $ROOTS/lean4
  mkdir K && cp $BEND/bend2/bendtt.lean K/ && cd K
  $ROOTS/lean4/bin/lean -c bendtt.c bendtt.lean
  $ROOTS/lean4/bin/leanc -O3 -DNDEBUG bendtt.c -o bendtt
  BENDTT=$PWD/bendtt bend bend/PROOF.bend --verdict
  ```
  `$BEND` is the flake input's path (§14). Lean is used only to build this
  tool; the proofs are Bend.
- `--verdict` refuses a file with open laws. To kernel-check a finished law
  early, copy it and its proof into a scratch file.

**Examples to imitate:**
- `demos/proof_typed_eval/`: an evaluator and an optimizer, with the law
  "the optimizer keeps the meaning of every program". Its `PROOF.bend` is
  the style to copy: induction over the term, a rewrite per subterm.
- `demos/pure_hvm5_mini/PROOF.bend`: larger proofs about an interpreter's
  lexer and printer, with helper laws.

**Prior art, not used:** the local `agda` branch (`README-Agda.md`,
`telomare.agda`). It is a typed toy language whose cost interpretation is
proven adequate for its execution. That's the same shape as law 2, but not
Telomare's core.

## 9. Risks

- **Proof effort.** Bend has no tactics and almost no inference, so big
  proofs are long. The S1 spike calibrates this before S2 commits to it.
- **Kernel coverage.** `--verdict` must accept everything the proof imports
  (Expr.bend, Size.bend, Base's `Map`/`Set`, U32). Check this in the spike.
  If something is refused, keep the checker and `Sem` free of it.
- **Call-by-name cost.** This one happened: the lazy draft never finished
  tc. It was resolved by making `Sem` strict, as the IC is (§2).
- **`Sem` vs the IC.** They can differ in stuck messages, or in which abort
  is reported when several are in a result. The parity test and the
  observation's design must decide which differences count as
  observations.
- **v1 coverage.** v1 may accept few real programs within its budgets. Then
  D3 decides between living with residual aborts and doing S5.
- **Compile time.** The checker adds to sizing's cost, and each `.telc`
  pays it once.

## 10. Setting up a machine

```sh
git clone git@github.com:hhefesto/stand-in-language.git telomare
cd telomare
git checkout sizing-proof        # once it has been pushed
git remote add telomare git@github.com:Stand-In-Language/stand-in-language.git
git fetch telomare               # telomare/master = 2ae49e0a (Sam's DESIGN.md)
git tag haskell-final 1270d8b3   # the tag is local-only; its commit is in bend-port
git config core.hooksPath hooks  # pre-commit: bend bend/Everything.bend --check-only
nix develop                      # bend 2.0.34 on PATH (flake input, rev 01875127)
nix flake check                  # telomare, bend-check, bend-tests, goldens: minutes
```

**Building the port:** `bend bend/Main.bend -o /tmp/bin/telomare`. On the
i7-1160G7 laptop (15 GB) it takes about 2 minutes and peaks at 2.2 GB.

**Building the oracle**, i.e. haskell-final's `telomare`:
```sh
git worktree add ../telomare-haskell-final haskell-final
cd ../telomare-haskell-final
nix build --accept-flake-config .#telomare --out-link result
# binary: ../telomare-haskell-final/result/bin/telomare
```
The cachix substituters are not picked up, because the user is not a
trusted user. So the Haskell dependencies build from source, in about 15
minutes.

**Reading the oracle's source**, the reference for every sizing question
here (S0.1, S0.3):
- `git show haskell-final:src/Telomare/Machine.hs`: the step algebra,
  superpositions, `filterLeft`/`filterRight` and `decendant`;
- `git show haskell-final:src/Telomare/Size.hs`: the sizing runs.

**Profiling:** `perf` comes from `nix build nixpkgs#perf --out-link …`.
User-space profiling works (`perf_event_paranoid` = 2).

**What does not travel**, so copy it by hand if wanted:
- Claude's memory directory and `~/.claude/plans/`;
- `notes.md` at the repo root (the private timesheet notes, gitignored on
  purpose: never commit it);
- `interview/`, which is excluded in `.git/info/exclude`;
- `.envrc`.

## 11. Verifying

- `nix flake check` runs:
  - `telomare`;
  - `bend-check`: `bend bend/Everything.bend`, which imports every module
    and prints `ALL PROOFS CHECK`;
  - `bend-tests`: each `bend/tests/X.bend` built with `bend -o` and run.
    The expected `ok NAME` lines per file are listed in `nix/bend.nix`
    `tests`; a test file missing there fails the check.
  - `goldens`: `test/golden/run.sh` over `goldenPatterns` in
    `nix/bend.nix`.
- The pre-commit hook runs `nix run .#bend -- bend/Everything.bend
  --check-only`.
- By hand: `bend bend/Main.bend -o /tmp/bin/telomare` (~65 s), then
  `test/golden/run.sh /tmp/bin check 'GLOB'`. Modes: `record` (writes
  `expected/`, only with the oracle), `record-port` (writes `port/`) and
  `check`.
- The goldens hold haskell-final's exit status, stdout, stderr and written
  files for 41 cases (`test/golden/cases`). Where the port changes a format
  on purpose: list it here (§1) and re-record only that case, into
  `port/`.
- A full golden pass on haskell-final took ~11.5 min; the port's patterns
  take a few minutes.
- Corpus parity: see §12.
- `bend/dev/gate.sh [build|tests|goldens|corpus|all]` runs the build, the
  bend tests (expected lines from `nix/bend.nix`), the goldens and the
  corpus, as P1–P7 did. Binaries and logs go to `$GATE` (default
  `/tmp/telomare-gate`); it prints `GATE OK` or `GATE FAILED`. Run it
  inside `nix develop`.

## 12. Dev tools and the parity corpus (`bend/dev/`)

**This branch's tools** (built from the repo root like the others):
- `check MODULE [RUNS]`: the erasure checker (`Check.bend`) on MODULE's
  main, guarded as the command guards it. It prints the erasable checks,
  the verdict, and the runs taken (4096 by default). The corpus runs from
  `bend/dev/corpus`.
- `fastdiff.sh BIN [SESSIONS [SEED]]`: S0.2's sized vs `--fast` sessions.
- `gate.sh`: the gate (§11), with its `proofs` step (§1).

Build a tool with `bend bend/dev/X.bend -o /tmp/X` (inside `nix develop`),
and run it from the repo root: modules load as `M.tel` from the cwd.

**Compile (all built on 2026-10-06, at `7c49323`):**
- `icmeter MODULE [LINE…]`: the session's displays, then
  `IC interactions: N`.
- `ealtime MODULE`: for the `term` (certified) and `sized` passes, `bodies N`, then
  `main X ms: vars V sites S pairs P blames B -> ok|<error>` and
  `verdicts Y ms: K certify`.
- `tplcount MODULE`: how many templates the prepared program has.
- `layouts MODULE`: the certification's verdict, then every capture layout
  EAL gives the sized term, one `hash shape` line each. It is a fingerprint
  for comparing builds.
- `bodyerrs MODULE`: every lifted body's standalone verdict on the
  certified term and on the sized one, with the failure text.
- `sites MODULE`: the recursion sites (location and token), and the
  term's node count.
- `size MODULE`: sizing's counts, or its failure.
- `lift MODULE`: the deferLift dump of the term.
- `lexdump`: tokens.
- `ealonly`: certification only.
- `sha`, `shabench`: SHA-256.

- `phases MODULE [LINE…]`: per-phase times (front, certify, size, layouts,
  prepare, session), for main alone (no guard). Fixed in the dev fixup
  after `74c4cc5`.
- `guarded MODULE`: EAL's verdict and the number of capture layouts for
  main sized with its session guard, main alone, and the guard (P7.5).

**Profiling** (how P1 was measured):
1. `bend bend/dev/ealtime.bend -o X.c` emits the C.
2. Compile it with frame pointers. Use the clang from bend's wrapper
   (`head $(which bend)` shows the store path):
   `clang -std=c11 -O3 -g -fno-omit-frame-pointer X.c -lpthread -lm -o X`.
3. `perf record -F 999 -g --call-graph fp -o D X tictactoe`.
4. Report flat: `perf report -i D --no-children -g none --no-inline
   --sort symbol --stdio`. Reports with call graphs are slow, so use
   `-S term_drop -G` to see one symbol's callers.

`perf annotate -s term_drop --no-source` shows where it spends: a
`lock xadd` (a refcount decrement on a shared value) was 31% of it.

**Timing on this laptop:**
- Thermal throttling makes back-to-back runs drift by 30%.
- Interleave the variants and `sleep 15`–`20` before each run.
- Take medians of 5.

**Stale** (they fail to check since the alignment round changed types;
fix them when needed):

| Tool | First error |
|---|---|
| `eal`, `ealphase` | unknown constructor `../Front.Terms` (gone since P3); before that, `eal`'s `main.only` called `EAL.main.of`, which no longer exists |
| `ic1`, `meter` | `../IC.Run` has 4 fields since P5 (`unrolls`) |
| `expr` | "write `../Syntax.Surf<..>`" |
| `parsedump` | `../Syntax.SLamPat`'s fields |
| `paths` | unknown constructor `../Term.TIdx` |

**`bend/dev/upstream/`:** draft issues for bendlang/bend (`NOTES.md`), not
filed:
1. A U32 literal match copies its default once per bit: the
   `nested-u32-match.bend` repro; `0001-merge-u32-literal-match-defaults.patch`
   against the flake input's `bend2/comp.ts`. With the patch, compiling
   `bend/Main.bend` peaks at 2.9 GB instead of 4.9 GB.
2. `Bool.pick` boxes both alternatives.

The patch is not applied to the flake.

**`bend/dev/bench.sh BENDBIN [NAMES…]`:**
- Times the port and, when `ORACLE=…/telomare` is set, haskell-final's
  `--ic`, and compares their outputs. `NOHS=1` times the port only.
- It runs the three golden programs and the corpus. The default set is the
  README table's programs.
- On this 16 GB laptop, cap the oracle's heap: `GHCRTS=-M8G` (ctprop peaks
  at 7.7 GB; the rest stay under 1.2 GB). Run nothing else heavy beside it.

**`bend/dev/corpus/`:** 15 programs beyond the goldens, with
haskell-final's outputs. Run them from that directory: `Prelude.tel` is a
symlink to the repo's, and `qual.tel` imports `Other.tel`. Every input is
empty.
- Programs:
  - `casea`, `casei`, `cases`: case expressions;
  - `ctall`, `ctign`, `ctprop`, `ctstr`: case tests;
  - `nonex`: a non-exhaustive case, which aborts;
  - `patlam`: pattern lambdas;
  - `qual`: a qualified import;
  - `natudt`: a user-defined natural type;
  - `natarith`, `arith`: arithmetic;
  - `rat`, `ratarith`: Rational.
- `NAME.hs-ic-meter`: haskell-final `--ic --meter` output (displays, then
  `IC interactions: N`). There are 13; `arith` and `casei` have none.
  `ratarith`'s is the fuel death at 10,000,000. The port matched all 13
  until P4; from P4 its displays still do (`ratarith`'s match
  `ratarith.hs-run`, the reference evaluator's), and `NAME.port-ic-meter`
  holds the port's whole output.
- `NAME.hs-certificate`: haskell-final `--certificate` output. There are
  14; `ratarith` has none. The port matched all 14 byte for byte until
  P7.2. Since then they still match with the checks section removed, and
  `NAME.port-certificate` holds the port's whole output.
- To compare:
  ```sh
  cd bend/dev/corpus
  /tmp/bin/telomare casea.tel --meter 2>&1 | diff - casea.port-ic-meter
  diff <(/tmp/bin/telomare casea.tel --meter 2>&1 | grep -v '^IC inter') \
       <(grep -v '^IC inter' casea.hs-ic-meter)
  { /tmp/bin/telomare casea.tel --certificate; echo "status $?"; } \
    | diff - casea.hs-certificate
  ```
  The port's `--meter` puts `IC interactions: N` on stderr after the
  displays, which matches haskell-final's first meter line.

## 13. Layout

- `bend/Everything.bend` imports every module.
- Front end: `Lex`, `Parse` (→ `Syntax`), `Expand`, `Resolve`, `Desugar`,
  `Lower` (→ `Term`), `Split`, and `Front` (loading, both lowerings).
- `Expr` (sizing's IR) and `Size`, which hands on `Core`: the runnable core
  `V`, data `D`, the reserved function indices.
- `Sha256`, `Lift` (deferLift, CapShape), `EAL`.
- `IC`, `Session`, `Main`.
- `Levels` and `Certificate`: the static report.
- `Text`, `Show`, `Loc`.
- This branch's: `Sem` (the meaning) and `Check` (the erasure checker),
  both in `Everything.bend`; `LAWS` and `PROOF` (the claims and their
  proofs), in it through PROOF.bend's import of LAWS.bend.

**IC:**
- The net is an `Array<U32>`, 8 words per agent. Active pairs are LIFO.
- `Ctl` is kept to 8 hot words; cold fields are boxed in a list of one.
  Widening it costs ~20%.
- The template store is one `Array<U32>`.
- Guided dup-closure copies a region by the plan EAL's layout gives.

**EAL:**
- The program is `P`: bodies by rank, as a complete binary tree.
- State lives in U32 arrays, with job machines for the walks and templates
  for repeated dispatch.
- The solver works over rows of words.

## 14. Bend 2 gotchas

- **Never branch on a U32's literal values in hot code.**
  `match x: case 1: … case _:` compiles to a test per bit, each with a copy
  of the default (`bend/dev/upstream`). That costs ~30 compares at run
  time, and nested literal matches blow up the compile (26 GB once).
  Decode to a small enum or a Bool once and match that.
- **`Bool.pick` evaluates both alternatives** (strict) and boxes them.
  Match the Bool in a helper instead.
- **Binder order:** you may only match binders introduced after the last
  one matched, and a destructuring let counts as a match. Put what is
  decided first in the parameter list.
- **A match on a computed value fails** with "a match on a parameter or
  field… give the value its own def". Pass it to a helper def.
- **No mutual recursion,** and a def can't call one written below it.
  Merge mutually recursive functions into one def with a selector
  argument.
- **No `(a, b) = f(x)` of a call result,** and no recursion through a
  template argument. A loop that needs a step's result takes it as its last
  parameter.
- **Flattened records:** non-recursive records are flattened into words at
  every call. Keep wide, cold state behind a list of one.
- **Parallel lets:** a parallel let deals the lanes out once, with no
  stealing. Run stages that fork internally one after the other.
- **Shared nodes:** matching a shared (`+`) node copies its fields and bumps
  counts; words in U32 arrays don't. Freeing an array of boxed values visits
  every slot (P1b).
- **State monads** cost a closure per bind, ~40% in hot loops. Use direct
  style on arrays.
- **Strict evaluation:** a message argument is built even when it is unused.
- **Types:**
  - Pairs (`A & B`) are Type, not Data.
  - `do M<…>:` needs its type spelled out.
  - Type parameters are explicit at calls (`S.loc(Empty, Unit, Empty, t)`),
    and a family instance is written `Syntax.Surf<..>`.
  - `Empty.absurd(T, w)` eliminates a witness.
  - Bare Nat arithmetic needs an annotation: `(a + b : Nat)`.
  - A record literal may need a type: `{Def{m, "main"} : Def}`.
- **`+case` is a keyword** (use `+cased`). `LT` clashes with Base.
  Constructor names must be unique across the modules imported together.
- **Termination is checked left to right** over the arguments. Non-structural
  loops take `fuel: Nat`.
- **Running:**
  - Interpreted `bend F.bend` is 20–50× slower than `-o`.
  - `IO.args()` keeps argv[0].
  - `--check-only` reports only the first error.
- **Reference:** the flake input's source, `guide/GUIDE.md` and
  `bend2/base.bend`. Find it with `nix flake archive --json` →
  `inputs.bend.path`; it was `/nix/store/mirj9jkif1lnsqj1n7g3645fwscl42hp-source`
  for rev `018751270e80`, release 2.0.34. Nothing from
  `~/src/formalTransformer` or `~/src/bend2`.

**Proofs** (learned in S1 and S2):
- `%e : P; body`, with `e : {a == b : T}`: P is the current goal with `_`
  where b stands, and body proves P with a there. So it rewrites b into
  a. Use `Equal.sym` for the other way.
- A default case (`case _:`) in a proof does not refine the goal:
  enumerate the constructors. Defaults in the definitions a proof
  unfolds are fine once the scrutinee is a constructor.
- Matching a binder consumes the pattern-bound binders introduced after
  it. So match a def's parameters in their order, before the fields of
  anything matched later. Where a case needs a field and an earlier
  parameter both matched, move it to a helper that takes the induction
  hypothesis as an argument.
- A Pi type is `@x: A -> B`, and the domain stops at the first bare
  `->`. A recursive call inside a lambda passed as an argument is
  accepted when its first argument shrinks, by bend and by the kernel.
- A lambda-bound hypothesis cannot be matched. Close an Empty one with
  `Empty.absurd(T, h)`: T is not inferred, so write it out.
- A rewrite cannot precede a match. Match first, or hand the rest to a
  helper whose parameter stands for the computed value, and match there.
- A law's own `for` binders are not shared (`+`). Where a proof uses one
  twice, delegate to a helper law that shares them (`what_runs_at`).
- `-x` marks a parameter used only in types: one passed to another lemma
  must not have it. `+x` marks one used twice, equations included, and a
  `+` parameter can still be matched.
- Hypotheses whose types depend on matched variables come after the
  matches, as arrows (`h => …`).

## 15. Nix gotchas

- corepkgs' `lib.mkFlake`. `bend` brings its own nixpkgs. Upstream Bend
  ships no flake.lock; ours pins its nixpkgs.
- corepkgs uses structured attrs: environment variables go in `env.*`.
- `.gitignore` keeps its Haskell entries on purpose: old checkouts still
  hold `dist-newstyle/`.
- `nix/bend.nix` takes every `*.bend` under `bend/` (`bendSrc`) and every
  `*.tel` in the repo (`telFiles`). While `bend/dev/` is committed, editing
  a dev tool rebuilds the `telomare` derivation, and the corpus's `.tel`
  files ride along in the test and golden sources. That is harmless, and it
  ends once the dev commit is dropped.
