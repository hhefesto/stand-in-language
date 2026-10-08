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

Once S1 starts, add `bend bend/PROOF.bend` (§5).

## 2. The goal, stated exactly

**The objects. All of them exist in the code today:**
- `x`: main as sizing receives it. This is `Sz.size.at`'s `x`
  (Size.bend:1268), an `E.X` with an `XStub` per recursion site and an
  `XCheck` per refinement check. `cm = Sz.capped(x, True{})`.
- `counts`: sizing's counts.
- **marked**: `Sz.program(counts, None{}, False{}, cm, True{})`
  (Size.bend:1188). Every check is kept, and every chain's bottom is an
  abort. Each such abort carries its site in `E.Site`: `AtCheck{n}`, or
  `AtRecursion{tok}` (Expr.bend `check.of` 244, `bottom` 180).
- **erased**: `Sz.program(counts, Some{left}, True{}, cm, True{})`. This is
  what bend-port runs when sizing says `proven` (`Sz.discharged`, 1210).
  The checks not in `left` and every bottom are erased.
- **unbounded**: marked with each chain replaced by the self-rebuilding
  step, i.e. `E.unbounded` (Expr.bend:219) where `program` calls
  `set.sizes`. This is `--fast`'s meaning, with the checks kept.
- **admitted inputs**: 0, the session's opening call, and every datum the
  session's guard passes. P7.5(b) runs main's boundary refinements as a
  guard before every later call.

**The meaning, `Sem`.** A lazy (call-by-name) big-step evaluator over the
core fragment of `E.X`:
- It follows DESIGN §2's table.
- Aborts and stuck values are values (DESIGN §5 "Applying data is
  tolerated", §6 "aborts are discardable values").
- It is indexed by fuel, because Bend demands termination.
- It records which erasable aborts fire (§4 explains why: firings, not
  where an aborted value ends up).
- The observation is the result read back in full: a data tree whose leaves
  may be an abort (site and message) or a stuck value.

**The theorem, as three laws:**
1. **Erasure.** If the marked program fires no erased site on input `d` at
   fuel `f`, the erased program gives the same observation on `d` at `f`.
2. **Chains suffice.** If the marked program fires no bottom on `d`, the
   unbounded program gives the same observation on `d`, at some fuel.
3. **Certificate.** If the checker accepts the program, then for every
   admitted `d` and every fuel, the marked program fires no erased site.

Together these say: for every program, whatever the compiler erases is
erased soundly, and the compiled program computes what the unbounded
program computes.

"Every program" means every program the compiler builds. A program the
checker can't verify keeps its bottoms and checks: that is P7.5's
behaviour, and DESIGN §10's part 2. The theorem then holds for it
trivially.

**Not covered: the trusted base.**
- `Sem` is the meaning. It is checked against the IC by tests (S1), not by
  proof. Proving the IC sound (optimal reduction of EAL-typable nets, §7)
  is a separate, larger project.
- Termination is EAL's promise (C2 through §5), not this branch's. The laws
  are indexed by fuel, so they need no termination.
- The front end (parse to Term3) and the session loop.
- Bend's own checker. `bend … --verdict` re-checks with BendTT's kernel,
  which has a proof in Lean.

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

**One lemma does most of the work: demand.** In a lazy semantics, a subterm
the run never needed was never evaluated. So if no erasable site fires
during a run, replacing what those sites hold changes nothing, at the same
fuel.

`Sem` records firings rather than checking where aborted values end up, for
two reasons:
- An abort's message is truncated to data (`trunc`, Size.bend:479, after
  haskell-final's `truncF`). That can swallow an aborted value that was
  demanded, so "no marker in the result" is weaker than "no marker fired".
- A kept check also does work its erased version skips: it evaluates its
  test. So law 1 needs fuel monotonicity besides demand.

The lemma is used three times:
1. **Erasure** (law 1). The sites are the erased bottoms and checks. Each
   is replaced by 0, or by the check's value.
2. **Chains suffice** (law 2). Each bottom is replaced by the rest of the
   unbounded recursion. This also needs an unrolling lemma: n chain links
   over `limit` behave as `limit` does. The encodings differ: a chain link
   carries the next link as data (Expr.bend `chain` 188), while
   `limit.code` (208) rebuilds itself.
3. **The checker** (law 3). Input positions are sites too. Suppose a run on
   a partial input (data with holes) never inspects a hole and fires no
   erased site. Then the run is the same on every input that fills the
   holes.

**Checker v1: forking symbolic execution on `Sem` itself.**
- Run the marked program with `Sem` on a partial input.
- A projection of a hole is a hole. The left of input position `p` is
  position `pL`, as with sizing's `XVar`, and this holds because
  `Left 0 = 0`.
- When a gate, an abort or an application inspects a hole, stop. Then run
  twice: once with the hole as 0, and once with it as a pair of two new
  holes.
- Run the guard on the same partial input first, and prune the branches it
  rejects. That handles the boundary exactly, with none of the limits
  pass's `extract`/`exact` (§7).
- Accept when no leaf fires an erased site. Reject when any budget (fuel,
  number of leaves) runs out.
- Proof: the demand lemma, plus "the leaves cover every input" (induction
  on the split tree). This is small.
- Cost: exponential in the input positions inspected. That's fine for tc,
  simpleplus and most of the corpus. tictactoe will likely blow the budget,
  because the board, the player and a line of input are all inspected. It
  then keeps its bottoms, which cost it 11,078 of 5.9 million interactions
  on the test game (0.2%).

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

**S0.1. Fix the filter inversion.**
- In Size.bend:376, drop the `Bool.not`, so that the left alternative is
  kept where the superposition is at or below `n`.
- Pin the seven cases of §3 as a `size-filter` group in
  `bend/tests/size.bend`, and list it in `nix/bend.nix` `tests.size`.
- Gate it. Expect no output to change. If a golden or corpus count does
  change, that's a sizing change: compare with haskell-final and record it.
- Where the fix lands is D2.

**S0.2. Differential test, sized vs unbounded.**
- Run tictactoe and the corpus with and without `--fast` on many generated
  input sequences: digits 1–9, other digits, letters, `q`, and empty and
  long lines. Diff the displays.
- A difference means an over-run (the erased bottom's stuck error) or a
  wrongly discharged check.
- Put the script in `bend/dev/`.
- This reaches only the states a session reaches. The laws cover every
  state the guard admits.

**S0.3. Explain tictactoe's #0 and #13.**
- Rebuild the old re-run as `bend/dev/rerun.bend`, from `e64b80a^`'s
  `bottomed` and `as.ran`.
- Have it print the superposition path (the `XEither` names) on which each
  bottom fires.
- Then decide which it is:
  - a real input: a sizing bug, so fix sizing and see D4;
  - a combination no input produces: then checker v1 rejects tictactoe,
    and v2 must not.

### S1. The specification (medium; ends at D1)

**`bend/Sem.bend`.**
- The lazy evaluator over the core fragment of `E.X`: Zero, Pair, Env,
  SetEnv, Defer, Gate, Left, Right, `Abort{site}` and `Aborted{site, m}`.
  Every other form is stuck.
- Fuel-indexed and call-by-name: a thunk is a term and its environment.
- It records the sites that fire, and reads the result back as an
  observation tree.
- Keep it short and plainly DESIGN §2's table: it is the one definition
  everything else is trusted against.
- It is not a second runtime (C4). Nothing runs user programs on it. It is
  the meaning, and later the checker's engine.

**`bend/LAWS.bend` and `bend/PROOF.bend`.**
- `LAWS.bend` holds the three laws of §2 in Bend, as open claims. The human
  owns them, so don't edit them once they are approved.
- `PROOF.bend` fills them, with `?TODO` until each is done.
- Bend's convention (GUIDE, "Laws and Proofs"): `bend PROOF.bend` prints
  SOME PROOFS FAIL while a law is open, and ALL PROOFS CHECK once all hold.
  `--verdict` re-checks with the kernel.
- `Sem.bend` joins `Everything.bend` like any module. Keep `LAWS.bend` and
  `PROOF.bend` out of it while laws are open: its check and the pre-commit
  hook expect ALL PROOFS CHECK.

**`bend/tests/sem.bend`.**
- `Sem` against the IC on the sized terms of the goldens and the corpus:
  the same displays and the same aborts.
- This is the evidence that `Sem` means what the IC does.
- Call-by-name may be too slow for tictactoe. Measure it, and fall back to
  the small programs if so.

**Spike first, before writing the laws for real:**
- Prove one small law about `Sem`: more fuel never changes a finished
  result.
- Run `bend --verdict` on a file that imports Expr.bend and Size.bend.

This measures how proofs feel in Bend. It also finds kernel limits (U32,
String, `Map`/`Set`) before they matter.

### S2. Semantic lemmas, proven (medium)

- Fuel monotonicity. Determinism is free, since `Sem` is a function.
- The demand lemma, for sites and for input holes.
- Law 1, erasure.
- The unrolling lemma, and law 2, chains suffice.

After S2, P7.6's erasure is proven correct on every input on which the
marked program fires no bottom. What remains is knowing that statically.

### S3. Checker v1, executable (medium)

**`bend/Check.bend`.**
- `Sem` over partial inputs, with guard pruning and budgets (§4).
- Wire it into `Sz.discharged` (Size.bend:1210): erase only when sizing
  says `proven` and the checker accepts. Otherwise keep every bottom and
  every check, as P7.5 did for tictactoe.

**Gate.**
- Outputs are unchanged for the programs it accepts.
- Re-pin where it rejects. If tictactoe is rejected:
  - `ic-meter-tictactoe` and `port/tictactoe.ic-meter` go back to
    5,938,558;
  - `size-erased`'s tictactoe line goes back to "Abort";
  - the `.compile` digest changes.

**Also:**
- Measure compile time. Sizing is meant to be paid once (DESIGN §4), and
  the checker joins it.
- Whether `--certificate` should say which erasures are proven is an output
  change. Ask the user.

### S4. Checker v1, proven (small to medium, given S2)

- Prove law 3 for v1.
- Add a `bend-proof` check to `nix flake check`:
  `bend bend/PROOF.bend --verdict` must print ALL PROOFS CHECK.
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

**D1 (end of S1): the laws' wording.**
- The meaning is lazy call-by-name.
- The inputs are 0 plus whatever the guard admits, not only the states a
  session reaches. Sizing claims every input, and DESIGN §6 keeps the
  session out of totality ("each turn is a total function call").
- The observation is the full readback, with abort sites and messages.
- These pin down what a Telomare program means, so Sam should see them.
  Approve LAWS.bend before S2.

**D2 (now): where S0.1's fix lands.**
- Recommended: on bend-port, before the pending push of
  `8103636..e3480b1`. bend-port is the branch headed for master, and P7.6
  trusts sizing.
- Then rebase sizing-proof onto it.

**D3 (after S3): residual aborts.** Is it acceptable that programs the
checker can't verify keep their bottoms, as a residual runtime abort
(DESIGN §10's part 2)? If tictactoe must lose its aborts, S5 is needed.

**D4 (S0, only if a real input over-runs): revert P7.6.** Revert it on
bend-port and go back to P7.5's confirming re-run until the checker lands.

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
- **Call-by-name cost.** It affects both `Sem`'s parity test and checker
  v1's leaves. If it is too slow, give `Sem` a call-by-need twin and prove
  the two equal, or keep v1 to small programs.
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
- Planned on this branch (§5): `Sem` (the meaning), `Check` (the checker),
  and `LAWS`/`PROOF` (the claims and their proofs).

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
