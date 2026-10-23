# Sizing's erasures, proven sound

Sizing lets the compiler erase two kinds of abort from main: the bottoms of
the recursion chains, and the refinement checks it discharges. This file
says what is proven about those erasures, how, and what is still trusted.
The claims are `bend/LAWS.bend`, their proofs `bend/PROOF.bend`, the
meaning they are stated over `bend/Sem.bend`, and the checker they certify
`bend/Check.bend`.

The work was done on branch `sizing-proof` (2026-10-08 to 10-21) and merged
into `bend` on 2026-10-22. That branch still holds its full handoff,
`HANDOFF-sizing-proof.md`, with the day-by-day history.

Contents:
1. Status
2. The goal, stated exactly
3. The evidence before the proof
4. The approach, and the proofs as built
5. Decisions
6. Reference: sizing, read as a prover must
7. Reference: proofs in Bend 2

## 1. Status

**All six laws are proven** (§2), and `bend bend/PROOF.bend` prints ALL
PROOFS CHECK. PROOF.bend is about 7,700 lines and is part of
`Everything.bend`, so `bend-check` and the pre-commit hook check it.
The proofs of laws 1 to 4 and of laws 5 were also rechecked with
`--verdict` (BendTT's Lean-proven kernel, §7) when they were written.

**The checker is wired into sizing.** Sizing calls `Ck.check` on main's
witness and on its guard's (`Sz.erasure.of`, `Sz.erased`). Bottoms and
discharged checks are erased only when sizing proves the program *and* the
checker proves it too; otherwise every one stays an abort. The guard is
sized first, since the checker runs main only on inputs the guard passes.
`count.of` lives in `Expr.bend` so that Size and Check need not import
each other.

**`--certificate` says which erasures are proven** (asked by the user):
`erasures in main:` and `erasures in the guard:`, each proven (with the
evaluation steps it took) or kept (and why).

**The budget is work, not runs.** `Sem.semc` is `sem` with a count of
evaluation steps beside each result, and `semc_sem` proves it gives `sem`'s
result. `Ck.explore` spends each node's steps (guard plus main) and one
more per leaf; `node_counted` and `at_good` carry `tree` over to it. The
laws did not change: LAWS.bend's `leaves` argument is the work budget.
The budget is 2^28 steps (`Sz.check.work`):
- tc_ultra_minimal: proven in 4,197 steps;
- simpleplus: proven in 200,013,887 steps (about 4 s);
- tictactoe: gives up, so it keeps its aborts (D3, §5). `--certificate`
  takes 8.5 s (at a budget of 16,384 runs it took 110 s);
- the 15 corpus programs: proven at once, since they ignore their input.

Two designs for the count failed first, both on Bend's rules (no mutual
recursion, a match only on a parameter): helpers that call `semc` back
(rejected), and closures for the continuations (1.7 times slower). `semc`
instead hands itself the first result as a job (`Kc`'s `SetK`, `IfK`), and
counts the two halves of a pair separately.

**Open:**
- A `bend-proof` check in `nix flake check`, so that
  `bend bend/PROOF.bend --verdict` must print ALL PROOFS CHECK. It needs
  the kernel built in Nix (§7). Until then `bend/dev/gate.sh proofs` runs
  it by hand when `BENDTT` is set.
- Checker v2 (§4), only if programs like tictactoe must lose their aborts.

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
  reduction of EAL-typable nets, §6) is a separate, larger project.
- Termination is EAL's promise (C2, through DESIGN §5).
- The front end (parse to Term3), and the session loop.
- Bend's checker. `--verdict` re-checks with BendTT's kernel, which has a
  proof in Lean.

## 3. The evidence before the proof

**Before the proof, the evidence was testing:**
- The goldens and the 15-program corpus pass, with displays and counts as
  haskell-final's apart from the differences by design (HANDOFF.md
  section 7).
- Sizing is a transcription of haskell-final's, which was never proved
  either.

**The re-run P7.6 removed.** Until P7.6 (`e64b80a`), a second symbolic run
confirmed the bottoms dead before erasing them (`bottomed`, `as.ran` and
`opening.bottomed`: `git show e64b80a^:bend/Size.bend | sed -n 1195,1257p`).
It confirmed tc, simpleplus and every corpus program, and reached two of
tictactoe's bottoms: #0, Prelude:30:18 (the `d2c` in `minus`, `<= 79`), and
#13, tictactoe:96:45 (`d2c nextPlayer`, `<= 2`). It used sizing's own
evaluator, so it was a consistency check, not an independent one. P7.6
trusted sizing instead; the checker now stands where the re-run stood.

**An over-run**, if one happened: an erased bottom is 0, applying 0 gives
a stuck value, and if that value is demanded the session prints
`IC runtime: ICStuck "applied value is ICZero, not a function: 0"`. Still
an error, but one that doesn't name the recursion.

**Found while planning the proof, and fixed (`822f0c5`): the left-branch
superposition filter was inverted.** haskell-final's `filterLeft n` keeps
the left alternative of a superposition at or below the choice position
`n`, and leaves every other superposition alone
(`src/Telomare/Machine.hs:211-214` at `haskell-final`; `decendant x d` is
"x is d or below it", 673). The port's `filter.at` did the opposite. In a
left branch it kept only the left side of superpositions at unrelated
positions, which drops a path some input takes (so a count could come out
too small, or a check be discharged wrongly), and kept both sides of the
superpositions that branch decides. The fix is a `filter.left` that
mirrors `filter.right`; the `size-filter` test pins the seven cases. No
golden or corpus output changed.

**A differential test**, `bend/dev/fastdiff.sh BIN [SESSIONS [SEED]]`,
compares the sized program with `--fast` on generated sessions. On 100
each of tictactoe and simpleplus (seed 7) it found no difference. It
reaches only the states a session reaches; the laws cover every state the
guard admits.

**tictactoe, by checker v1:** 50,000 runs found no input that fires a
site, and a 5,000,000-run check hit its 10-hour limit without a verdict.
So no counterexample is known (D4 did not arise), but checker v1 cannot
prove tictactoe within any budget a compile could afford. That was D3.

## 4. The approach

**Translation validation, not a verified sizer.** Prove a *checker* that
looks at the program sizing produced, not sizing itself. CompCert validates
its register allocator this way, and CeTA checks termination proofs this
way. The reasons:
- Sizing must keep matching haskell-final's counts and certificates byte
  for byte, so it can't be reshaped for proof.
- Sizing leans on Strings, Maps and U32 tokens, and has approximations
  (§6) whose soundness argument has never been written down.
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
  pass's `extract`/`exact` (§6).
- It accepts when no leaf's run lets a mark reach the result. A leaf where
  one does names a concrete input. A budget that runs out (evaluation
  steps, §1, or depth) gives "unknown".
- Proof: the lemma, plus "the leaves cover every input" (induction on the
  split tree).
- Cost: exponential in the input positions inspected.
  - Characters are unary numbers, so the guard's digit test splits once
    per level, and strict evaluation looks at every character before the
    guard decides.
  - simpleplus takes 14,163 runs (200,013,887 steps).
  - tictactoe (board, player and line) is in the millions of runs.

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

### The proofs as built

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
- With these, the erasure is correct on every input where the watched
  witness answers. Laws 5 make that static: the checker proves the
  watched witness answers without a mark on every admitted input.

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
  fields would consume them (HANDOFF.md, "Bend 2 gotchas", Proofs).
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

**Laws 5, as built** (PROOF.bend, "Laws 5: the certificate"):
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

## 5. Decisions

**D1 (decided 2026-10-09): the laws' wording,** `bend/LAWS.bend`.
Approved as drafted, except `what_runs`, which was false as written and
now takes data inputs only. As first written it took any `E.X` as input:
an input that is itself an `XCheck` numbered like one of main's erased
checks, with a failing test, and main the identity, make the witness
answer 0 while the program that runs aborts, at any fuel. The user chose
to take only data inputs (`Co.D`, run on `Sm.of.data(input)`), which is
what the session gives main and what the certificate laws quantify over.
- The meaning is the IC's evaluation order (§2), not a lazy one.
- The inputs are 0 plus whatever the guard admits, not only the states a
  session reaches. Sizing claims every input, and DESIGN §6 keeps the
  session out of totality ("each turn is a total function call").
- The observation is the full readback, with abort sites and messages. A
  closure shows only as its function index.
- Erasure and the counts are stated where both runs answer, leaving
  termination to EAL.
- These pin down what a Telomare program means, so Sam should see them.

**D2 (decided 2026-10-08): the filter fix** (§3) landed on `bend`
(then `bend-port`), the Bend version that keeps up with master's
behaviour.

**D3 (decided): residual aborts stay.** Programs the checker cannot
verify keep their bottoms and checks, as a residual runtime abort (DESIGN
§10's part 2). tictactoe is one: erasing its aborts would save 1.5% of
the game `1 4 2 5 3` (6,016,132 interactions kept, 5,927,480 erased) and
needs checker v2 (§4). Recommended to the user on 2026-10-21, and
accepted with the plan on 2026-10-22.

**D4: did not arise.** It was: if the tictactoe check fired, revert P7.6
and go back to P7.5's confirming re-run until the checker was wired in.
No input that fires a site is known, and the checker is wired in.

## 6. Reference: sizing, read as a prover must

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
  - with the left branch mirroring the right since `822f0c5` (it was
    inverted, §3).
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

## 7. Reference: proofs in Bend 2

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
  `$BEND` is the flake input's path (above). Lean is used only to build this
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

