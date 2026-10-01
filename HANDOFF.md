# HANDOFF — bend-port: the plan after DESIGN alignment

Written 2026-10-01, just before a move to a new computer. It replaces the
2026-09-30 handoff, which mapped DESIGN.md onto the port. That work is done;
its map is kept in full under "Done: DESIGN alignment" below.

**This file is committed only so it travels.** Master keeps HANDOFF.md out
of the tree (`27bec343`), and so does `bend/dev/` (the dev tools and the
parity corpus, committed for the move too). Drop both commits ("Hand off
bend-port …" and "Carry the dev tools …") before any PR, and go back to
an untracked HANDOFF.md and an excluded `bend/dev/`
(`echo bend/dev/ >> .git/info/exclude`).

Line numbers below are as of `0c062de5` (the README design commit). They
drift as code changes; search for the definition named.

Contents:
1. Working rules
2. Setting up the new computer
3. Where the branch stands
4. The plan: P1–P7, with the user's decisions
5. Reference: what the research found
6. Done: DESIGN alignment (2026-09-30)
7. Differences by design
8. Left open
9. Verifying
10. Dev tools and the parity corpus
11. Layout
12. Bend 2 gotchas
13. Nix gotchas

---

## 1. Working rules

These are the user's standing instructions. Claude's memory directory
(`~/.claude/projects/-home-hhefesto-src-telomare/memory/`) does not travel
with the repo, so they are repeated here.

- **Never** add a Claude co-author or attribution line to commits or PR
  bodies.
- "Success" means local success. Ask before every `git push`; one approval
  covers one push. Open a PR only when asked.
- Keep this HANDOFF.md current as work progresses.
- Bend comes only from upstream (`github:bendlang/bend`, the flake's `bend`
  input), and the only oracle is `haskell-final`. Use nothing from
  `~/src/formalTransformer` or `~/src/bend2`.
- Code must be elegant and fit the existing design naturally. Backtracking
  is fine.
- Outputs (displays, errors, reports) stay byte-identical to
  haskell-final's unless a step lists a difference by design (section 7).
  A difference gets a `test/golden/port/NAME` expectation and a line in
  section 7.
- DESIGN.md is Sam's (sfultong) document. Don't edit it. Record how the
  port resolves an item in the README's "Design" section (under "Status:
  moving to Bend") and here.
- Commit per step, each gated on the checks in section 9.

## 2. Setting up the new computer

```sh
git clone git@github.com:hhefesto/stand-in-language.git telomare
cd telomare
git checkout bend-port
git remote add telomare git@github.com:Stand-In-Language/stand-in-language.git
git fetch telomare            # telomare/master = 2ae49e0a (Sam's DESIGN.md)
git tag haskell-final 1270d8b3  # the tag is local-only; its commit is in bend-port
git config core.hooksPath hooks # pre-commit: bend bend/Everything.bend --check-only
echo 'use flake . -Lv' > .envrc # optional: direnv (it was a local file)
nix develop                     # bend 2.0.34 on PATH (flake input, rev 01875127)
nix flake check                 # telomare, bend-check, bend-tests, goldens: minutes
```

Other remotes on the old machine: `sfultong` (sfultong/stand-in-language),
`junkicide`, `private` (hhefesto/telomare-private), `delfos` (a LAN host).

To build the port: `bend bend/Main.bend -o /tmp/bin/telomare`. It takes about
65 s and peaks at 3–5 GB.

To build the oracle, i.e. haskell-final's `telomare`:
```sh
git worktree add ../telomare-haskell-final haskell-final
cd ../telomare-haskell-final && nix build --accept-flake-config .#telomare
# binary: ../telomare-haskell-final/result/bin/telomare
```
On the old machine it sat at
`/tmp/claude-1000/-home-hhefesto-src-telomare/df6c1806-08ed-4cba-89db-b2556657b09e/scratchpad/oracle/bin/telomare`.
That copy is gone after the move.

**What did not travel.** Copy these by hand if you want them:
- Claude's memory directory (above), and `~/.claude/plans/`.
- `notes.md` at the repo root. It is the private timesheet notes and is
  gitignored on purpose; don't commit it.
- `interview/`: the Bend interview drills, excluded in `.git/info/exclude`.
- `.envrc`.
- Local branches that were never pushed:
  - `backup/bend-port-pre-design-rebase-2026-09-30`: bend-port before the
    DESIGN rebase (old tip `f8aff8e6`).
  - `backup/ic-space-bounds-local-2026-09-29`, `keep/ic-model2`,
    `space-bounds-pre-rewrite`, `space-bounds-pre-squash`,
    `nonmonadic-sizing-prototype`, `telomare3-m2-core`,
    `refactor/handoff-runtime-cleanup`, `hhefesto/simplification-review`,
    `agda`.

  Push them to the `private` remote if any matter, but only when the user
  asks.
- `tictactoe.telc` at the root: an old v2 artifact, worthless.
- `src/` (ignored Haskell leftovers).
- The scratchpads under `/tmp/claude-1000/…`. Their useful parts (the
  parity programs, haskell-final's outputs, `bench.sh`) are now in
  `bend/dev/`.

## 3. Where the branch stands

`bend-port` sits on telomare/master `2ae49e0a` ("adding official design
doc"). It is Telomare rewritten in Bend 2, with only the
interaction-combinator (IC) runtime. The commits since `telomare/master`, 35
before this handoff, are:
- `7f91d419` … `4962f955`: PR #152 (ekapkgs build) and PR #153 (the IC
  work: IC certificate, `.telc` v4, `--draw-net`), still in Haskell.
- `1270d8b3`: records haskell-final's outputs as goldens. This is the tag
  `haskell-final`, the last commit with Haskell.
- `503c306b` … `b0917c2e`: the Bend milestones (scaffold, parse/resolve,
  sizing, IC, the `telomare` app, EAL, `case`/`#`).
- `a1b24e13` … `16596046`: performance rounds.
- `a2ee8246` … `0c062de5`: the DESIGN.md alignment (section 6).

Pushed: `origin/bend-port` (hhefesto/stand-in-language) was force-pushed at
`0c062de5` on 2026-09-30, and this handoff's commits were pushed on top on
2026-10-01. There is no PR; the user decides.

**Checks at `0c062de5`, all green:**
- `nix flake check` passed at every commit.
- `bend bend/Everything.bend` prints `ALL PROOFS CHECK`.
- The test binaries all pass: lexical (8 groups), front (13), size (6),
  eal (14), ic (16, including `ic-usage-agrees`).
- 22 ported golden cases pass.
- The corpus (section 10) matches haskell-final on `--ic --meter` (13
  programs) and `--certificate` (14 programs).

**Interaction counts that tests pin** (guided, as in haskell-final):
- tc_ultra_minimal: 524
- simpleplus `3 4`: 1,517,868
- tictactoe test game (`1 9 2 8 3`): 15,168,230

**Templates after `7103aa53`** (one per exactly-equal body):
- tc 34 → 17
- simpleplus 664 → 94
- tictactoe 2958 → 194
- casea 883 → 101
- natudt 1484 → 109
- rat 380 → 91

**Speed.** On the old machine, an AMD Ryzen 7 3700X (8 cores, 16 threads), a
whole Bend run against haskell-final `--ic` gave:
- tc 0.03 vs 0.07 s
- simpleplus 1.2 vs 10.9 s
- tictactoe 7.7 vs 81 s
- casea 1.6 vs 38 s
- ctprop 4.9 vs 206 s
- natarith 1.3 vs 13.9 s
- natudt 3.3 vs 61 s
- rat 2.4 vs 30.6 s

The README's "Speed: Haskell to Bend" table holds these. Re-baseline on the
new machine before any perf work (`bend/dev/bench.sh`).

**A finding to keep:** `bend/dev/corpus/ratarith.tel` (Rational arithmetic)
dies of fuel under both haskell-final `--ic` and the port:
`IC runtime: ICFuelExhausted 10000000`, at 10,000,000 interactions. P4 is
expected to change that (section 4).

## 4. The plan: P1–P7

**Asked on 2026-10-01:**
- "Plan and start a new HANDOFF.md for resolving" four DESIGN §11 items:
  - certified ≠ executed term (§3, §11.4);
  - abort as a core form (§10, §11.6, C5);
  - strict vs lazy `if` (§11.3);
  - `trace` (§11.7).
- "and a plan to implement" `--fast`, `.telc`, and the two perf leads
  (EAL's final-state drop, and the IC's stack being a cons list).

**The user's decisions (2026-10-01, by question):**
- `if`: keep one conditional, the strict gate-switch shape the analyses
  already read, and **make the IC run only the chosen branch**.
- `trace`: **remove it.**
- `.telc`: **haskell-final's version 4 format.** The port writes no IC
  space certificate, stores its EAL layouts, and can read haskell-final's
  artifacts by skipping their IC certificate.
- `--fast`: on the IC. This was not asked as a question: C4 ("one
  runtime") and an IC-only port leave no other choice.

**Nothing in P1–P7 is implemented yet.** The user said to stop after the
handoff. The order below runs from output-preserving work to work that
changes outputs. P5 needs P4.

Every step:
- is gated on section 9's checks;
- is one commit or a few, without a co-author line;
- updates this file and the README's "Design" section;
- is pushed only when the user asks.

### P1. Performance, output-preserving

Re-baseline first: build the port and the oracle, then run
`bend/dev/bench.sh` plus `ealtime tictactoe` and `icmeter tictactoe 1 9 2 8 3`.

**P1a. The IC's pending-pair stack is a cons list.**

Now:
- `type Ctl` (IC.bend:49-51) is `Ctl{+stk: List<&2, U32>, +cold, +bump,
  +free, +label, +fuel, +err, +cap}`, inside `Net{mem: Array<U32>, tpl:
  Array<U32>, ctl: Ctl}` (54-55).
- `push` (1011-1016) is `Ctl{a <> b <> stk, …}`: two cons cells per push.
  It is reached through `push.if/kb/ka` and `connect.push` (1018-1036),
  which `connect` (1040-1042) calls.
- `pop` (1790-1795) takes `stk` out and leaves `Ctl{[], …}`, so the record
  stays unshared. `pop.list` (1774-1779) matches
  `Con{+a, Con{+b, rest}}`; `set.stk` (1764-1772) rebuilds the record.
  `pop.ka/kb/pa/pb/done` (821-842) check that the pair still faces each
  other and give `PPair` or `PStale` (`Popped`, 133-136).
- `reduce(fuel, st)` (1799-1816) is `reduce(f, pop(fire(net, a, b)))`. It is
  entered from `finish` (2590) and `run` (2603).
- The stack starts as `[]` in `reset.ctl` (2252-2254), `scratch` (2396) and
  `net.new` (2441).
- The header comment (16-17): LIFO, and "every rule consumes the pair it
  fires, so the count of interactions does not depend on the order".

Try in this order, keeping the fastest that leaves every count identical:
1. **One cell per pair:** `type Stk is Data: SNil{} | SPush{+a: U32,
   +b: U32, +rest: Stk}`. This halves the allocations, and `Ctl` stays 8
   words.
2. **The stack inside `mem`:** words 6 and 7 of every 8-word agent slot are
   unused. `init` writes words 0, 4 and 5, ports use 1–3, and nothing reads
   `*8+6` or `*8+7`. Keep stack entry k at `mem[k*8+6]` and `mem[k*8+7]`,
   and make `stk` a `U32` stack pointer.
   - Push must grow when the pointer reaches `cap`; `grow` (1080-1085)
     already copies `cap*8` words.
   - Index by stack position, never by agent. Stale entries plus agent
     reuse would overwrite links.
3. A separate `Array<U32>` on `Net`. This is least likely: it adds a word to
   every flattened call.

**Don't retry:**
- counters in an array (`33842008`: 20% slower);
- widening `Ctl` past 8 hot words (~20%).

Gate:
- counts identical: `ic-meter-*` groups in `bend/tests/ic.bend`,
  `*.ic-meter` goldens and the corpus meters;
- session time from `icmeter` or `time`. `phases` is stale (section 10):
  fix it first if you want per-phase times.

**P1b. EAL frees its final state slowly (about 13% of tictactoe's certification).**

How it was measured (2026-09-30): `ealtime` was rebuilt from its emitted C
with frame pointers and profiled with perf on tictactoe.
- `term_drop` was 18.36% of the time, 15.06% of it through `term_sink`.
- 6.73% was in `spin_229` inside `WL_FID____EAL_RUN_K790`: 6 sinks, one per
  array of the solver state `Sv{c, cb, q, qb, v, n}`.
- 6.68% was in `spin_378`: 9 sinks, one per field of `St`, dropped at the
  end of every per-body analysis.
- So freeing the analysis state is ~13% of tictactoe's certification. About
  half is at the end of the solver, half at the end of each per-body
  analysis.
- An IC profile shows the same pattern for the whole pipeline:
  `term_drop` 13.20%, `rfc_wrap` 5.17%, `span_fade` 3.11%.

**Why freeing is expensive** (Bend runtime, `bend2/comp.ts` in the flake
input):
- An `Array<U32>` is a BUF block, freed in one step (`term_drop`, ~4135).
- An array of boxed values is an ARR block. `term_drop` visits every one of
  its 2^c slots (4142-4185).
- A slot holding a shared (`+`) value costs an atomic refcount decrement
  (4122-4131).
- Nullary constructors and numbers are cheap (`term_triv`, 4041).

**The state** (types at EAL.bend 171-178 and 293-295):
- Cheap: `m`, `ps`, `X.sv`, `X.ct` are `Array<U32>`. `m` is 8 words per
  variable; tictactoe's certify pass has 889,086 variables.
- Boxed:
  - `tg: Array<List<TE>>`: one slot per variable, grown in `grow.m`
    (812-816). Empty slots are `[]`, which is cheap.
  - `X.sites: Array<Site>`: unused slots hold the shared `site.none()`
    (406), so each costs a refcount decrement.
  - `X.bl: Array<Blame>`: unused slots hold the shared `blame.none()` =
    `Blame{Unknown, ""}` (403).
  - `X.tp: Array<Tp>`: the template lists.
  - `X.eqs: List<SumEq>`: each entry has a `lhs` list and a fresh
    `Blame{loc, what}` from `sum.eq`.
- In the solver: `Sv.c`, `q`, `v`, `n` are cheap `U32` arrays. `Sv.cb` (one
  slot per variable root) and `Sv.qb` (one per equation) are
  `Array<Blame>`, filled by `fill.root`/`fill` through `blame.get`
  (~3950-3970).

**Where the state is dropped:**
- The solver: `run` (3871) returns `sv.err(…)` (3460-3465), which matches
  `Sv{c, cb, q, qb, v, n, ch}` and erases all six arrays. It is called from
  `solve.sv` (3982); the tables are built in `solve.size` (3988-3995).
- Per body:
  - `failure.of` (4395) and `st.err` (4373) keep only the error;
    `standalone` (4400) uses them.
  - `verdicts` (4433) runs one `st.new` + `analyze` per body, as a parallel
    fork-join. tictactoe has 3,054 bodies.
  - `main.done` (4444), `lay.done` (4504) and `lay.sg` (4516) drop the
    whole program's `St`.

tictactoe figures on the old machine (`ealtime`):
- certify pass: 889,086 variables, 10,053 sites, 119,517 pairs, 145,051
  blames; main 848 ms, verdicts 972 ms;
- the sized pass, used for layouts, gives up at the 2,000,000-variable
  budget.

Candidates, in order:
1. Keep blame **numbers** (`U32`) in the solver instead of `Blame` values.
   A variable's class already stores its blame number at word `r*8+19` of
   `m`. `SvErr` would carry numbers and resolve them through `bl` after
   `run`. Then all of `Sv` is `U32` arrays, which are cheap to free.
2. Mark unused slots with a nullary constructor (cheap) instead of the
   shared `site.none()` and `blame.none()`.
3. Reuse one state per verdict lane instead of a fresh `st.new` for each of
   the 3,054 bodies, the way the IC's `reset` keeps `mem`.

**Don't retry:** equations as rows written at creation. It was 7–9% slower;
per-word writes through the state cost more than consing.

Gate:
- verdicts and layouts byte-identical: `bend/tests/eal.bend` (all
  groups), the `*.certificate` goldens, corpus certificates, and IC counts
  unchanged (layouts drive guidance);
- `ealtime tictactoe` before and after.

### P2. Remove `trace` (DESIGN §11.7, the user's decision)

Today `trace` is a builtin (`trace = \x -> STrace x`, Desugar.bend:46-47,
62). In-scope applications are rewritten to `STrace` (201-202, 288-289,
344-345). The form is carried through:
- Syntax.bend:57
- Expand.bend:486-489
- Resolve.bend:117, 316-317
- Levels.bend:269
- Lower.bend:487-490, 902-905, 1225-1228, becoming `TTrace` (Term.bend:28)

`show` prints `TraceUPF` (Lower.bend:702-703), so it enters `#` hashes. At
Split it becomes `FTrace` (Split.bend:162-163) and is then built as
`T.C.retag(a, x)` (353-356), the identity. haskell-final did the same:
`HTraceF x -> one x id -- TODO add trace back in, or rethink`
(`src/Telomare/Resolve.hs:257`).

No `.tel` file uses it, now or at haskell-final.

Remove the builtin and `STrace`/`TTrace`/`FTrace` everywhere; `trace` then
becomes an ordinary (undefined) name. Also:
- `bend/tests/front.bend:53`, `accepts("trace (\\x -> (\\y -> (x,y))) 0 0")`,
  still parses; keep or drop it.
- README.md:116-117 documents the no-op; replace it with a line in "Design"
  ("§11.7: removed; it had no runtime meaning, and restoring it would need a
  side channel through the IC (C1/C4)").

Gate: the full checks; outputs are unchanged.

### P3. Certify the term that runs (DESIGN §3 [open], §11.4)

**The two builds:**
- `Front.bend:44-47` holds `Terms{cert, run}`. `lowered` (176-180) builds
  `cert` with `Lw.process(t)` first, then `run` with `Lw.process.let(t)`.
  Both go through `Sp.split` (162-167). Since `cert` is built first, its
  errors are the ones reported.
- `cert` (`process`, Lower.bend:753-757):
  - `validate` (400-501) inlines each let value at every use through an env
    map (412-421), in `let.order`'s order (350-355).
  - Every lambda is `Open`, and `close.lams` is never applied.
  - Each `SRec` becomes `TApp(TRec, TRep)` (471-476), with one `TRep` per
    inlined copy.
  - A missing variable gives `MissingDefinitionAt{loc,n}` (367-372).
- `run` (`process.let`, 1284-1289):
  - `annotate` (839-936) numbers the recursion sites per binding as
    `{t,r,b} :n`.
  - `lta` (1147-1246) turns lets into `(\n -> body) value`, with kind
    `LetB{c}`; `let.build` (1073-1077) drops unreachable bindings.
  - `add.repeaters` (1248-1281).
  - `debruijn(app=True)` gives each use of a let-bound name c fresh `TRep`s
    (529-555).
  - `close.lams` (619-655).
  - Missing names give `MissingDefinitions` ("undefined identifier").
- The `#` hashes probably differ between the builds: `kind.show` (660-667)
  is part of the hashed text, and a UDT wrapper is a lambda containing a
  let.

**Certification:**
- `Main.bend:292-299` calls `certified(run, EAL.certify(Lf.defer.lift(cert)))`.
  On success, `Main.bend:285-290` sizes `E.of.term3(run)` with budget
  65536.
- `EAL.certify` (EAL.bend:4485) runs `inferred` (4479-4482), which is:
  - the standalone verdicts of every body, in parallel (4433-4435);
  - `main.shape` with the virtual application to input (4457-4458);
  - a dependency check (4469-4470);
  - the "main is data" check (4146-4159).
- `Lf.defer.lift : T.C -> Lifted` (Lift.bend:211-212) takes any Term3.
  **Certifying `run` is a one-line change at Main.bend:299.**

**Expect:**
- New rejections are possible. In `run`, a let value used k times is a
  contraction of one env path (`contraction`/`dup.of`, EAL.bend:489-493),
  which needs a box; inlining avoided that.
- EAL ignores refinement validators in the main walk (`to.a` 519-520,
  usage 453-454, `gen.intr` 2234-2235; their refs are dependency-checked at
  4121-4122). Unsized holes count as Env (507-508).
- The testchar golden, `RE (missing definition "not" at line 2, column
  52)`, comes only from the `cert` path.
- Tests that read `cert`: `bend/tests/eal.bend` `program`/`sized`/`main.hash`
  (199-288), and the `eal-lift-udt` digest (378-380). `eal-sized`
  (217-226, 369-377) sizes `cert`.

**Steps:**
1. **Measure.** Write a `bend/dev/certrun.bend` that, for a module, certifies
   both `cert` and `run` and prints each verdict, its time and its
   variable count. (Copy `ealtime.bend`'s setup; it already builds both
   terms.) Run it over the three goldens' programs, testchar,
   `test/programs/limits/*` and `bend/dev/corpus/*`.
2. **If `run` certifies wherever `cert` does:**
   - Certify `run` and delete the `cert` build: `Front.Terms` becomes one
     term, and `Lower.process`/`validate` go if nothing else uses them.
   - Make the `run` path's missing-definition error render exactly as the
     testchar golden expects.
   - Move the eal tests to `run`, re-pinning `eal-lift-udt`'s digest with
     the reason.
   - Runtime outputs cannot change: the executed term is untouched.
3. **If some programs are rejected:** read the blame (`EALBoxConflict` names
   both sites). Fix EAL only where the fix fits naturally, such as boxing a
   contracted let-bound closure. Otherwise stop and report the data to the
   user. The fallback, running `cert` itself, needs their OK. It is ~15×
   bigger (tictactoe: 3,054 bodies against 194 templates), so measure its
   sizing and IC cost first.
4. **README "Design":** "§3/§11.4: the port certifies the term it runs".

### P4. One conditional; the IC runs only the chosen branch (DESIGN §11.3)

**The shapes today:**
- Surface `if` lowers to the **strict** shape
  `SetEnv(Pair(SetEnv(Pair(Gate,i)), Pair(e,t)))`. The path is `SIte`
  (Parse.bend:636; `case` lowering emits it too, Desugar.bend:542-556) →
  `TIte` (Lower.bend:445-450, 1205-1210) → `FIte` → `ite.of`
  (Split.bend:299-301, 339-344). haskell-final did the same (`ITEF → iteB_`,
  rationale at `src/Telomare/IR/Base.hs:126-136`).
- The **lazy** shape is `Expr.ite` (Expr.bend:100-102) and `Co.ite`
  (Core.bend:190-192): the branches are `Defer -4` and `Defer -5`, then
  applied to Env. Production uses it only in sizing's `step.body`
  (Expr.bend:131-138), via `stub.expand`/`step.next` (Size.bend:436-449).
  `Co.ite` appears only in tests.
- The sized chain is strict on purpose: `approx.body` uses `gate.switch`
  (Expr.bend:96-98, 140-151). The rationale is EAL level-flatness
  (`src/Telomare/Machine.hs:399-413` at haskell-final).
- Sizing's input-restriction extraction needs the strict shape. `extract`
  (Size.bend:647-667) matches only `XSetEnv{XPair{XAbort{}, i}}` (660) and
  the strict shape (662-665). Sizing also evaluates both strict branches,
  because `XPair` evaluation (699-700) happens before the gate selects.
- The IC speculates. The branch pair compiles as two live subnets
  (IC.bend `compile`, `CdPair`, 1960-1967). The gate's select instantiates
  selector template 0 or 1 (1264-1282), and the projection sends an eraser
  to the losing branch (1295-1301). An eraser only consumes values
  (`rule.of` 790-797), so a diverging dead branch runs until the fuel is
  gone.
- **The pin:** `bend/tests/ic.bend:364-367`, group `ic-laziness`:
  1. lazy `Co.ite` with omega in the dead branch gives 0;
  2. **the strict shape with `omega.applied` in the dead branch runs dry at
     50,000 fuel** (`runs.dry` 97-98, omega 60-65);
  3. the strict shape with a stuck dead branch gives 0.

  haskell-final's original is `test/ICTests.hs`, "branch laziness (iteB vs
  iteB_)" (543), "strict ite speculates: a diverging dead branch is fuel
  death" (550-560). It also asserted that the **reference evaluator** gives
  `Right z` on the strict term.

**The story to record:**
- The core has one conditional, the gate-switch shape. Sizing and EAL keep
  reading it as they do; nothing changes for them.
- The core is total for certified programs, and an abort is a value: a dead
  branch's aborted value is projected away, and Session looks for aborts
  only in the result. So evaluating the unchosen branch can change only the
  cost, never the result. When a branch is evaluated is the runtime's
  choice.
- The IC chooses selection. This narrows DESIGN §7's "eager speculation is
  accepted" to everything except gate branches. Against its rationale:
  selection removes both the dead-branch cost and the fuel death. The price
  is handing the env to the chosen branch.
- Afterwards the IC agrees with haskell-final's reference evaluator, the
  oracle (§6), on the pinned case.

**How:**
- In `IC.collect` (IC.bend:2125), recognise
  `Co.VSetEnv{Co.VPair{Co.VSetEnv{Co.VPair{Co.VGate{}, s}}, Co.VPair{l, r}}}`
  and collect it as `Co.ite`'s shape:
  `SetEnv(Pair(SetEnv(Pair(SetEnv(Pair(Gate, s')), Pair(Ref l', Ref r'))), Env))`.
  - `l` and `r` become templates through `c.add(fi, code, orig)`, with
    `orig` set to `l` and `r`.
  - The function indices are `Co.step.e.ind()`/`step.t.ind()` (-4/-5),
    as in `Co.ite`.
- Readback should not change: a template keeps its `orig: Co.V`
  (`Src{…, orig, …}`, `c.named` 2055-2062), and an enclosing closure reads
  back through its own `orig`, the strict shape. Check this on a test that
  shows a stuck closure.
- Guidance: the branch templates get code hashes in `c.named`, but EAL's
  layouts (computed over the sized term's DeferMap, where the branches are
  not Defers) have no entry for them. A branch template is applied at
  once and never duplicated as a value, so this should cost nothing.
  Check the guided counts.
- `ic-usage-agrees`: make it cover the branch templates. It compares
  `IC.usage` with `EAL.usage` on the same `Code`, so it should agree.
- Env cost: the chosen branch receives the whole env (`CdEnv`). Where the
  scrutinee uses env paths too, the splitter tree fans them. If some
  program's count gets worse, pass only the paths the branches use
  (capture trimming, like Split's lambda lifting), but measure first.
- Soundness: the abstract algorithm needs EAL, and the certified term is
  the strict one. The lazy net duplicates no more than the strict net does:
  the env goes to one branch instead of being fanned to both. Write that
  argument into the README "Design" line. Back it with all displays
  unchanged across the goldens and the corpus.

**Tests and goldens:**
- Flip pin 2 to expect 0, named "the IC runs only the chosen branch" and
  citing haskell-final's reference evaluator.
- Re-pin `ic-meter-*` (524 / 1,517,868 / 15,168,230 today) and re-record
  `test/golden/port/*.ic-meter` (`run.sh BIN record-port '*.ic-meter'`).
- Displays must stay identical, except possibly ratarith. If it now
  finishes, compare with the oracle's reference evaluator
  (`telomare ratarith.tel` without `--ic`) and record it in section 7.
- Section 7 gets a line: interaction counts differ from haskell-final
  `--ic` by design, from P4 on.

**P4b, measured follow-up: retire sizing's lazy `ite`.**
- Let sizing select on the gate-switch when the scrutinee is known, and
  fork when it is symbolic. Then `step.body` uses `gate.switch`, and
  `Expr.ite`, `Co.ite` and the reserved -4/-5
  (`Core.step.e.ind`/`step.t.ind`) go.
- **Stop if any certificate count changes.** Sizing today evaluates dead
  strict branches of user `if`s and may size recursion sites reachable only
  there. If anything changes, report to the user instead of re-recording.

### P5. `--fast` on the IC (needs P4)

The facts are in section 5.1. The design:

**Pipeline:** certify, as P3 leaves it (the `run` term); skip sizing; run on
the IC with every recursion site an unbounded approximant that unrolls one
layer each time it is applied. Nothing proves termination, so fuel caps
each iteration.

**Types (H1):** give the runnable core a parameter for recursion sites, the
way `Syntax.Surf<P,C,N>` uses `Empty` witnesses.
- `type V<-U: Data>` gets `VLimit{+site: U}`.
- The sized core is `V<Empty>`: a site cannot be written.
- A fast program is `V<U32>`, with the token as the site.
- Build it from Term3 the way `E.of.term3` + `E.remove.checks` do,
  turning `CUnsized{tok}` into the site's closure. haskell-final:
  `FUnbounded site` evaluated in env `VPair trb _` gives `VRec site trb`,
  with `trb = (t, (r, (b, 0)))`.

  If the parameter ripples too far, a separate fast-core type is the
  fallback. But then `IC.collect` would be duplicated, which Appendix A
  warns against.

**The limit as code:**
- `VLimit{tok}` stands for the *code* of site tok's approximant. Its body
  takes env `(i, trb)`, builds its own recursion value
  `Pair(Defer[VLimit tok], trb)`, and runs `approx.body` with env
  `(i, (recur, trb))`. `approx.body`'s env is
  `(i, (recur, (t, (r, (b, 0)))))`: var 2 = t, 3 = r, 4 = b.
- The recursion value is a closure, i.e. data plus a code pointer.
  Building it unfolds nothing; only applying it, in the chosen recursion
  branch (P4), instantiates another layer.
- In `IC.collect`: allocate the template id for `tok` before collecting
  its body, and keep a token → tid map in `Coll`. The body's own
  `VLimit{tok}` then becomes a `CdRef` to the same id.
  - This is a cycle in the template table, but only through a reference
    leaf: code is a pointer (DESIGN §7).
  - Key these templates by token, not by `key.of`.
- Without P4 the IC would speculate the recursion branch forever. That is
  why P4 comes first.
- Watch for eager speculation elsewhere: an unused let value that holds a
  recursion still unrolls (to its test's end, or to fuel death). Haskell's
  Fast was call-by-need and would not. Compare unroll counts with
  haskell-final's and record any difference.

**Fuel and meter:**
- IC fuel already counts interactions per iteration (`run(p, net, input,
  +fuel)`, IC.bend:2603; `default.fuel` = 10,000,000).
- `--fast` defaults to 2^24 = 16,777,216 per iteration, and `--fuel 0`
  means uncapped.
- Out of fuel, keep haskell-final's text, with "interactions" for
  "applications and unrollings" (a difference by design), on stdout with
  exit 0:
  ```
  runtime error: out of fuel after 16,777,216 interactions.
  This run is not sized, so nothing proved it terminates. Raise the cap with --fuel N, or lift it entirely with --fuel 0.
  ```
- `--fast --meter`: on stderr, `IC interactions: N` (the port's meter line),
  then haskell-final's per-site table and footer verbatim (section 5.1).
  There are no "function applications" or "gate selections" lines; those
  were the Fast interpreter's own.
- Count unrolls per site by counting instantiations of the limit templates
  only, in `Ctl`'s cold part. Never widen the hot words.
- Owner names ("Prelude.foldr") come from haskell-final's `ownerMap`. Reuse
  `Levels`' owner logic (`Lv.Site{source, owner, ls}`, `Lv.show.def`).

**CLI** (`bend/Main.bend`):
- Remove `--fast` and `--fuel` from `old.flags` (58-60, 149).
- Usage becomes `telomare FILE.tel [--ic] [--meter | --certificate] [--fast [--fuel N]]`,
  or similar.
- `--fast --ic`: refuse. haskell-final refuses too, though its text is
  optparse's. Use the port's usage-error convention (exit 2, Main.bend:348)
  and record it.
- `--fuel` without `--fast`: refuse.
- `--fast --certificate`: haskell-final's unsized static report, with no EAL
  on that path. Its sizing section becomes
  `iterations: not inferred, because this program was not sized.` /
  `  Nothing here says it terminates. Compile it without --fast for that.`
  and has no correspondence paragraph. Add this as a variant of
  `Certificate.sizing`.
- `--fast` on a `.telc` (after P6): print
  `note: --fast does not apply to an already-compiled program`, then run it
  sized.

**Tests:**
- A new `bend/tests/fast.bend`, with its groups listed in `nix/bend.nix`
  `tests.fast`:
  - `fast-agrees`: `Session.replay` transcripts equal the sized ones
    (simpleplus `3 4`, tc_ultra_minimal, tictactoe `1 9 2 8 3`);
  - `fast-base-case`: the base case doesn't demand the recursive branch
    (fuel 100, one unroll);
  - `fast-sites`: simpleplus counts unrolls per site;
  - `fast-unsized`: `test/programs/limits/unbounded-input-recursion.tel`
    with input `a` reaches `done`, while the sized compile fails;
  - `fast-fuel`: cap 20 runs out, and uncapped finishes.
- Goldens: add cases (`simpleplus.fast`, `simpleplus.fast-meter`,
  `tc_ultra_minimal.fast-meter`, `tictactoe.fast`) to
  `test/golden/cases`:
  - record `expected/` with the oracle (`run.sh ORACLE_BIN_DIR record
    'GLOB'`);
  - record `port/` where the meter or fuel text differs
    (`record-port`);
  - add the patterns to `goldenPatterns`.

**README "Design":** `--fast` is an IC mode (C4); list its differences.

### P6. `.telc` artifacts in haskell-final's version 4 (user's decision)

The format and messages are in section 5.2.

**Writing** (`--compile [-o|--output FILE]`):
- The output defaults to the source path with `.telc` in place of `.tel`.
- Contents, in order: magic, version 4, entry, source hash, certificate
  text, report, budget, expr, IC certificate = Nothing (byte 0), layouts.
  - The certificate text is `Certificate.report`'s, already byte-identical
    to haskell-final's.
  - The report: counts token → Just n, locs token → LocTag, and the budget.
  - The expr is `Core.V` in tag order 0–9.
  - The layouts are the EAL layouts the IC runs with: digest →
    `Lf.Shape` as CapShape tags.
- Print on stderr `wrote <path> (<N> nodes, sources <first 12 hex>)`,
  exit 0. N is the node count of the expr.
- This is haskell-final's `--ic --compile` minus the IC certificate. Decide
  whether to accept `--ic --compile` as the same thing (haskell-final also
  printed the IC certificate on stderr, which the port can't); record the
  choice.

**Reading** (`X.telc`, recognised by its extension before anything else):
- Decode everything. Skip an IC certificate when present: Data.Binary
  `Integer`/`Natural` (section 5.2).
- Run with the stored layouts. Output and interaction counts must equal a
  run from source, with no EAL and no sizing.
- `X.telc --certificate` prints the stored text.
- `X.telc --meter` meters the run.
- `X.telc --compile` gives `X.telc is already compiled`.
- `X.telc --ic --certificate` stays refused.
- Staleness, magic and version messages are exactly haskell-final's.

**Locations:** map `L.Loc` (bend/Loc.bend) onto haskell-final's `LocTag`
encoding faithfully: Source span, Generated label plus parent, Builtin,
etc. Check against a haskell-final artifact.

**Bytes:**
- Write with `File.open(path, "w")` + `File.write_bytes(List<U32>)`. Values
  must be 0–255; a larger one fails with EINVAL before anything is written.
- Read with `Bytes.read` (bend/Text.bend 61-125: `File.read_bytes` in
  65536-byte chunks).
- int64 little-endian from U32 halves. A negative function index (U32 ≥
  2^31) has the high word 0xFFFFFFFF.
- The source hash goes through `bend/Sha256.bend` (UTF-8, lowercase hex).

**CLI:** remove `--compile`, `--output` and `-o` from `old.flags`.
`Main.with.path` (126-131) refuses `.telc` today.

**Compatibility checks** (with the oracle, by hand):
- haskell-final's `--ic --compile` artifacts for the three golden programs
  load in the port and run with identical output and counts (the layouts
  are equal).
- The port's artifacts load in haskell-final (`telomare X.telc --ic`) and
  run with identical output.
- Byte equality with haskell-final holds field by field, except the IC
  certificate. haskell-final's plain `--compile` writes Nothing and empty
  layouts; the port stores layouts.

**Tests:**
- A `bend/tests/telc.bend` covering:
  - a round trip of simpleplus (expr, entry, hash, certificate, counts,
    locs, budget);
  - a decoded tc_ultra_minimal runs like its source;
  - garbage gives an error containing "magic";
  - the hash changes with content and doesn't depend on module order;
  - simpleplus has more than 1000 nodes.
- Golden cases `P.compile` + `P.telc` (`P.telc` must equal `P.ic`'s
  expectation) through `record-port`. Cases of one program share a directory,
  in file order.
- The nine haskell-final `.telc` goldens stay excluded: they need its IC
  certificate.

### P7. Erase aborts the sizer proves dead (DESIGN §10 direction, §11.6, C5)

The facts are in section 5.3. The plan follows DESIGN §10's three parts:
1. checks discharged statically;
2. checks left to run time, visible as such;
3. code with no aborts.

**P7.1 Site identity (H1).**
- Number every check (`CCheck`, Split.bend:334-338) and every chain bottom
  (`Expr.chain(0)`, function index -9, message `(0, tok)`).
- Sizing's aborted values carry their site: `XAborted{site, m}`, or a site
  beside it. User-visible messages don't change.

**P7.2 Classify.**
- A check is a **runtime** check (part 2) when an aborted value from its
  site can reach main's symbolic result on some path. Sizing explores
  every input path, and `fold.aborted` (Size.bend:944-957) already
  inspects the result, but it ignores user aborts (tag 1). Make it collect
  them by site.
- Every other check is **discharged** (part 1).
- "Fired somewhere" is not the test, because sizing evaluates both strict
  branches; "reaches the result" is.
- Report both in `--certificate` as a new section, e.g.
  `checks: N discharged statically, M at run time:` with locations. This
  changes the `*.certificate` goldens and the corpus certificates: record
  them under `port/` with the reason, and list the change in section 7.
- **Ask the user before changing the report's format.**

**P7.3 Chain bottoms.**
- After the chains are built, evaluate the sized program symbolically once
  more, and require that no `(0, tok)` aborted value reaches the result.
  If one does, sizing was wrong: fail with `Sz.Internal` naming the site.
- Then replace every bottom by an inert value, Zero. Applying data gives a
  stuck value, which is erased when not demanded.
- Measure the extra pass (sizing all of tictactoe took ~0.2 s).

**P7.4 Erase discharged checks.**
- Have `E.remove.checks` (Expr.bend:158-178) keep only runtime sites. A
  discharged `CCheck` becomes its checked value.
- A program whose checks are all discharged has no `Abort` in its
  runnable core, so C5 holds for it.
- Counts drop: re-record the `port/` meters and the tests.

**P7.5 Decision point, for the user (and Sam).** What remains are runtime
checks. In the goldens that is input validation: simpleplus's `invalid
input` and tictactoe's input refinements. The options:
- (a) Keep `Abort` as the residual runtime check (part 2), with its
  footprint reported. This is recommended for now.
- (b) Move input refinements to the session boundary (§11.10: validate
  before calling main). Then `Abort` leaves the core, but this needs a
  language-level boundary discipline.

**Soundness:** classification is exactly as sound as sizing's path
exploration. That is the evaluation that already makes the program total,
so say so in the README line.

**Gate:**
- displays identical everywhere; the `simpleplus.*-abort` goldens keep
  their text;
- `tests/ic.bend:375` ("Non-exhaustive patterns in case") still fires;
- counts re-recorded with the reason.

## 5. Reference: what the research found

Gathered 2026-10-01 by reading `haskell-final` and `bend/`, so the next
machine needn't redo it. Read Haskell with `git show haskell-final:PATH`.

### 5.1 haskell-final `--fast` (`src/Telomare/Fast.hs`, 551 lines; CLI in `app/Main.hs`)

**CLI:**
- `data Mode = Sized | IC | Fast (Maybe Int)` (Main.hs:52-62). The parser
  (104-117) makes `--fast` and `--ic` alternatives.
- Both together fail with ``Invalid option `--ic'`` plus usage, exit 1.
  `--fuel` without `--fast` fails with `Missing: --fast`, exit 1.
- Help: `--fuel N  Cap on applications and unrollings per iteration under
  --fast (default 16777216; 0 for no cap)`.
- A `.telc` path is checked first; otherwise `Fast fuel -> runFast`
  (149-154).
- `runFast` (292-304):
  - `--compile` → `die "--compile sizes the program, so it cannot be combined with --fast"`.
  - `--draw-net` → `die "--draw-net draws the IC net; combine it with --ic"`.
  - `--certificate` → `staticReport Nothing Nothing`, which prints
    `iterations: not inferred, because this program was not sized.` /
    `  Nothing here says it terminates. Compile it without --fast for that.`
    (Certificate.hs:54-56). It has no correspondence paragraph and does no
    EAL check on this path.
  - Run or meter → `compileFast`, then `runFastLoop`. With `--meter`, after
    `hFlush stdout`, it writes `renderFastMeter` to stderr.
- `--fast` on a `.telc` prints
  `note: --fast does not apply to an already-compiled program` and runs it
  sized.

**`compileFast`** (479-497):
1. Parse and expand the modules. Errors read `"Error in module X:\n" <> err`.
2. `main2Term3` (= the port's `cert`) → `certifyMain`; a failure renders as
   `renderEALError`.
3. It **runs `main2Term3let`** (= `run`) through `term3ToFast (ownerMap
   modules)`, with no sizing, no `inferEALCompiled` and no static checks.

**`term3ToFast`** (502-526) maps 1:1 to `FastExpr`, except:
- `Term3Unsized tok` → `FUnbounded (RecursionSite tok anno owner)`;
- `AbortedF` → `Left "an already-aborted term in the source"`;
- a checking wrapper → `FSetEnv (FPair performTC (FPair tc c))`, where
  `performTC = FDefer (FSetEnv (FPair (FSetEnv (FPair FAbort (app (FLeft
  FEnv) (FRight FEnv)))) (FRight FEnv)))`. That is the port's
  `remove.checks` closure.
- `FDefer` drops the function index.

**`ownerMap`** (533-551) maps the `(file, offset)` of every `SourceLoc` in a
top-level binding's body to `"Module.def"`. The first one wins.
`GeneratedLoc` falls back to its parent, and an unknown owner prints `?`.

**Types** (93-129):
`RecursionSite{rsToken, rsLoc, rsOwner}`, ordered by token;
`FastExpr = FZero | FPair | FEnv | FSetEnv | FDefer | FGate | FLeft | FRight | FAbort | FUnbounded RecursionSite`;
`Value = VZero | VPair | VDefer FastExpr | VGate | VAbort | VAborted BasicExpr | VRec RecursionSite Value`.

**Unrolling:**
- `FUnbounded site` in env `VPair trb _` gives `VRec site trb` (354-357).
- Forcing it (278-283) counts an unroll and returns
  `VPair (VDefer approxBody) (VPair (VRec site trb) trb)`. The ladder is its
  own recursion slot: an infinite limit with no aborting base.
- `approxBody = approximantStep app iteFast slot` (296-300, IR/Recursion.hs:10-14)
  means `if t i then r recur i else b i`, with env
  `(i,(recur,(t,(r,(b,0)))))`.
- `iteFast s t e = FSetEnv (FPair (FSetEnv (FPair FGate s)) (FPair e t))`.
  This is the **strict shape**, but `evalFast` pattern-matches exactly that
  shape and evaluates only the chosen branch (339-346). That laziness is
  load-bearing, and it applies to every user `if` too.

**Fuel** (243-275):
- `defaultFastFuel = 2^24`.
- Fuel is charged per `VDefer` application (`tickApply`, including main's)
  and per unroll. Gates are counted but not charged.
- It is **per iteration**: `runEval` runs afresh for each main call (441).
- On exhaustion it prints on **stdout**, exit 0, and keeps the partial
  meter:
  ```
  runtime error: out of fuel after 16,777,216 applications and unrollings.
  This run is not sized, so nothing proved it terminates. Raise the cap with --fuel N, or lift it entirely with --fuel 0.
  ```
  The number has thousands separators (`commaInt`).
- Stuck: `runtime error (stuck): <why>`.

**Meter** (`renderFastMeter`, 162-196), on stderr. For simpleplus with
`3 4`:
```
function applications (measured): 2,479
gate selections (measured):       83
recursion unrolls (measured):     110 across 4 sites

  site   source            function          unrolls
  #1     Prelude:48:23     Prelude.foldr     48
  #0     Prelude:30:18     Prelude.dMinus    40
  #2     simpleplus:12:42  simpleplus.doAdd  12
  #3     simpleplus:12:28  simpleplus.doAdd  10

Unrolls are totals over the run, not depths, so they are not the same
measurement as --certificate's per-instantiation iteration counts.
```
- Rows are sorted by (−unrolls, `"#tok"`). The site column is `padRight 5`;
  the source and function columns are as wide as their longest entry;
  gutters are 2 spaces.
- Source is `renderLocTagCompact` (`file:line:col`). The count says "1 site"
  or "N sites". The table is omitted when there are no sites.
- tc_ultra_minimal: applications 19, gates 2, `2 across 1 site`, row
  `#0  tc_ultra_minimal:6:25  tc_ultra_minimal.main  2`.
- tictactoe: stdout byte-identical to `expected/tictactoe.run`; 69,252
  applications, 7,782 unrolls across 14 sites.
- The README at haskell-final shows 2,560 applications for simpleplus,
  which is stale.

**Aborts:**
- An aborted value is a value that can be discarded. It propagates through
  projections, `SetEnv` heads and gate scrutinees, and is never thrown.
- `findAbort` finds the leftmost abort anywhere in the result, state
  included, and prints `"runtime error:\n" <> show (AbortRunTime e)`.
- A result of `VZero` prints `aborted`. A display that isn't a string
  prints `error converting display value`.
- EOF ends quietly with exit 0.

**Tests at haskell-final:**
- `ConformanceTests.hs:31-38`: the fast transcript equals the sized one
  (simpleplus `["3 4"]`, tc_ultra_minimal `[]`).
- `ResolverTests.hs:436-438`: tictactoe `1,9,2,8,3`.
- `RunModeTests.hs`:
  - 90-111: the base case doesn't demand the recursive branch (fuel 100,
    result `(0,0)`, 1 unroll);
  - 113-122: unrolls are counted per site;
  - 124-133: it runs a program sizing rejects
    (`unbounded-input-recursion`, `["a"]`);
  - 135-144: the fuel cap (20 runs out; uncapped finishes);
  - 146-160: the unsized static report.

No golden case uses `--fast` or `--fuel`.

### 5.2 haskell-final `.telc` (`src/Telomare/Artifact.hs`, 348 lines)

**Record:** entry, source hash, report (`SizingReport`), certificate (the
rendered static report, with no `source hash:` line), expr
(`CompiledExpr`), `Maybe ICCertificate`, capture layouts
(`Map Digest CapShape`).

**Encoding:**
- Ints are int64 **little-endian**. A string is an int64LE byte length
  followed by UTF-8.
- Maybe is byte 0, or byte 1 then the payload; on read, any nonzero byte
  counts as Just.
- A list or map is an int64LE count, then its elements in ascending key
  order.

**Byte layout:**
```
"TELC" (54 45 4C 43) | int64LE version = 4
string entry | string sourceHash (64 lowercase hex) | string certificate text
report: map<token int64, Maybe int64 count> ; map<token int64, LocTag> ; int64 budget (65536)
expr, preorder, tag per node: 0 Zero | 1 Pair a b | 2 Env | 3 SetEnv x | 4 Defer int64 fnIndex, x
                              | 5 Gate | 6 Left x | 7 Right x | 8 Abort | 9 Aborted basic   (basic: 0 Zero | 1 Pair a b)
Maybe ICCertificate: method byte (0 ICAnalyzer | 1 ICCompositional), then 3 SpaceBounds (agents, ports, work/pending)
   SpaceBound = list<Affine>; Affine = map<Integer,Natural> coeffs + Natural const,
   with Data.Binary's put (BIG-endian): Integer = 0 + int32BE | 1 + sign byte + [Word8] (int64BE length, LE magnitude);
   Natural = 0 + word64BE | 1 + [Word8]
map<digest (string, hex), CapShape>: 0 Data | 1 Code | 2 Other | 3 Pair a b
LocTag (267-284): 0 Source span (Maybe string file; start, end = 3 × int64 line, col, offset)
   | 1 Generated string label, Maybe LocTag parent | 2 Builtin string | 3 Runtime | 4 Decompiled | 5 Unknown
```
`Core.V`'s ten constructors are in this tag order (Core.bend:16-26).

**Source hash** (`sourcesHash`, 102-110):
- SHA-256 of the UTF-8 of
  `concatMap (\(n,c) -> show (length n) <> ":" <> n <> show (length c) <> ":" <> c)`
  over the modules sorted by name. Lengths are in code points; the result
  is lowercase hex.
- The modules are the entry plus everything it imports, read from the cwd
  as `M.tel`.
- Golden prefixes: tc_ultra_minimal `a2a06b3bc4b3`, simpleplus (with
  Prelude) `b5486d3e7461`, tictactoe `1309be3f2e02`.

**Messages** (stderr, exit 1, via `die`, so `path: err`):
- Version: `X.telc: this artifact is version N, but this telomare reads version 4; recompile it from source`.
- Magic: `not a telomare artifact (bad magic number)`.
- Decoding: `not a readable telomare artifact: <err>`.
- Staleness (`warnIfStale`, Main.hs:203-212), only when `entry.tel` exists
  in the cwd:
  `note: the sources have changed since this program was compiled; recompile it to pick the changes up`.
  It then continues.

**CLI:**
- `--compile [-o|--output FILE]` is an alternative to `--certificate`,
  `--meter` and `--draw-net`. The output defaults to
  `replaceExtension file ".telc"`.
- With `--ic`, it first prints the IC certificate on stderr.
- It prints `wrote <path> (<nodeCount> nodes, sources <first 12 hex>)` on
  stderr, exit 0, with `nodeCount = cata (1+sum)`.
- `runArtifact` (167-199):
  - `--compile` → `X.telc is already compiled`;
  - `--certificate` → the stored text;
  - a plain run uses the reference evaluator;
  - `--ic` prepares under the stored layouts;
  - `--ic --certificate` prints the stored IC certificate, or recomputes it.

**Goldens:**
- Nine cases (`test/golden/cases` lines 22-24, 38-40, 53-55), all with
  `--ic`: `P.ic-compile`, `P.telc-ic`, `P.telc-ic-certificate`. All are
  excluded from `goldenPatterns`.
- `ic-compile`'s stderr is the IC certificate, then
  `wrote P.telc (881 / 23866 / 98610 nodes, sources a2a06b3bc4b3 / b5486d3e7461 / 1309be3f2e02)`.
- The written files are recorded as `--- files` lines (`sha256 size path`):
  `11994ea3…f7f2 4102`, `df8baa2a…3640 93765`, `0b753b81…1e 127369`.
- `telc-ic` equals `P.ic`.

**Tests at haskell-final:**
- `RunModeTests.hs:33-85, 177-183`: round trip, decoded run, garbage →
  "magic", hash properties, node count.
- `ICSpaceTests.hs:116-132`.

### 5.3 Aborts in the port

**Producers.** Split never builds `CAbort`; every user abort is a `CCheck`:
- `x : v = e`: Parse `FDefChecked` (Parse.bend:659-664) → `SCheck`
  (Expand.bend:593-598) → `TCheck` (Lower.bend:491-495) → `CCheck`
  (Split.bend:334-338).
- Prelude `abort = \str -> let x : (\y -> (1, str)) = 1 in x`
  (Prelude.tel:111-112): a check that always fails.
- `assert = \t s -> if not t then (1, s) else 0` (114): a validator.
- The UDT validator's `else abort "not T"` (Expand.bend:209-217).
- Pattern lambdas: `abort "buildMultiLambda: pattern not reached"`
  (Expand.bend:350-354).
- `case`: `if 1 then __case_abort "Non-exhaustive patterns in case" else 0`
  (Desugar.bend:542-548; the alias is at 86-90, and the pruner keeps
  `abort` by name, Resolve.bend:90-91).

**In sizing:**
- `E.remove.checks` (Expr.bend:158-178) makes each check the closure
  `refinement.tc` (function index -10), `Abort (tc c)` applied to c. It is
  applied at Size.bend:1038 and 1059-1060.
- The chain's bottom is a closure with index -9 that aborts with
  `(0, tok)` (Expr.bend:145-156). A site sized to n gets n+1 links
  (Size.bend:966-992).
- Sizing's internal aborts:
  - `step.over` → `(0,tok)` (451-460);
  - `test.var` → `(3,tok)` (413-432);
  - `abort.var` → `(2,0)` (514-519);
  - the tag builders are at Expr.bend:121-129.
- `abort.on` (521-534):
  - on 0, the identity closure (index -11);
  - on a pair, `XAborted{trunc}` (462-470);
  - on an input variable, AbortAny;
  - on a superposition, each side (752-758).
- `fail.of.abort` (900-909): `(0,t)` → FuelExhausted, `(2,0)` → AbortAny,
  `(3,t)` → UnboundedInput, and `(1,s)` is ignored.
- `fold.aborted` (944-957) looks only at tags 0, 2 and 3.
- The limits pass assumes every check passes (660-661).
- Nothing re-checks the chain bottoms after sizing.

**Tags** (the message's left component):
- 0: recursion, with the token;
- 1: user, with the string;
- 2: any;
- 3: unsizeable, with the token.

They are unprotected: a validator returning `(0,n)` shows as a recursion
overflow.

**Core:** `VAbort` and `VAborted{D}` print as `!` and `?`. `E.core` turns a
non-data message into `Leftover`.

**IC:**
- `CdAbort`/`CdAborted` (IC.bend:31-32); agent kinds abort=6, aborted=9,
  scrut.abort=15 (226-254).
- Applying Abort waits for its argument (`RAwaitAbort`, 738, 1684):
  - on 0, template 2, the identity (1696, 2162-2166);
  - on a pair, `RAbortPair` (1287-1293);
  - on something that isn't data, it is stuck (1284-1285, 1700).
- Aborted values pass through (711-720, 1249-1252), and are split, erased or
  duplicated (1320-1337, 1360-1365, 1384-1393).
- Readback truncates in data mode (2479-2496, 2520-2536, 2550-2551).

**EAL:** Abort is a builtin tag (EAL.bend:359) with an identity
continuation (3000-3022).

**What the user sees** (Session.bend):
- `aborted` (53-69) finds the leftmost `VAborted` anywhere in the result,
  under Defer too.
- `value` (122-127) prints `runtime error:\nAborted, ` plus
  `abort.message`, on stdout, exit 0 (Main.bend:227-230).
- `abort.message` (34-44) gives one of:
  - `recursion overflow (should be caught by other means) for rt: Just N`
  - `user abort: <text>`
  - `user abort invalid data: <Fix…>`
  - `user abort of all possible abort reasons (non-deterministic input)`
  - `unexpected abort: <Fix…>`
- A result of 0 prints `aborted`.

**Goldens with abort text:** `simpleplus.run-abort` and `simpleplus.ic-abort`
(input `9 a`):
`enter two digits separated by a space` / `runtime error:` /
`Aborted, user abort: invalid input`. Tests: `tests/ic.bend:375`, and
`ic-abort` (353-358).

**Programs with aborts or refinements:**
- simpleplus.tel:5-8, 14
- tictactoe.tel:38-40, 68-71
- testchar.tel:6, 11
- test/programs/limits/over-budget-recursion.tel:20, 29
- unbounded-input-recursion.tel:22
- Prelude.tel:70-71, 111-114, 148-149

### 5.4 EAL budgets (EAL.bend:333-349)

| Budget | Value | Where it's checked |
|---|---|---|
| `level.cap` | 4096 | 1263/1271, 3534-3546, 3718, 3744 |
| `depth.cap` | 1024 | 2965-2968, 3028 |
| `var.budget` | 2,000,000 | `budget.err` 808-809, `fresh` 831, template copy 2904-2913 |
| `poly.cap` | 16384 | 2935-2952 |
| dispatch rounds | > 10000 → "application dispatch did not converge" | 3201-3227 |
| solver rounds | k·4+64 propagation, k·4+16 adjust | 3871-3874 |

**The IC layouts pass** (the analogue of haskell-final's `prepareEntry`):
- `Session.prepared` (137-140) calls
  `IC.prepare(expr, EAL.layouts(Lf.defer.lift(Lf.of.expr(expr))))`.
- Any error in `main.shapes` gives an empty map, and the program then runs
  unguided without a word (EAL.bend:4508-4530; IC.bend `hashes.for`,
  2409-2421).
- tictactoe hits `var.budget` here, in both implementations.

### 5.5 Bend 2 IO (`bend2/base.bend` in the flake input)

`R<A>` below means `Result<&1, &1, U32 & String, A>`.

| Function | Signature | Notes |
|---|---|---|
| `IO.print` / `IO.write` / `IO.print_err` | `(String) -> IO(Unit)` | stdout with a newline / stdout without / stderr with a newline |
| `IO.args` | `() -> IO(List<String>)` | the first item is argv[0] |
| `IO.die` | `(-A, code: U32, msg: String) -> IO(A)` | msg + newline on stderr, then exit |
| `IO.now` | `() -> IO(Nat)` | milliseconds |
| `File.open` | `(path, mode) -> IO(R<File>)` | modes only `"r"`, `"w"` (create/truncate 0644), `"a"` |
| `File.read_bytes` | `(File, max: U32) -> IO(File & R<List<&2, U32>>)` | one `read(2)`; `[]` at end of file |
| `File.read_at` | `(File, offset, max) -> …` | `pread` |
| `File.size` | `(File) -> IO(File & R<U32>)` | fails above 4 GiB |
| `File.write` | `(File, String) -> …` | UTF-8 encodes, so not for binary |
| `File.write_bytes` | `(File, List<&2, U32>) -> IO(File & R<Unit>)` | raw bytes; a value > 255 fails with EINVAL before writing |
| `File.close` | `(File) -> IO(Unit)` | |

There is no stdin primitive (the port opens `/dev/stdin`), no exists check
(open `"r"` and look for code 2), and no rename, delete or mkdir except
through `Process.run`.

## 6. Done: DESIGN alignment (2026-09-30)

Sam committed `DESIGN.md` to telomare/master as `2ae49e0a`. On 2026-09-30:
- `bend-port` was rebased onto it. The old tip is the local branch
  `backup/bend-port-pre-design-rebase-2026-09-30`, and the tag
  `haskell-final` moved to the rebased goldens commit `1270d8b3`.
- The port was aligned with DESIGN.md. DESIGN.md's module names refer to
  the Haskell at `haskell-final`.

How DESIGN.md binds the port, using its own tags:
- **[commitment]** C1–C5: the port meets them.
- **[heuristic]** H1: the port follows it by default.
- **[decision]**: the port follows it, or records here why it differs.
- **[direction]** / **[open]**: the port kept haskell-final's behaviour
  until the user asked on 2026-10-01 for P2–P7.

Key: ✔ follows · ≠ differs, with a reason · — not applicable

**Commitments**

| DESIGN | Port | Where / what |
|---|---|---|
| C1 small core | ✔ | `bend/Core.bend` `V`: Zero, Pair, Env, SetEnv, Defer, Gate, Left, Right + Abort (and Aborted, a result only) |
| C2 total | ✔ | certifyMain gate, then sizing (`Main.bend`: `compile` → resolved → certified → sized) |
| C3 resource use is an output | ✔ `a2ee8246` | `--certificate` (sizing's counts + `Levels`), `--meter` (session interactions) |
| C4 one runtime | ✔ | IC only; the goldens recorded from haskell-final play the second runtime's oracle role |
| C5 abort erased | ≠ until P7 | Abort is a core form and the IC implements it |

**Heuristic**

| DESIGN | Port | Where / what |
|---|---|---|
| H1 eliminated forms unrepresentable | ✔ `37e8d85a` `f2a3247c` `0a171419` `26bf8332` | `Syntax.Surf<P, C, N>` indexed by stage (`Parsed`, `Expanded`, `Desugared`, `Lowering`; an eliminated constructor carries an `Empty` witness); `Term.T<V>` (Term1 = names, Term2 = indices); the sized program is `Core.V`, data is `Core.D`, the IC's collected code is `IC.Code`; errors typed per stage (`Fr.Err`, `Sz.SizeFail` with no catch-all, `IC.Fault`, `Main.Failure`) |

**Decisions**

| § | DESIGN decision | Port | Notes |
|---|---|---|---|
| 1 | small conventional surface; no native numbers | ✔ | |
| 2 | eight forms + abort; no binders; SetEnv the sole eliminator; encodings; `$n` Church literals; negative FunctionIndexes | ✔ | `Co.neg(k)` indices as in haskell-final |
| 3 | stage pipeline, eliminated forms by type | ✔ | see H1 |
| 3 | lambda lifting with capture trimming at splitExpr | ✔ | `Split.bend` |
| 3 | UDT identity = structural hash; UDT surface convention | ✔ | `Lower.bend` `hashed`, `Expand.bend` |
| 4 | `{t, r, b}`; counts inferred; per-use-site oracle; approximant chain, strict shape; default budget 65536 | ✔ | `Size.bend` |
| 4 | exactly two failure kinds, named, with the site | ✔ `f2a3247c` | `Sz.UnboundedInput`, `Sz.FuelExhausted`; sizing's own failures named apart (`AbortAny`, `Internal`, `Leftover`) |
| 4 | `uncurryRecursions` / `uncurryBindings` | — | in neither master nor haskell-final (Sam's uncommitted work); port it when it lands upstream |
| 5 | EAL instead of a type checker; data-only main rejected; caps reject but never mis-certify; tags, not arrows; path-granular contraction; virtual application of main; advisory guidance; blame names both sites | ✔ | `EAL.bend` (verdicts and layouts byte-identical to haskell-final's) |
| 5 | certification gates every compile path, pre-sizing | ✔ | |
| 5 | `admitIC`: the sized program re-certified as the IC's admission | ≠ | not in master or haskell-final; like haskell-final, the port certifies the sized term only for its layouts and refuses nothing. A strict gate would refuse tictactoe today (`var.budget`, both implementations) |
| 6 | all runtimes interpret one core; parity by tests | ✔ | goldens + `bend/tests` |
| 6 | environments shared, not copied | ✔ | the IC's env splitter tree |
| 6 | iterated pure main; one driver loop | ✔ `a2ee8246` | `Session.start`/`answer`; `Main.session` (stdin) and `Session.replay` (tests) drive it |
| 6 | `--fast`, Fast's discardable aborts | ≠ until P5 | |
| 7 | abstract-algorithm IC, EAL as its soundness condition | ✔ | |
| 7 | code is a pointer into a template table | ✔ `7103aa53` | one template per exactly-equal body (`key.of`: the collected code, nested closures as (template, index)), as haskell-final's hash-then-Eq; the guidance hash (Lift's namespace) is computed per template, and only with guidance |
| 7 | env splitter tree; a test pins envWiring = cgUsage | ✔ `ef94f232` | `ic-usage-agrees` in `bend/tests/ic.bend` (every template and the entry of the three golden programs; a mutated `IC.usage` fails it) |
| 7 | stuckness is a value; eager speculation; guided dup | ✔ | guided erasure isn't in haskell-final either; P4 narrows speculation |
| 8 | content-addressed defers (deferLift) | ✔ | `Lift.bend`; EAL consumes it; DeferMap-native compilation stays DESIGN's [open] destination |
| 9 | `.telc`; staleness and versioning | ≠ until P6 | |
| 9 | two reports, `--certificate` (static) and `--meter` (one run) | ✔ `a2ee8246` | `--meter` prints interactions only; `--ic --certificate` is refused |
| 9 | error taxonomy mirrors the pipeline | ✔ `f2a3247c` | `Main.Failure` (Unread, Refused, Uncertified, Unsized) from one pure `compile`, rendered by `failed`; runtime failures are `IC.Fault` |

The alignment steps that were done:
1. **C3** (`a2ee8246`):
   - one session loop;
   - `--meter`: stderr `IC interactions: N`;
   - `--certificate`: `bend/Levels.bend` (the structural pass as a job
     machine; its string keys sort as Haskell's tuples) and
     `bend/Certificate.bend`;
   - goldens `*.certificate` and `*.ic-meter`, with `test/golden/port/`
     (`run.sh BIN record-port GLOB`; check prefers `port/` over
     `expected/`).
2. **H1:**
   - `37e8d85a`: `Core.bend`;
   - `f2a3247c`: the failure union;
   - `0a171419`: the stage-indexed surface (`S.loc(Empty, Unit, Empty, t)`;
     `Desugar.Arm`; `Lower.NB`);
   - `26bf8332`: `Term.T<V>` (`T.T.loc(V, t)`, `T.ints.i2t(V, …)`).
3. **§7, one template per body** (`7103aa53`). Consuming Lift's DeferMap
   directly was set aside: Lift dedups index-blind, so readback could show
   another site's nested indices.
4. **§7, pin envWiring = usage** (`ef94f232`). One function for both was
   set aside: they read different IRs (`IC.Code`, `Lf.L`).
5. **Docs** (`0c062de5`): the README's "Design" section and stage types.

## 7. Differences by design (port vs haskell-final output)

- `Lexical`: identifier classes are ASCII; Haskell's are Unicode. Every
  program in the repo is ASCII.
- `--meter` prints the interaction count, not haskell-final's storage
  figures (`test/golden/port/*.ic-meter`). The interaction line equals
  haskell-final's on all three goldens.
- `--ic --certificate` (haskell-final's IC space certificate) is refused,
  exit 2. `--certificate` alone gives the static report.
- `--draw-net`, the REPL and the LSP are not ported.
- P4–P7 will add their lines here: counts, the fuel text, the
  certificate's checks section.

## 8. Left open

- These are not in the plan and stay as haskell-final has them:
  - §11.1–2: EAL completeness and gate joins;
  - §11.5: elegance of the recursion form;
  - §11.8: Levels is approximate by design;
  - §11.9: guidance for data;
  - §11.10: the input boundary (but see P7.5);
  - §8: DeferMap-native compilation.
- §11.11, when the multi-runtime arrangement ends: the port has one
  runtime, so for the port it is answered.
- Appendix A analogues, kept for byte-identical output:
  - `__case_*` helper names, with the pruner keeping
    `and`/`listEqual`/`foldl`/`abort` by name (`Desugar.bend`,
    `Resolve.bend:91`);
  - `:N` placeholder names for recursion sites (`Lower.bend` `site.name`);
  - generated locations ("LamBase Cofree instance") on case-lowered nodes.

## 9. Verifying

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
  on purpose: list it in section 7 and re-record only that case, into
  `port/`.
- A full golden pass on haskell-final took ~11.5 min; the port's patterns
  take a few minutes.
- Corpus parity: see section 10.

## 10. Dev tools and the parity corpus (`bend/dev/`, committed for the move)

Build a tool with `bend bend/dev/X.bend -o /tmp/X` (inside `nix develop`),
and run it from the repo root: modules load as `M.tel` from the cwd.

**Compile (`--check-only` passed on 2026-10-01):**
- `icmeter MODULE [LINE…]`: the session's displays, then
  `IC interactions: N`.
- `ealtime MODULE`: for the `cert` and `sized` passes, `bodies N`, then
  `main X ms: vars V sites S pairs P blames B -> ok|<error>` and
  `verdicts Y ms: K certify`.
- `tplcount MODULE`: how many templates the prepared program has.
- `layouts MODULE`: the certification's verdict, then every capture layout
  EAL gives the sized term, one `hash shape` line each. It is a fingerprint
  for comparing builds.
- `bodyerrs MODULE`: every lifted body's standalone verdict on the
  certified term and on the sized one, with the failure text.
- `sites MODULE`: the recursion sites (location and token), and the node
  counts of `cert` and `run` (useful for P3).
- `size MODULE`: sizing's counts, or its failure.
- `lift MODULE`: the deferLift dump of `cert`.
- `lexdump`: tokens.
- `ealonly`: certification only.
- `sha`, `shabench`: SHA-256.

**Stale** (they fail to check since the alignment round changed types;
fix them when needed):

| Tool | First error |
|---|---|
| `phases` (per-phase times: front, certify, size, layouts, prepare, session) | expected `../Core.V` |
| `eal`, `ic1`, `meter` | "expected: a defined name"; `eal`'s `main.only` calls `EAL.main.of`, which no longer exists |
| `ealphase` | expects `Result<…, EAL.St>` |
| `expr` | "write `../Syntax.Surf<..>`" |
| `parsedump` | stage types |
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
  `ratarith`'s is the fuel death at 10,000,000. The port matched all 13.
- `NAME.hs-certificate`: haskell-final `--certificate` output. There are
  14; `ratarith` has none. The port matched all 14 byte for byte.
- To compare:
  ```sh
  cd bend/dev/corpus
  /tmp/bin/telomare casea.tel --meter 2>&1 | diff - casea.hs-ic-meter
  /tmp/bin/telomare casea.tel --certificate | diff - casea.hs-certificate
  ```
  The port's `--meter` puts `IC interactions: N` on stderr after the
  displays, which matches haskell-final's first meter line.

## 11. Layout

- `bend/Everything.bend` imports every module.
- Front end: `Lex`, `Parse` (→ `Syntax`), `Expand`, `Resolve`, `Desugar`,
  `Lower` (→ `Term`), `Split`, and `Front` (loading, both lowerings).
- `Expr` (sizing's IR) and `Size`, which hands on `Core`: the runnable core
  `V`, data `D`, the reserved function indices.
- `Sha256`, `Lift` (deferLift, CapShape), `EAL`.
- `IC`, `Session`, `Main`.
- `Levels` and `Certificate`: the static report.
- `Text`, `Show`, `Loc`.

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

## 12. Bend 2 gotchas

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

## 13. Nix gotchas

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
