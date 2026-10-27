# Telomare
> A simple but robust virtual machine

<p float="left">
  <img src="https://github.com/Stand-in-Language/stand-in-language/actions/workflows/telomare-ci.yml/badge.svg" />
  <a href="https://gitter.im/stand-in-language/Lobby?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge"
     title="Join the chat at https://gitter.im/stand-in-language/Lobby">
    <img src="https://badges.gitter.im/stand-in-language/Lobby.svg" /> 
  </a>
</p>


A virtual machine with a simple grammar evolved from simply typed lambda calculus, that eventually will have powerful static checking and an optimizing backend.

## Warning
This project is in active development. Do expect bugs and general trouble, and please let us know if you run into any by creating a new issue if one does not already exist.

## Status: moving to Bend

Telomare is being rewritten in [Bend 2](https://github.com/bendlang/bend). The
Haskell implementation was removed after the tag `haskell-final`, the last
commit that has it. The port keeps one runtime, the interaction-net runtime
(`--ic`), and runs `--fast` on it too. haskell-final's other runtimes are
not coming back: the reference evaluator behind the plain run, the REPL and
the LSP; the metered evaluator behind `--meter` without `--ic`; and the
Fast interpreter.

The Bend `telomare` command is the flake's default app. It runs a program on
the IC runtime, as haskell-final's `telomare FILE.tel --ic` did (`--ic` is
accepted and changes nothing):

```sh
$ nix run . -- tictactoe.tel
$ nix run . -- tictactoe.tel --certificate   # what is known without running it
$ nix run . -- tictactoe.tel --meter         # run it, then what the run cost
$ nix run . -- tictactoe.tel --fast          # run it unsized
```

As in haskell-final, the program must pass EAL certification before it is
sized (a program that does not certify is refused with the reason, exit 1),
and the EAL capture layouts of the sized program guide the runtime's closure
copying. Both reports of [Resource reporting](#resource-reporting) are
ported: the static report (`--certificate`) as haskell-final prints it, and
`--meter` with the interaction count only (see that section). haskell-final's
other actions are not ported: `--ic --certificate` (the IC space
certificate) and `--draw-net`.
The sections that describe them say so. `test/golden/` records exactly what
haskell-final printed for each example program and mode, and `nix flake
check` runs the command on every case it covers (`test/golden/run.sh BIN_DIR
check [PATTERN...]`). Where the port prints something else on purpose,
`test/golden/port/` holds what it prints instead, beside haskell-final's
record. To run haskell-final itself:

```sh
$ git worktree add ../telomare-haskell-final haskell-final
$ cd ../telomare-haskell-final && nix build --accept-flake-config .#telomare
$ ./result/bin/telomare tictactoe.tel
```

### Speed: Haskell to Bend

The Bend `telomare` prints what haskell-final's `telomare FILE.tel --ic`
prints, through the same stages: EAL certification, sizing, capture layouts
and an interaction net. It does it in a fraction of the time. Wall-clock
times for a whole run, from
reading the program to the session's end, both printing identical output (an
Intel Core i7-1160G7 laptop, 4 cores and 8 threads, 16 GB):

| Program | haskell-final `--ic` | Bend | Speedup |
|---|---:|---:|---:|
| `tc_ultra_minimal.tel` | 0.06 s | 0.02 s | 3× |
| `simpleplus.tel`, input `3 4` | 9.6 s | 0.8 s | 12× |
| `tictactoe.tel`, the test game (`1 9 2 8 3`) | 73.7 s | 2.8 s | 26× |
| a CaseTests program (integer cases) | 36.4 s | 1.7 s | 21× |
| a CaseTests program (property shapes) | 289.9 s | 5.0 s | 58× |
| UDTTests' natural arithmetic | 16.3 s | 1.0 s | 16× |
| NatUDTTests' `Nat` | 61.8 s | 3.0 s | 21× |
| the Prelude's `Rational` | 31.3 s | 0.7 s | 43× |

haskell-final ran the property-shapes program with its heap capped at 8 GB
(`GHCRTS=-M8G`); uncapped, it ran this machine low on memory. tic-tac-toe
took 2.4 s before its input refinements moved to the session boundary (see
[Design](#design)), which adds a second program, the guard, to certify, size
and run.

These times predate the erasure checker (see [Design](#design)), which now
runs as part of sizing. On an AMD Ryzen 7 3700X it adds about 4 s to
`simpleplus.tel`, where it proves the erasures, and about 7 s to
`tictactoe.tel`, where it spends its whole budget and gives up. `--compile`
(below) pays it once.

Most of the difference is in EAL. The Bend analysis keeps its state in flat
arrays of words, as the runtime keeps its net, instead of maps in a state
monad. Its tags are small numbers instead of hashes compared as strings. It
also skips steps that the Haskell repeats with no effect: collapsing a pair
that is already data, and looking again at an apply site whose code has not
changed. And it certifies the term that runs, where haskell-final built and
certified a second one with every let binding inlined (3,054 bodies for
tic-tac-toe, against 176). Every result is identical, and the capture
layouts are byte for byte the same. The interaction net runs only the branch
an `if` chooses (see [Design](#design)), so it runs the tic-tac-toe test game
in 6.0 million interactions instead of 15.2 million, in about 0.7 s.

### Design

[DESIGN.md](DESIGN.md) is the maintainer's design document: Telomare's
commitments (a simple core, totality, resource use as an output of
compilation, one runtime, abort as a static device), the heuristic that each
compiler stage makes the previous stage's forms unrepresentable, and the
decisions that currently serve them. It was written against the Haskell
code, so its module names are haskell-final's.

The port meets the commitments and follows the heuristic and the decisions:
the bounds sizing infers and the cost of a run are both reported (C3); IC is
the one runtime (C4); every stage hands the next a type without the previous
stage's forms (H1, see [Compiler stages](#compiler-stages)); failures are one
union with a case per stage (§9); a closure body is one template however
often it occurs (§7), and a test pins that the IC's environment wiring and
EAL's usage map agree on the code the IC runs (§7). It differs on purpose
in these places:

- `--meter` reports interactions only. haskell-final's IC also printed
  "logical storage" counted on its own map-of-ports net, which the port
  does not share and so cannot report honestly.
- `--draw-net` is not ported.
- `--compile` writes haskell-final's version 4 artifact with no IC
  certificate (the port has none to store), and `--ic --compile` writes the
  same. Its stored report has the checks section below, and a program whose
  session has a guard (below) is written as version 5: version 4 and then
  the guard, which haskell-final refuses by its version rather than run main
  unguarded. haskell-final's artifacts load in the port.
- `--fast` runs on the IC (C4: one runtime), not on a second evaluator.
  Sizing is skipped, and every recursion site becomes a closure that
  rebuilds itself when applied, so each application unrolls one layer;
  only the branch an `if` chooses runs. The displays are haskell-final's.
  What it counts is the IC's: fuel and the meter are interactions, there
  are no application or gate counts, and each unroll counts once
  (haskell-final's Fast forced a recursion value at each projection, twice
  per application, so its unroll counts are double). It runs unguided:
  EAL's capture layouts are the sized program's.
- EAL certifies the term that is sized and run (DESIGN.md §3, §11.4).
  haskell-final certified a second term, built with every let binding
  inlined at each use; the port no longer builds it. Every example
  program certifies as it did, and a missing definition is reported as it
  was.
- The IC runs only the branch an `if` chooses (DESIGN.md §11.3). The core
  keeps one conditional, the strict gate-switch, and sizing and EAL read
  it as before. The IC compiles each branch into a template of its own,
  which the gate picks and runs on the parts of the environment the
  branches use. Evaluating the other branch could change only the cost:
  the core is total for certified programs and an abort is a value, so a
  dead branch's value is projected away. This narrows §7's "eager
  speculation is accepted" to everything but an `if`'s branches. It is
  sound for the same reason the strict net is: the lazy net duplicates no
  more than the strict one does, each captured part going once to the
  chosen branch instead of fanning to both. Displays are unchanged;
  interaction counts are not haskell-final's (the tic-tac-toe test game
  takes 6.0 million instead of 15.2 million), and a program whose dead
  branch never ends now finishes (`ratarith` in the parity corpus gives
  what haskell-final's reference evaluator gives, where its IC ran out of
  fuel).
- Main's input refinements are checked at the session boundary (DESIGN.md
  §11.10's convention, made a rule). These are the refined bindings of the
  `let` that `main = \input -> let ... in body` opens with. On each line it
  reads, the session runs them first, as a program of their own (the
  guard: main with its body replaced by the refined values), and calls main
  only when they pass. A failing one ends the session with its abort, as
  main would have. The opening call, main on 0, is not checked, since 0 is
  no input. Two things differ from haskell-final, where a refinement fired
  only when main used its value: one now fires on every line, even where
  main would not have used it, and an invalid line costs only the guard
  (tic-tac-toe's `10`: 1.0 million interactions instead of 7.6 million).
  `--fast` runs the guard too. Displays of the example programs are
  unchanged.
- `--certificate` also says what sizing proved of each refinement check
  (DESIGN.md §10's split, which haskell-final's report lacks): discharged,
  or left to run time because the session runs it at its boundary, because
  it validates input otherwise, because its abort reaches the result on
  some input, or because it is not proven for every input. Sizing's main
  run assumes the refinements that bound the input pass (its limits pass
  learned the input positions they force), so it explores only input that
  passes them. With the boundary that is every input main is called on,
  once sizing also runs the opening call, and provided each restriction is
  exactly what its check needs (sizing checks that). A program whose input
  is validated anywhere else is proven for nothing. Otherwise the split is
  exactly as sound as sizing's exploration.
- A program proven so runs without what sizing discharged (DESIGN.md §10
  and C5), where the erasure checker proves that too. Main's boundary
  checks and its discharged checks become the values they checked, and
  every chain's bottom becomes 0 instead of an abort. The counts are
  sizing's claim that no input main is called on reaches a bottom (§10:
  the bottom "is provably dead if the certificate is right"). The checker
  (`bend/Check.bend`) does not take sizing's word for it. It runs main's
  sized form, every erasable site still marked, over every input the
  guard passes, splitting the input wherever the run needs to see it, and
  it proves the erasures when no input reaches a marked site. That this
  verdict makes erasing safe is proven (see [What is
  proven](#what-is-proven)). Where the checker cannot decide, because it
  finds an input that reaches one or because it spends its budget first,
  every bottom and check stays a run-time abort, and `--certificate` says
  so. simpleplus is proven: `3 4` takes 42,943 interactions instead of
  782,347, nearly all of the difference being the check no longer run
  inside main. tic-tac-toe is not: the checker gives up, so its main keeps
  its aborts, and the game `1 4 2 5 3` takes 6,016,132 interactions instead
  of 5,927,480 (1.5% more). Elsewhere counts drop a little: 150 to 146 for
  `tc_ultra_minimal`, and 91,147 to 90,345 for the Rational example.
- The checker's budget is work, not runs: 2^28 evaluation steps
  (`check.work` in `bend/Size.bend`), counted over every run it makes.
  simpleplus takes 200,013,887. A budget of runs would let a program whose
  runs are long, like tic-tac-toe's, take minutes to give up (110 s at the
  16,384 runs simpleplus needs); this one gives up in about 7 s. A budget
  never makes an erasure unsafe: it only decides when the checker stops
  and leaves the aborts in.
- Like haskell-final, the port certifies the sized program only for the
  capture layouts that guide the IC; it does not refuse to run a program
  whose sized form fails certification (DESIGN.md's `admitIC` is not in
  master or haskell-final).

Of DESIGN.md's open questions (§11), three are resolved: the certified
term is the executed one (§11.4), the IC runs only an `if`'s chosen branch
(§11.3; both above), and `trace` (§11.7) is removed, since it had no
runtime meaning and restoring it would need a side channel through the IC
(C1/C4). Abort (§10, §11.6) is erased where sizing and the erasure checker
prove it dead. main's
input refinements run at the session boundary (§11.10), in a guard that
keeps them as checks. Abort stays a core form there, in the guard, in the
checks left to run time, and in programs sizing does not prove.

### What is proven

`bend/LAWS.bend` states, in Bend, what makes erasing safe, and
`bend/PROOF.bend` proves it. `bend bend/PROOF.bend` checks the proofs, and
`nix flake check` runs it. The laws read the core through `bend/Sem.bend`,
its meaning in the IC's evaluation order:

- **erasure** and **counts_suffice**: where a run with the erasable sites
  watched answers, no marked site having reached its result, the same run
  with them erased (as the program runs) or unbounded (as `--fast` runs)
  gives the same answer, when it gives one.
- **what_runs**: the program the compiler hands the runtime answers as the
  checker's witness does with its sites erased.
- **certificate_opening** and **certificate_guarded**: where the checker
  says proven, neither the opening call nor a call on any input the guard
  passes reaches an erasable site, at any fuel.
- **fuel_more**: more fuel never changes an answer a run already has.

The checker counts its evaluation steps for its budget with a copy of the
evaluator, which is proven to give the evaluator's results (`semc_sem`),
so its verdict rests on the meaning the laws are about.

What this leaves trusted:

- That the IC computes what `bend/Sem.bend` says. It is tested
  (`bend/tests/sem.bend` runs both on whole sessions), not proven.
- Termination. The laws compare answers where both runs give one; that
  every run of a certified program ends is EAL's promise (DESIGN.md C2,
  §5), and nothing proves it of the checked runs.
- The laws are separate statements, not yet one theorem, and `what_runs`
  is proven in one direction only.
- BendTT's kernel, rather than Bend's checker: `nix flake check`'s
  `bend-proof` rechecks the proofs with the kernel (`bend bend/PROOF.bend
  --verdict`), which has a proof in Lean. The flake builds the kernel with
  Lean 4.34 from its `lean` input, and `nix develop` sets `BENDTT` to it.

[bend/SIZING-PROOF.md](bend/SIZING-PROOF.md) explains the laws, the
checker and the proofs as built.

## Quick Start

1. Clone this repository and change directory to it:
   ```sh
   $ git clone https://github.com/Stand-In-Language/stand-in-language.git
   $ cd stand-in-language
   ```
2. [Install Nix](https://nixos.org/nix/download.html):
   ```sh
   $ curl https://nixos.org/nix/install | sh
   ```
3. Optional (reduces build time by using telomare's cache):
   ```sh
   # Install cachix with nix-env or adding `cachix` to your `/etc/nixos/configuration.nix`'s' `environment.systemPackages` if in NixOS.
   $ cachix use telomare
   $ cachix use ekala-corepkgs
   ```
   The build comes from [ekapkgs](https://github.com/ekala-project/ekapkgs-roadmap)
   rather than nixpkgs: `corepkgs` supplies the base system. The one
   exception is `bend`, which comes from Bend's own flake and brings that
   flake's nixpkgs, so its closure comes from cache.nixos.org. `telomare`
   caches everything this flake builds; `ekala-corepkgs` holds the base
   system. The flake names both caches in its `nixConfig`, so accepting that
   when Nix asks does the same job. (Maintainers fill the `telomare` cache
   with `nix run .#push-cachix`, which publishes the package, its checks and
   apps, and the development shell, and uses the `cachix` and `nix` already
   on your PATH.)
4. Enter a Nix shell. It provides `bend`, pinned by the flake:
   ```sh
   $ nix develop # or nix develop -c zsh
   $ nix develop .#full # the same plus haskell-language-server, hlint, stylish-haskell and ghcid
   ```
   (`nix develop` takes its interactive bash from whatever your flake registry
   calls `nixpkgs`. That is Nix's doing, not this flake's, which has no
   nixpkgs input of its own.)
5. Check the port. Every module under `bend/` is type-checked, checked for
   termination and has its laws proven, and every test under `bend/tests/` is
   compiled to a native binary and run:
   ```sh
   $ bend bend/Everything.bend   # prints ALL PROOFS CHECK
   $ bend bend/PROOF.bend --verdict   # the same, by BendTT's kernel
   $ nix flake check
   ```
6. Profit!

## Resource reporting

Telomare is total because every `{test, recursion, last}` in a program is
compiled into a loop whose iteration count the compiler *infers*, by unrolling
the recursion abstractly over a symbolic input until its test stops. A program
whose counts cannot be found does not compile.

Those counts are worth seeing, so they are reported rather than discarded.
There are exactly two reports: `--certificate`, which says what the compiler
knows without running the program, and `--meter`, which says what one run
actually cost.

```sh
$ telomare test/programs/simpleplus.tel --certificate
static report: what the compiler knows without running the program

recursion sites (iterations, over every input):
  Prelude:30:18 (#0)     <= 11
  Prelude:48:23 (#1)     <= 7
  simpleplus:12:42 (#2)  <= 10
  simpleplus:12:28 (#3)  <= 10

sizing budget in force: 65536 unrollings

refinement checks: 0 discharged statically, 1 left to run time:
  simpleplus:14:31  at the session boundary
erasures in main: proven, by the erasure checker in 200013887 evaluation steps
  no input it is called on reaches an erased recursion bottom or check
erasures in the guard: none; every recursion bottom and check stays a run-time abort
  sizing did not prove the guard for every input

recursion nesting (structural, approximate):
  triple         function             levels
  Prelude:11:17  Prelude.d2c          0, 1
  Prelude:44:32  Prelude.foldr.fixed  0, 1

maximum nesting depth: 2
...
```

The counts assert nothing new: they are the numbers already baked into the
program to make it total, and they hold for every input. The nesting below them
is a separate, structural reading of the source — it evaluates and searches
nothing, so it costs far less than sizing — and it also reports which bindings are used
below the level they were bound at (on `tictactoe.tel`, `whoWon.board : !!`),
which is what duplicating a value across recursion levels costs. The two lists
index differently — a count is per instantiation, a nesting row is per `{test,
recursion, last}` as written — so they do not line up row by row, and the
report says so.

The checks section splits the program's refinement checks as DESIGN.md §10
asks. These are every `x : v = e`, plus Prelude's `abort`, the one check that
`case`, UDT validators and pattern lambdas call. A check is *discharged* when
sizing proved that no input makes its abort reach the result. Otherwise it is
left to run time, and the report says why. simpleplus's `validInput` is a
refinement of main's input, so the session runs it before main on each line
it reads, and main runs without it.

The two `erasures` lines say, for main and for its guard, whether the
program that runs leaves out its recursion bottoms and discharged checks.
It does only when the erasure checker proved that no input reaches them
(see [Design](#design)); otherwise the second line says why they stay.
On `tictactoe.tel` it reads "the erasure checker could not prove them
unreachable: its budget of evaluation steps ran out".

`--meter` runs the program and reports what the run cost: the interactions
the net performed over the whole session, on stderr once the session ends.
That is a measurement of one run, not a prediction about the next:

```sh
$ printf '3 4\n' | telomare test/programs/simpleplus.tel --meter
enter two digits separated by a space
3 plus 4 is 7
IC interactions: 42943
```

The count is the port's own: its net runs only the branch an `if` chooses,
where haskell-final's built both, and main runs without the input check the
session ran before it, so it is far lower than haskell-final's `--ic
--meter` count (1517868 for this run; see [Design](#design)). It is
not a memory figure, deliberately. haskell-final's IC also
printed the peaks of its net's "logical storage" (agents, port entries,
pending pairs), but those counted its own representation of the net (a map of
ports, stale entries included), which the port does not share, so it does
not print them; no figure is reported that the port cannot measure honestly.
(haskell-final's reference evaluator, which `--meter` without `--ic` used,
counted steps and term nodes instead; it is not ported.)

When sizing fails, the error names the recursion, where it is, and which of the
two failures it is — a budget that was too small, or an input that nothing
bounds. Only the first is fixable by raising the budget. See
`test/programs/limits/` for a worked example of each.

## Compiling once

Certifying and sizing are the slow part (about 70 seconds for `tictactoe.tel`
in haskell-final, about 8 s here, most of it the erasure checker giving up),
and they give the same answer every time,
because sizing runs the program over a *symbolic* input. So they need only
happen once:

```sh
$ telomare tictactoe.tel --compile      # writes tictactoe.telc
$ telomare tictactoe.telc               # starts at once
```

A `.telc` file holds the sized program together with its counts, its
certificate and the capture layouts it runs under, so running it skips
parsing, certifying, resolving and sizing,
and `--certificate` on it prints instantly. If the sources are still around and
have changed since it was built, running it says so and carries on — an
artifact is expected to outlive the checkout it came from.

## Running without sizing

`--fast` skips sizing altogether and runs the recursion on demand, unrolling
one layer per call instead of a count inferred in advance. It runs on the
interaction net like everything else, plays `tictactoe.tel` identically, and
will even run programs the sizing pass rejects:

```sh
$ printf '3 4\n' | telomare test/programs/simpleplus.tel --fast --meter
enter two digits separated by a space
3 plus 4 is 7
IC interactions: 735924
recursion unrolls (measured):     55 across 4 sites

  site   source            function          unrolls
  #1     Prelude:48:23     Prelude.foldr     24
  #0     Prelude:30:18     Prelude.dMinus    20
  #2     simpleplus:12:42  simpleplus.doAdd  6
  #3     simpleplus:12:28  simpleplus.doAdd  5
```

Per-site unrolls are only available this way: sizing compiles each site into a
loop of a fixed length, after which the site no longer exists to attribute
anything to. They are totals over the run rather than depths, so they are not
the same measurement as the certificate's per-instantiation counts.

What `--fast` gives up is the thing sizing is for: **nothing proves the program
terminates**. A recursion that would not have sized runs until a fuel cap stops
it (default 16777216 interactions per iteration of `main`, `--fuel N` to change
it, `--fuel 0` to lift it). That is why it is a flag and why sizing remains the
default. `--fast --certificate` prints the static report with no counts.

## Telomare REPL

haskell-final ships `telomare-repl` (`result/bin/telomare-repl`, run beside
`Prelude.tel`). The Bend port brings it back on the IC runtime, after the
`telomare` command.

## Editor Support (LSP)

haskell-final ships a language server (`telomare-lsp`); the Emacs major mode
under [`emacs-telomare-mode/`](emacs-telomare-mode/), with variants for
Spacemacs, Doom, and vanilla Emacs, is still here. The flake has no `lsp` app
until the port brings the server back, so the setup below needs a
haskell-final checkout for now.

### LSP capabilities

The language server provides:

- **Diagnostics** — on every document open and edit it reports parse
  errors, missing imported modules, undefined variable references, and
  resolver errors. Diagnostics are cleared when the document is closed.
- **Go to definition** — jumps to local `let`, lambda, and case-pattern
  binders, to top-level definitions, and to definitions in qualified
  imported modules.
- **Find references** — lists every reference to a symbol, optionally
  including its declaration.
- **Semantic-token highlighting** — keywords, comments, strings,
  numbers, and operators, for the whole file or a requested range.
- **Code action** — *Partially evaluate*: select an expression and the
  server evaluates it, reporting the result in an editor popup.
- **Workspace commands**:
  - `telomare.version` — reports the server version as a UTC timestamp.
  - `telomare.partialEval` — evaluates a given expression; this backs
    the partial-evaluation code action.

Document sync is full-text (whole-document). Hover and rename are not
implemented yet.

### Installing the Emacs mode

The recommended Spacemacs setup is to load Telomare's Emacs mode from the
same Telomare flake input that provides the language server. Do not point
Spacemacs at a random checkout unless you are actively developing the mode;
make the editor use the same pinned source that NixOS or Home Manager builds.

For a NixOS/Home Manager Spacemacs config, add Telomare as a flake input and
load the mode file from that input:

```elisp
(load "${telomare}/emacs-telomare-mode/telomare-mode-spacemacs.el")
```

The mode auto-detects the surrounding flake source path and starts the LSP with
`nix run path:<telomare-source>#lsp --`. This matters for Nix store paths:
`nix run /nix/store/...-source#lsp --` is parsed incorrectly by Nix, while
`nix run path:/nix/store/...-source#lsp --` is the intended absolute-path flake
form.

For a manual checkout-based setup, load the mode from this repository and set
`TELOMARE_ROOT` only if auto-detection cannot find `flake.nix`:

```elisp
(load "/path/to/telomare/emacs-telomare-mode/telomare-mode-spacemacs.el")
```

For Doom and vanilla Emacs setup, see
[`emacs-telomare-mode/README.md`](emacs-telomare-mode/README.md).

### Keybindings

The mode binds only features the server implements. Some entries below
come from `lsp-mode` rather than Telomare's mode — these are marked
*(lsp-mode)*. Spacemacs exposes the major-mode leader as `SPC m` in Evil
state and as `M-m m` in holy-mode; the leader entries are otherwise the
same bindings.

**Spacemacs — Evil mode** (`SPC m` major-mode leader):

| Key | Action |
|-----|--------|
| `SPC m g` | Go to definition |
| `SPC m G` | Find references |
| `SPC m a` | Execute code action (partial evaluation) |
| `SPC m v` | Show Telomare LSP version |
| `C-c C-v` | Show Telomare LSP version |
| `g d` | Go to definition *(lsp-mode / Evil default)* |

**Spacemacs — holy mode** (`M-m m` major-mode leader):

| Key | Action |
|-----|--------|
| `M-m m g` | Go to definition |
| `M-m m G` | Find references |
| `M-m m a` | Execute code action (partial evaluation) |
| `M-m m v` | Show Telomare LSP version |
| `C-c C-v` | Show Telomare LSP version |
| `M-.` | Go to definition *(lsp-mode)* |
| `M-?` | Find references *(lsp-mode)* |
| `M-,` | Jump back *(xref)* |

Vanilla Emacs binds `M-.`, `M-?`, `C-c a`, and `C-c C-v`.

### Troubleshooting

If navigation does not work, check the active LSP session with
`M-x lsp-describe-session`, restart it with `M-x lsp-workspace-restart`, and
confirm the server command with:

```elisp
M-: (telomare--lsp-command)
```

The expected command shape is:

```elisp
("nix" "run" "path:/nix/store/...-source#lsp" "--")
```

### LSP version command

`C-c C-v` (or `SPC m v` / `M-m m v` in Spacemacs) reports the server
version as a UTC timestamp truncated to minutes, using the parent commit
timestamp when git history is available and the flake source timestamp
when launched from a Nix store source without `.git`. It can also be
invoked directly:

```elisp
(lsp-request "workspace/executeCommand"
             `(:command "telomare.version" :arguments []))
```

The command shows an editor message such as:

```text
Telomare LSP version: 2026-05-22T10:14Z
```

## Git Hooks

You can set up git to check every Bend module before each commit (`bend
bend/Everything.bend --check-only`, the check `nix flake check` runs). Just run:

``` sh
$ git config core.hooksPath hooks
```

## Surface Syntax

Telomare source is a small expression grammar. Applications associate to the
left, definitions in the same `let` or module are mutually visible, and
continuation lines must remain indented under the expression they continue.

```text
module      ::= (import | definition)*
import      ::= "import" module-name
              | "import" "qualified" module-name "as" identifier
definition  ::= identifier (":" expression)? "=" expression
              | "[" identifier ("," identifier)* "]" "=" expression
expression  ::= "let" definition* "in" expression
              | "if" expression "then" expression "else" expression
              | "\\" pattern+ "->" expression
              | "case" expression "of" alternative+
              | atom+
alternative ::= pattern "->" expression
atom        ::= identifier | natural | string | "$" natural | "#" atom
              | "(" expression ")" | "(" expression "," expression ")"
              | "[" (expression ("," expression)*)? "]"
              | "{" expression "," expression "," expression "}"
pattern     ::= identifier | "_" | natural | string
              | "(" pattern "," pattern ")"
              | "(" pattern ":" expression ")"
identifier ::= letter (letter | digit | "_" | ".")*
```

The keywords are `let`, `in`, `if`, `then`, `else`, `case`, `of`, `import`,
`qualified`, and `as`. Naturals must fit in the implementation's `Int` range;
oversized literals are parse errors rather than wrapping.

UDTs deliberately retain the existing list-definition convention:

```telomare
[T, constructor, extractor, operation] = \h ->
  [ constructorBody, extractorBody, operationBody ]
```

Expansion recognizes this only when the first name starts uppercase and the body
is a lambda. There must be exactly one more name than body slots: the extra
name is the generated validator. This classification is not parser behavior.

| Source form | Parsed representation | Immediate expansion result |
| --- | --- | --- |
| `\p1 p2 -> e` | `LamPatF` | nested `LamF`, with cases for patterns |
| `let defs in e` | `LetSugarF` | `LetUPF` |
| `x : T = e` | annotated `SingleDefF` | `CheckF T e` |
| `[a, b] = e` | `ListDefF` | one binding per name |
| `[T, ...] = \h -> [...]` | `ListDefF` | UDT bindings and validator |
| `import ...` | `ModuleImportItem ImportDecl` | `ExpandedModuleImport ImportDecl` |
| `case e of ...` | `CaseUPF` | lowered later by `Telomare.Desugar` |

## Compiler stages

The port follows haskell-final's stages, bottom-up, under `bend/`. Each stage
is checked against the haskell-final tests it can answer and against the
goldens in `test/golden/`.

| Stage | haskell-final modules | Status |
| --- | --- | --- |
| Lexical facts | `Telomare.Lexical` | ported: `bend/Lexical.bend` |
| Parse | `Telomare.IR.*` (surface), `Telomare.Parse`, `Telomare.Expand`, `Telomare.Desugar` | ported: `bend/{Loc,Syntax,Lex,Parse,Expand,Desugar}.bend` |
| Resolve | `Telomare.Resolve` | ported: `bend/{Resolve,Term,Lower,Split,Front}.bend` |
| Size (totality) | `Telomare.Size`, `Telomare.Size.IR`, the parts of `Telomare.Machine` sizing uses | ported: `bend/{Expr,Size}.bend`, handing on `bend/Core.bend`'s CompiledExpr |
| Certify | `Telomare.EAL`, the lifting and hashing in `Telomare.Resolve` | ported: `bend/{Sha256,Lift,EAL}.bend` (the verdict and the capture layouts; the per-Defer bangs and levels of the REPL's `:t` are not) |
| IC runtime | `Telomare.IC` | ported: `bend/IC.bend`, closure copying guided by the EAL capture layouts |
| Drive | `Telomare.Driver`, the `telomare` command | ported for running programs, `--meter` and `--fast`: `bend/{Session,Meter,Main}.bend` |
| Static report | `Telomare.Levels`, `Telomare.Certificate` | ported: `bend/{Levels,Certificate}.bend` |
| IC storage bounds | `Telomare.IC.*`, `Telomare.SpaceBound` | not ported |
| Artifacts | `Telomare.Artifact` | ported: `bend/Telc.bend` (version 4, written with no IC certificate; version 5 with a session guard) |
| REPL and LSP | `app/Repl.hs`, `app/LSP.hs` | not ported |

Not ported: `Telomare.Eval.Reference`, `Telomare.Eval.Meter` and the
evaluator of `Telomare.Fast` (`--fast` runs on the IC; its unbounded
recursion is `Expr.limit`).

Each stage hands the next a type in which the previous stage's forms cannot
be written (DESIGN.md's H1): the surface term `Syntax.Surf` is indexed by
stage (`Parsed`, `Expanded`, `Desugared`, `Lowering`; a stage's eliminated
constructors carry a witness of type `Empty`); `Term.T` is over names
(Term1) or de Bruijn indices (Term2); `Term.C` is Term3; and sizing hands
the IC `Core.V`, the runnable core, whose input and state are `Core.D`
data. The IC's own collected code (`IC.Code`) has closures as template
references.

`bend/Lexical.bend` holds the lexical facts of the language (the reserved
words, the identifier character classes, the comment delimiters), so that the
parser and the language server cannot disagree about them.

## Contributing
If you'd like to contribute, please fork the repository and use a feature branch. Pull requests are warmly welcome.

## Links
1. [A Better Model of Computation](http://sfultong.blogspot.com/2016/12/a-better-model-of-computation.html?m=1) by Sfultong
2. [SIL: Explorations in non-Turing Completeness](http://sfultong.blogspot.com/2017/09/sil-explorations-in-non-turing.html?m=1) by Sfultong
3. [Deconstructing Lambdas, Closures and Application](http://sfultong.blogspot.com/2018/04/deconstructing-lambdas-closures-and.html?m=1) by Sfultong
4. [Join the community's chat](https://gitter.im/stand-in-language/Lobby)


## Licensing
The code in this project is licensed under the Apache License 2.0. For more information, please refer to the [LICENSE file](https://github.com/Stand-In-Language/stand-in-language/blob/master/LICENSE).

## IC logical storage (haskell-final)

This section describes haskell-final. The port's `--meter` reports the
interaction count alone, and `--ic --certificate`, `--compile` and
`--draw-net` are not ported.

`--ic` runs a sized source program or `.telc` artifact on the interaction-net
runtime (`Telomare.IC`) instead of the reference evaluator. The rules and
the LIFO scheduling are those of the runtime's own evaluator, unchanged in
behavior; `--ic` adds storage counters and a prepare-once entry around them.
Preparation is guided by the EAL capture
layouts of the sized program (`Telomare.EAL.ealCaptureLayouts`), the
duplication strategy the runtime was designed around; where the EAL pass has
no layout for a body, that body copies generically.

```sh
telomare test/programs/simpleplus.tel --ic                # run on the net
telomare test/programs/simpleplus.tel --ic --meter        # plus peaks and interactions
telomare test/programs/simpleplus.tel --ic --certificate  # bound or estimate, any input
telomare test/programs/simpleplus.tel --ic --compile -o /tmp/sp.telc
telomare /tmp/sp.telc --ic --certificate                  # the stored certificate
telomare test/programs/simpleplus.tel --ic --draw-net     # net and templates, as SVG
```

`--ic --draw-net` draws the prepared program as an SVG figure
(`simpleplus.net.svg`, or `-o FILE`) in the visual language of
[interaction-nets.html](interaction-nets.html): one circle per agent, a
filled dot on its principal port, and principal-to-principal wires — the
active pairs, where rules fire — in the hot color. The first panel is the
entry net, the net a run starts from just before the input is plugged into
its boundary (boundary wires drawn hot become active then). That net is the
same small scaffolding for every program, because a program's code lives in
templates spliced in only when instantiated, so the panels after it draw
those templates, breadth-first from `main`, until `--draw-limit` agents
(default 400) are spent; larger templates are listed with their size
instead. An artifact draws the same program it runs.

`--ic --meter` reports interactions and the peaks of three logical
resources: resident agents, stored port entries and pending pairs (stale
entries count). Templates are reported separately as static storage.
Preparation, compiler workspace, readback, the Haskell heap, GC and RSS are
outside the model.

### Reading a certificate

`--ic --certificate` states what is known about an `--ic` run's storage on
**any** finite Zero/Pair input — not a measurement of one run. When the net
walk finishes, that is a bound, printed as an *IC space certificate*; when it
gives up, an estimate, printed as an *IC space estimate*. The first line says
which, and the document is written to be read on its own.
`tc_ultra_minimal.tel --ic --certificate` in full:

```
IC space certificate

  What this bounds: run this program on the interaction-net runtime
  (--ic) on any finite Zero/Pair input, and the net's logical storage
  stays within the figures below. |input| is the number of constructor
  cells (Zero and Pair nodes) of that input.

  How it was computed: a net walk. The analysis replayed the runtime's own
  rules over a symbolic input, splitting wherever control depends on the
  input's shape, and kept the worst peak over every split, plus a fixed
  allowance for each unknown part of the input. Where the walk finishes,
  as it did here, the figures are usually close to the real peak.

  Peak storage of one evaluation (a session of several evaluations
  peaks at the largest of them):

    agents         ≤ 36·|input| + 1130
    port entries   ≤ 108·|input| + 2894
    pending pairs  ≤ 36·|input| + 647

  Agents are the nodes resident in the net, port entries the wire
  endpoints it stores (stale ones included), and pending pairs the
  interactions waiting on the worklist.

  The figures above fold every part of the input into the whole;
  by part, where |input.left| counts only the cells of the input's
  left subtree and input.left×63 folds 63 left steps, the analysis
  established the tighter:

    agents, the largest of 6 cases:
      4·|input| + 559
      4·|input.left| + 4·|input.right| + 505
      4·|input.left.left| + 4·|input.left.right| + 503
      12·|input.left.left| + 1130
      12·|input.left.left| + 4·|input.left.left.left| + 4·|input.left.left.right| + 834
      36·|input.left.left| + 535
    port entries, the largest of 6 cases:
      ⋮
    pending pairs, the largest of 6 cases:
      ⋮

  Not counted: preparation workspace, readback of the result, Haskell
  runtime overhead, GC and process memory.
```

Top to bottom:

- **What this bounds** states the claim: the figures cover every
  finite Zero/Pair input, expressed in that input's size. `|input|` is a
  count of constructor cells, so the pair `(0, (0,0))` has `|input| = 5`
  (three Zeros, two Pairs).
- **How it was computed** names the analysis, because the two read
  differently. A *net walk* (`Telomare.IC.Space`) replays the runtime's own
  rules in the runtime's own order over a symbolic input, splitting where a
  branch tests the input's shape, and adds a fixed allowance for each
  unknown part of the input. Where it finishes, its figures are usually
  close to the real peak: on `tc_ultra_minimal` the tightest case sits just
  above the measured 559 agents, while on `simpleplus` the constant alone is
  1.6× the measured peak. A program whose control depends on many
  independent input parts exhausts the walk's budget, and the command falls
  back to the *compositional estimate* described below.
- **The headline figures** give one bound per resource as a plain function
  of `|input|`: run the program on an input of 100 cells and the net never
  holds more than 36·100 + 1130 = 4730 agents. The three resources are the
  net's whole logical footprint: its nodes (agents), the wire endpoints it
  stores (port entries), and the interactions queued but not yet fired
  (pending pairs).
- **The by-part refinement** is the same bound before parts of the input
  were folded into the whole; it is tighter when only some parts matter.
  `|input.left.left|` counts only the cells two lefts down, and a deep
  position folds repeated steps: `input.left×63` is 63 lefts down. Each
  resource's bound is the largest of a few cases because different input
  shapes take different branches; every case is itself a bound.
- **Not counted** delimits the model: the bound is about the net's logical
  storage, not the Haskell process around it.

A program the walk cannot finish gets an estimate instead.
`tictactoe.tel --ic --certificate`:

```
IC space estimate

  What this estimates: the net's logical storage when this program runs
  on the interaction-net runtime (--ic) on any finite Zero/Pair input.
  The figures are an estimate, not a guarantee (see below). |input| is
  the number of constructor cells (Zero and Pair nodes) of that input.

  How it was computed: compositionally. The walk of the runtime's own
  rules did not finish here (IC transition budget exhausted).
  These figures instead charge every allocation the program's templates
  allow, in any order of firing, times an estimated multiplier for
  copying. Figures like these exist for every program, but they are
  loose — often by many orders of magnitude — and not a proven bound:
  the copy multiplier can undercount programs that copy code heavily,
  such as towers of Church numerals. Read them as an order-of-growth
  estimate, not as a guarantee or a prediction of the actual peak.

  Estimated peak storage of one evaluation (a session of several
  evaluations peaks at the largest of them):

    agents         ≤ 4.78×10^11·|input| + 1.57×10^534
    port entries   ≤ 1.44×10^12·|input| + 4.08×10^534
    pending pairs  ≤ 1.44×10^12·|input| + 4.08×10^534

  ⋮

  Figures over six digits are shown rounded up to three significant
  figures; rounding up never shows less than the analysis computed.
```

The compositional estimate (`Telomare.IC.Static`) never runs anything: it
charges each counter's lifetime increments from the template table, the
reference graph and the EAL guidance, times an estimated copy multiplier
(1 + 3F)^L for F duplication fans and EAL box depth L. It does not depend on
firing order and exists for every program that prepares, but it is not a
proven bound. The multiplier grows single-exponentially in L, where
elementary affine logic allows a tower of exponentials of height L, and on
a hand-built Church-numeral tower of height five it reports about 9×10^11
agents for a result of 2^65536 cells. For tic-tac-toe it sits some 530
orders of magnitude above a measured game's 265,483 agents. Making it sound,
and tighter, is the main open work. Large figures are rounded *up*, so
rounding never shows less than the analysis computed.

The output is the walk's bound when the walk finishes, else the
compositional estimate, labeled as such. `--ic --compile` stores it and the
capture layouts in the artifact (format version 4; artifacts from older
builds are rejected with a message), and an `--ic` run of the artifact
prepares under those stored layouts, so the stored figures describe exactly
the runs the artifact performs.

Measurements are in [bench/README.md](bench/README.md); the design and the
soundness arguments are in the module documentation of `Telomare.IC.Space`
(the walk) and `Telomare.IC.Static` (the compositional estimate). For the
concepts from first principles — what an interaction net is, what an agent
is, how the node map stores the graph, and where the two analyses' figures
come from —
open [interaction-nets.html](interaction-nets.html) in a browser: an
illustrated primer with worked diagrams.
