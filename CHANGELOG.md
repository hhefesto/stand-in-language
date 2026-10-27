# Revision history for telomare

## Unreleased

* Telomare is being ported to Bend 2. The Haskell implementation was
  removed after the tag `haskell-final`: the library, the `telomare`,
  `telomare-repl` and `telomare-lsp` executables, the test suites, the
  benches, `telomare.cabal` and the Haskell tooling (hlint, stylish-haskell,
  HLS, the `format`/`format-lint`/`lsp`/`repl` apps, the haddock release job).
  What haskell-final printed for each example program and mode is recorded in
  `test/golden/` (`run.sh record|check`), and the port is checked against it.
  The port keeps the interaction-net runtime only; the reference evaluator,
  the non-IC `--meter` and `--fast` are not ported.
* The flake builds Bend instead of Haskell: `bend` comes from
  `github:bendlang/bend`, the rest still from corepkgs (`haskell-pkgs` left
  the lock). `nix flake check` checks every module under `bend/` and runs
  `bend/tests/` as native binaries; the pre-commit hook runs the same module
  check. `bend/Lexical.bend` is the first ported module.
* `telomare` is the flake's default package and app again, now
  `bend/Main.bend` compiled to a native binary: it opens the program it is
  given and reports that the port cannot compile it yet. `nix flake check`
  builds it.
* The Bend `telomare` runs programs: `telomare FILE.tel [--ic]` parses,
  resolves and sizes the program in Bend and runs it on the IC runtime
  (`bend/IC.bend`), printing each display and reading a line of input
  between iterations, as haskell-final's `--ic` run did; `tictactoe.tel`
  plays. haskell-final's other flags are refused with a note. The new
  `goldens` check in `nix flake check` runs the command on every golden
  case it covers, and `test/golden/run.sh` takes several patterns.
* The Bend `telomare` certifies programs with EAL before running them, as
  haskell-final did: a program that does not certify is refused with
  haskell-final's message. The EAL capture layouts of the sized program guide
  the IC runtime's closure copying, so interaction counts match
  haskell-final's `--ic --meter` (`bend/{Sha256,Lift,EAL}.bend`,
  `bend/tests/eal.bend`).
* The Bend `telomare` takes the whole language: `case` expressions (and
  the pattern lambdas that expand to them) are lowered to nested ifs as
  haskell-final did, and `#` (which user-defined types use for their tags)
  becomes the same number haskell-final computed, the SHA-256 of the
  term's Haskell `show`. Case programs, the Prelude's `Rational`, a user
  `Nat` type and a qualified import give haskell-final's output and
  interaction counts.
* The Bend `telomare` erases a program's recursion bottoms and discharged
  checks only where the erasure checker (`bend/Check.bend`) proves that no
  input reaches them, and `bend/PROOF.bend` proves that its verdict makes
  erasing safe. Sizing runs the checker on main and on its guard, within a
  budget of 2^28 evaluation steps; where it cannot decide, the aborts stay.
  `--certificate` has two new lines saying which erasures are proven, and
  why the others stay. simpleplus is proven; tic-tac-toe is not, so its main
  keeps its aborts (the game `1 4 2 5 3` takes 6,016,132 interactions
  instead of 5,927,480), and sizing it takes about 7 s longer.
* EAL certification now terminates by construction in every phase: each
  DeferRef occurrence instantiates its body once (let-polymorphism over the
  DeferMap DAG) and carries the instance's interface with its tag, so dispatch
  only unifies and is bounded by sites times tags. The dispatch depth cap,
  polyvariance cap and variable budget are gone. Self-application is rejected
  as a cycle through an interface's argument half (the occurs check of arrow
  types), with the cycle named in the error; cycles through captures remain
  regular closure shapes. An abort that really aborts now has a bottom type
  instead of being read as the identity, so sized recursion chains type
  through their dead base. Numeral-of-numeral composition and the previously
  pinned same-arity gate join certify.
* The box constraints are solved exactly (presolve, sparse Gaussian elimination,
  exact dual simplex from the slack basis); the level cap, the round budgets and
  `EALSolverGaveUp` are gone, and an unsatisfiable system names the rows that
  cannot hold together. The objective is total leaf depth. Depths are cumulative
  per node, so equations have at most three terms.
* A closed data tree under a pair constructor is one data leaf in the analysis
  (one level of pair structure kept), not a node per pair: data is level-free,
  and the per-component view bangs were what every instance copied.
* The box constraints are solved once, in the global pass, and per-body levels
  and env bangs are read off it. The standalone per-body passes run only when
  main fails, to localize the failure: a certified main has certified every
  body's instances, and a body's own constraints are a subset of its
  instance's, so no body can fail on its own under a certified main. The
  forced identity reading of an unresolved abort could previously fail a body
  standalone and reject main through the dependency gate even though main's
  own derivation certified; that false rejection is gone with the gate.
* The box discipline is faithful EAL: occurrences sit exactly as deep as the
  bangs they open, boxes pass through applications, projections and gate
  switches instead of vanishing, a duplicated capture is contracted outside
  its closure's box (the reading that types Church numerals), and data stays
  level-free. Reported levels are now proof-net depths.
* Reorganized the library into compiler-stage modules: `Telomare.Parse`,
  `Telomare.Expand`, `Telomare.Desugar`, `Telomare.Resolve`,
  `Telomare.TypeCheck`, `Telomare.Size` (+ `.IR`) with the shared
  `Telomare.Machine` step algebra, `Telomare.Eval.Reference` /
  `Telomare.Eval.Meter`, and `Telomare.Driver`. The IR vocabulary moved
  to `Telomare.IR.*` and the error types to `Telomare.Error`.
* Parser APIs now expose an explicit parse-then-expand pipeline. Each surface
  phase has its own term type: the parser produces `ParsedSurfaceTerm` (base
  functor `ParsedTermF` = `UnprocessedParsedTermF` plus the `SugarTermF`
  fragment), and `Telomare.Expand` removes the sugar fragment, returning
  `ExpandedSurfaceTerm` — so expanded trees structurally cannot contain raw
  sugar forms. `Telomare.Desugar` then returns `DesugaredSurfaceTerm`, whose
  case capability is uninhabited, and only that type enters name resolution.
  Module syntax uses `ModuleItem`/`ImportDecl`; expansion retains imports as
  typed `ExpandedModuleItem` values instead of encoding them as arbitrary
  terms. Complete expression runners reject trailing input. The old
  parse-time expansion APIs and `Telomare.Parse.Sugar` module were removed.
* Fixed parser and elaboration correctness issues around oversized naturals,
  keyword boundaries, empty list definitions, generated-pattern capture, UDT
  arity truncation, import failures/cycles, and shadowed builtin rewrites.
* Removed dead code: the unbuildable benchmarks, the C serializer FFI
  (`cbits/`, `ctest/`), the commented-out HVM/LLVM/Chez backends,
  `Telomare.Decompiler`, and orphaned fixture files.
* Removed the `telomare-evaluare` executable and its flake app; its
  interactive evaluation functionality lives in the LSP app now.
* Fixed every GHC `-Wall` warning across the library, executables, and test
  suites (unused imports, name shadowing, incomplete patterns, missing
  signatures, orphan instances, type defaults), and enabled `-Wall`
  permanently for every component in `telomare.cabal`. Orphan instances moved to
  their proper homes: `MonadFail (Either ResolverError)` to `Telomare.Error`,
  `TelomareLike CompiledExpr` to `Telomare.IR.Core`, and the
  `PrettyPrintable` `Char`/`FunctionIndex` instances to
  `Telomare.PrettyPrint`.
* Removed a further ~1,100 lines of dead code across the library, the
  executables and the test suites, including the unused `super*`/`indexed*`
  step family in `Telomare.Machine` and test scaffolding reachable from nothing
  live. Every component now also carries `-Wunused-packages`, and the
  build is warning-free under it.
* Consolidated duplicated logic behind shared abstractions: `Telomare.Util`
  (one `debugTrace`, `padRight` and `plural` where there were six, four and
  two), `Telomare.Lexical` (reserved words, identifier character classes and
  comment delimiters, now read by both the parser and the language server),
  `traverseScoped` in `Telomare.IR.Surface` (one binding-aware traversal of the
  surface functor replacing five hand-written scope walks), and `purely` in
  `Telomare.Machine` (the pure step functions are derived from the monadic ones
  rather than written out a second time).
* Fixed three drifts between the language server's lexer and the parser, all of
  which came from the lexer restating parser facts: `where` was highlighted as
  a keyword though the language does not reserve it, identifiers could only
  start with an ASCII letter, and `{- -}` block comments were never lexed.
* Added `test/ConformanceTests.hs`, a corpus-driven check that the sized
  evaluator, the step meter and the fast runtime agree on the programs they can
  all run.
* Fixed `topologicalSort` in `Telomare.Resolve`, which existed twice with the
  two copies returning opposite orders.
* Fixed the nix build, which had stopped compiling the test suites: it builds
  from `cabal sdist` output, and the Telomare programs the tests read at run
  time were no longer declared in `telomare.cabal`.
* Fixed `nix run .#push-cachix`, which aborted before pushing anything: it named
  the shell apps' closures by evaluating `apps.<system>.<name>.program`, which
  computes a store path without building it, and `nix path-info` rejects a path
  that does not exist. The apps are now build inputs of the script.
* Moved to GHC 9.10.3 and `cabal-version` 3.12, and updated every flake input.
* Moved the Nix build from nixpkgs + flake-parts + haskell-flake to the
  ekala package ecosystem (ekapkgs): `corepkgs` for the base system and the
  GHC 9.10.3 bindist (added upstream for this, corepkgs#178 and #180), plus
  the `haskell-pkgs` snapshot (Stackage LTS 24), consumed with
  `corepkgs.lib.mkFlake`. The Nix code lives in `nix/`; the package
  expression is a checked-in cabal2nix file (`nix/telomare-cabal2nix.nix`),
  regenerated from `telomare.cabal` by `nix run .#cabal2nix` with the
  snapshot's cabal2nix; the `cabal2nix` workflow runs it on every push that
  can change the file and appends the result to the branch as a commit (set
  a `CABAL2NIX_TOKEN` secret for that commit to run CI like any push; without
  one, the workflow starts Telomare CI on the branch itself); `default.nix`
  and `shell.nix` read the pins from `flake.lock` instead of going through
  flake-compat, and are no longer built or cached by `push-cachix`.
  `apps.telomare-lsp` now carries the version stamp like `apps.lsp`. The
  default dev shell is the minimum that builds the project (GHC and
  cabal-install); `nix develop .#full` adds haskell-language-server, hlint,
  stylish-haskell and ghcid; both export `name`, which corepkgs' structured
  attributes leave unexported, so direnv hands it to prompts that show the
  environment's name (haskell-language-server needs its closure in
  one Cabal-syntax 3.14 scope; `nix/haskell.nix` carries that override until
  ekala-project/haskell-pkgs#4 or its corepkgs equivalent lands), and hoogle
  is no longer built for either. `nix run .#push-cachix` publishes every
  declared development shell with its environment closure, every check and
  every app, and uses the cachix and nix on PATH (the snapshot's cachix does
  not build, its amazonka 2.0 predates GHC 9.8, and corepkgs' Nix is a
  from-source build); it keeps what it builds rooted until the push is over,
  since Determinate Nix collects garbage on its own when the disk runs low;
  `nix flake check` builds and shellchecks it. No check
  depends on the LSP version stamp any more, so CI, which builds a pull
  request's merge commit rather than the pushed one, finds every check in
  the cache instead of rebuilding the LSP wrapper, the helper and
  ShellCheck. `systems` is `x86_64-linux` until corepkgs marks
  aarch64-linux supported.
* CI installs Determinate Nix 3.23.3, the Nix `push-cachix` is run with,
  instead of Nix 2.31.5: `nix develop` builds its environment from the
  running Nix's own get-env.sh, so only the same version finds it in the
  cache. Bump the pin, in both workflows, with the maintainer's Nix.
  magic-nix-cache is gone:
  every upload was failing, and Cachix holds everything CI needs.
* CI pushes what it builds to the `telomare` cache. The cache signs with
  a Cachix-managed key, which takes an auth token to push to, and CI was
  offering only a signing key: every upload was refused (403), so nothing CI
  built reached the cache. It now pushes with the `CACHIX_AUTH_TOKEN` secret.
* Fixed `cabal test` in the dev shells, which found none of the test suites'
  own dependencies (hspec, tasty-hunit, tasty-quickcheck): corepkgs' Haskell
  builder defaults to `doCheck = false`, and `shellFor` gathers the
  dependencies through a package built with that default. CI now dry-runs
  `cabal test` in `nix develop` with no package index, so the plan has to
  come from the shell alone.
* haskell-language-server loads every Haskell file again: `hie.yaml` maps
  the EAL, IC and conformance test modules to their suites, and `Common`,
  which `telomare-test` still listed although only the resolver suite
  imports it, belongs to that suite alone (a file in two components fails
  to load in one of them).
* `nix flake check` runs `bend-proof`: BendTT's kernel rechecks the proofs
  that sizing's erasures are sound (`bend bend/PROOF.bend --verdict`), so
  they rest on the kernel's Lean proof rather than on Bend's checker. The
  kernel (`packages.bendtt`) is built with Lean 4.34 from a new `lean` input
  (Bend's nixpkgs has Lean 4.30, which cannot build it), and `nix develop`
  sets `BENDTT` to it.
* The Bend `telomare` follows master (merged at `9e7a58d1`): a refined lambda
  parameter `\(x : T)` is a bare refinement, checked statically; a misplaced
  pattern annotation is an error; `case` lowers over the scrutinee's spine
  with the builtins declared in one place; a missing definition is reported
  where it is used; and imports are looked up beside the program, then in
  the working directory. The goldens are master's output. With master's
  `Bool` refinements in the Prelude, sizing no longer proves tic-tac-toe's
  guard and main for every input, so its main keeps its aborts (the game
  `1 4 2 5 3` takes 6,166,768 interactions) and the erasure checker no
  longer runs on it.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
