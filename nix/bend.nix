# The Bend sources and the checks over them. A build sees the .bend files
# under bend/ and the C and JS of the port's own effects (bend/effs: the
# IC's loop in C, Native.bend) and nothing else, so an edit to prose or Nix
# rebuilds nothing.
{
  pkgs,
  src,
  bend,
  leanPkgs,
}:
let
  inherit (pkgs) lib;

  bendFiles = lib.fileset.unions [
    (lib.fileset.fileFilter (file: file.hasExt "bend") (src + "/bend"))
    (src + "/bend/effs")
  ];

  bendSrc = lib.fileset.toSource {
    root = src;
    fileset = bendFiles;
  };

  telFiles = lib.fileset.fileFilter (file: file.hasExt "tel") src;

  # The tests also read the Telomare programs the goldens run.
  testSrc = lib.fileset.toSource {
    root = src;
    fileset = lib.fileset.unions [
      bendFiles
      telFiles
    ];
  };

  goldenSrc = lib.fileset.toSource {
    root = src;
    fileset = lib.fileset.unions [
      (src + "/test/golden")
      telFiles
    ];
  };

  # The language server's sessions (test/lsp) and the programs they open.
  lspSrc = lib.fileset.toSource {
    root = src;
    fileset = lib.fileset.unions [
      (src + "/test/lsp")
      telFiles
    ];
  };

  # The golden cases the port covers: runs on IC (the plain runs too, whose
  # output is the same), compile errors, the static report (--certificate),
  # the meter (--ic --meter; its expectation is test/golden/port's), the
  # unsized runs (--fast; the meter's and the fuel's are port's too), and
  # compiled programs (--compile, whose artifact is port's, and the .telc
  # run), the REPL (`--expr` and its lines), and --draw-net (an invalid
  # option, as the command line's errors are master's). The others need
  # haskell-final's IC certificate (--ic --compile, --ic --certificate,
  # .telc with --ic).
  goldenPatterns = [
    "*.run"
    "*.run-*"
    "*.ic"
    "*.ic-abort"
    "*.ic-carry"
    "*.ic-meter"
    "*.ic-certificate"
    "*.ic-compile"
    "*.telc-ic"
    "*.telc-ic-certificate"
    "*.certificate"
    "*.test-game"
    "*.test-game-ic"
    "*.fast"
    "*.fast-*"
    "*.compile"
    "*.telc-run"
    "*.telc-certificate"
    "*.ic-draw-net"
    "repl.*"
  ];

  # Each test under bend/tests prints one `ok NAME` line per group it checks
  # (`FAIL NAME` when one breaks); these are the lines it must print, in order.
  # A test file missing here fails the check rather than going unrun. Tests
  # run from the source root, where the programs are.
  tests = {
    front = [
      "parse-accept"
      "parse-reject"
      "parse-left-assoc"
      "parse-spans"
      "parse-module"
      "parse-empty-list-def"
      "expand-errors"
      "programs-parse"
      "sites-tc_ultra_minimal"
      "sites-simpleplus"
      "sites-tictactoe"
      "sites-limits"
      "testchar-error"
    ];
    ic = [
      "ic-application"
      "ic-projection"
      "ic-duplication"
      "ic-gates"
      "ic-abort"
      "ic-church"
      "ic-fuel"
      "ic-laziness"
      "ic-omega"
      "ic-constants"
      "ic-case"
      "ic-udt"
      "ic-meter-case-udt"
      "ic-prologue"
      "ic-meter-tc_ultra_minimal"
      "ic-meter-simpleplus"
      "ic-meter-tictactoe"
      "ic-usage-agrees"
    ];
    eal = [
      "sha256-vectors"
      "eal-linear"
      "eal-lift-dedupe"
      "eal-self-application"
      "eal-capture-layouts"
      "eal-localized-failure"
      "eal-certify-main"
      "eal-usage"
      "eal-programs"
      "eal-pinned"
      "eal-sized"
      "eal-lift-udt"
      "eal-layouts-tc_ultra_minimal"
      "eal-layouts-simpleplus"
    ];
    # master's EALTests (98de497c) on bend/EALm.bend, master's EAL
    ealm = [
      "identity-defer-linear"
      "disjoint-projections-linear"
      "env-shuffle-linear"
      "duplicated-path-one-box"
      "whole-and-part-contraction"
      "church-two-double-application"
      "duplicated-closure-both-sites"
      "gate-branches-multiplicative"
      "sibling-contractions-dedupe"
      "self-application-interface-cycle"
      "applying-data-certifies"
      "duplicated-input-box"
      "usage-contraction-path"
      "guidance-usage-bangs-speculation"
      "guidance-capture-layouts"
      "guidance-unsized-not-speculatable"
      "simple-main"
      "lambda-church-application"
      "church-literal-composition"
      "gate-joins-different-closures"
      "closure-capturing-closures-join"
      "prelude-listEqual"
      "filter-over-range"
      "deferLift-dedupes-siblings"
      "failing-body-localized"
      "sizing-preserves-church-application"
      "sizing-preserves-church-literal"
      "d2c-before-and-after-sizing"
      "function-wrapped-recursion"
      "curried-recursion"
      "sized-foldr"
      "pinned-disagreeing-arity"
      "same-arity-gate-join"
    ];
    fast = [
      "fast-agrees"
      "fast-base-case"
      "fast-sites"
      "fast-unsized"
      "fast-fuel"
    ];
    telc = [
      "telc-round-trip"
      "telc-runs"
      "telc-ready"
      "telc-prologue"
      "telc-magic"
      "telc-hash"
      "telc-nodes"
    ];
    native = [
      "native-terms"
      "native-pairs"
      "native-sessions"
    ];
    rules = [
      "rules-terms"
      "rules-pairs"
      "rules-sessions"
    ];
    sem = [
      "sem-tc_ultra_minimal"
      "sem-simpleplus"
      "sem-tictactoe"
    ];
    size = [
      "size-tc_ultra_minimal"
      "size-simpleplus"
      "size-tictactoe"
      "size-over-budget"
      "size-budget-exhausted"
      "size-unbounded-input"
      "size-mislabeled"
      "size-where-checks-go"
      "size-filter"
      "size-erased"
    ];
    lexical = [
      "reserved"
      "unreserved"
      "reserved-count"
      "start"
      "not-start"
      "continue"
      "not-continue"
      "comments"
    ];
  };

  # `bend` in the sandbox, over a writable copy of the sources: its release
  # launcher keeps state under HOME and checks for updates unless told not to.
  bendCommand =
    name: source: script:
    pkgs.runCommand name { nativeBuildInputs = [ bend ]; } ''
      export HOME=$TMPDIR BEND_NO_TELEMETRY=1
      cp -r ${source}/. .
      chmod -R u+w .
      ${script}
    '';

  # The `telomare` command, compiled to a native binary: bend/Native.bend,
  # which is bend/Main.bend's command with the IC's loop in C; the REPL,
  # `telomare-repl` (bend/Repl.bend), under rlwrap at a terminal for the line
  # editing and history master's haskeline gives (in the session only, as
  # haskeline's defaults keep them; rlwrap from leanPkgs, whose nixpkgs has a
  # binary cache, where corepkgs would build a C compiler for it); and the
  # language server, `telomare-lsp` (bend/Lsp.bend).
  telomare = bendCommand "telomare" bendSrc ''
    mkdir -p $out/bin $out/libexec
    bend bend/Native.bend -o $out/bin/telomare
    bend bend/Repl.bend -o $out/libexec/telomare-repl
    bend bend/Lsp.bend -o $out/bin/telomare-lsp
    cat > $out/bin/telomare-repl <<EOF
    #!${pkgs.runtimeShell}
    if [ -t 0 ] && [ -t 1 ] && [ -n "\''${TERM:-}" ] && [ "\$TERM" != dumb ]; then
      exec ${leanPkgs.rlwrap}/bin/rlwrap -c -n -H /dev/null $out/libexec/telomare-repl "\$@"
    fi
    exec $out/libexec/telomare-repl "\$@"
    EOF
    chmod +x $out/bin/telomare-repl
  '';

  # BendTT's kernel, the Lean program `bend --verdict` re-checks proofs with
  # (bend2/bendtt.lean in Bend's release; its soundness is proven in Lean).
  # Bend would build it on first use with an elan or PATH Lean v4.34; here
  # it is built once, with the `lean` input's Lean, and named by $BENDTT.
  bendtt = leanPkgs.runCommandCC "bendtt" { nativeBuildInputs = [ leanPkgs.lean4 ]; } ''
    cp ${bend}/libexec/bend/bend2/bendtt.lean .
    lean -c bendtt.c bendtt.lean
    leanc -O3 -DNDEBUG bendtt.c -o bendtt
    install -Dm755 bendtt $out/bin/bendtt
  '';
in
{
  inherit telomare bendtt;

  # The command against what haskell-final printed (test/golden).
  goldens = pkgs.runCommand "goldens" { } ''
    cp -r ${goldenSrc}/. .
    chmod -R u+w .
    bash test/golden/run.sh ${telomare}/bin check ${lib.escapeShellArgs goldenPatterns}
    touch $out
  '';

  # The language server against what master's answered (test/lsp).
  lsp = pkgs.runCommand "lsp" { nativeBuildInputs = [ pkgs.python3 ]; } ''
    cp -r ${lspSrc}/. .
    chmod -R u+w .
    bash test/lsp/run.sh ${telomare}/bin check
    touch $out
  '';

  # Every module type-checks, terminates and proves its laws.
  check = bendCommand "bend-check" bendSrc ''
    bend bend/Everything.bend | tee result
    grep -qx "ALL PROOFS CHECK" result
    touch $out
  '';

  # The proofs that sizing's erasures are sound (bend/PROOF.bend), re-checked
  # by BendTT's kernel: Bend's checker is then out of the trusted base.
  proof = bendCommand "bend-proof" bendSrc ''
    BENDTT=${bendtt}/bin/bendtt bend bend/PROOF.bend --verdict | tee result
    grep -qx "ALL PROOFS CHECK" result
    touch $out
  '';

  # bend/effs/ic.c's generated parts are what bend/dev/genic.bend prints, from
  # IC.bend's dispatch and bend/Rules.bend's table.
  icGenerated = bendCommand "ic-generated" bendSrc ''
    bend bend/dev/genic.bend > ic.c.generated
    diff bend/effs/ic.c ic.c.generated
    touch $out
  '';

  # Every test, compiled to a native binary (C through clang) and run.
  tests = bendCommand "bend-tests" testSrc ''
    for test in bend/tests/*.bend; do
      test="''${test#bend/tests/}"
      name="''${test%.bend}"
      case "$name" in
        ${lib.concatStringsSep "|" (builtins.attrNames tests)}) ;;
        *)
          echo "bend/tests/$test has no expected lines in nix/bend.nix" >&2
          exit 1
          ;;
      esac
    done
    ${lib.concatStrings (
      lib.mapAttrsToList (name: lines: ''
        bend bend/tests/${name}.bend -o "$TMPDIR/${name}"
        "$TMPDIR/${name}" > "$TMPDIR/${name}.out"
        printf 'ok %s\n' ${lib.escapeShellArgs lines} | diff - "$TMPDIR/${name}.out"
      '') tests
    )}
    touch $out
  '';
}
