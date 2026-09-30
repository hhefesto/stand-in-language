# The Bend sources and the checks over them. A build sees the .bend files
# under bend/ and nothing else, so an edit to prose or Nix rebuilds nothing.
{
  pkgs,
  src,
  bend,
}:
let
  inherit (pkgs) lib;

  bendFiles = lib.fileset.fileFilter (file: file.hasExt "bend") (src + "/bend");

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

  # The golden cases the port covers: runs on IC (the plain runs too, whose
  # output is the same), and compile errors. The others are haskell-final's
  # other actions (--certificate, --meter, --compile, .telc, --draw-net) and
  # the REPL.
  goldenPatterns = [
    "*.run"
    "*.run-*"
    "*.ic"
    "*.ic-abort"
    "*.ic-carry"
    "*.test-game"
    "*.test-game-ic"
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
      "ic-meter-tc_ultra_minimal"
      "ic-meter-simpleplus"
      "ic-meter-tictactoe"
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
      "eal-layouts-tc_ultra_minimal"
      "eal-layouts-simpleplus"
    ];
    size = [
      "size-tc_ultra_minimal"
      "size-simpleplus"
      "size-tictactoe"
      "size-over-budget"
      "size-budget-exhausted"
      "size-unbounded-input"
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

  # The `telomare` command, bend/Main.bend compiled to a native binary.
  telomare = bendCommand "telomare" bendSrc ''
    mkdir -p $out/bin
    bend bend/Main.bend -o $out/bin/telomare
  '';
in
{
  inherit telomare;

  # The command against what haskell-final printed (test/golden).
  goldens = pkgs.runCommand "goldens" { } ''
    cp -r ${goldenSrc}/. .
    chmod -R u+w .
    bash test/golden/run.sh ${telomare}/bin check ${lib.escapeShellArgs goldenPatterns}
    touch $out
  '';

  # Every module type-checks, terminates and proves its laws.
  check = bendCommand "bend-check" bendSrc ''
    bend bend/Everything.bend | tee result
    grep -qx "ALL PROOFS CHECK" result
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
