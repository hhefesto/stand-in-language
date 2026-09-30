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

  # The tests also read the Telomare programs the goldens run.
  testSrc = lib.fileset.toSource {
    root = src;
    fileset = lib.fileset.unions [
      bendFiles
      (lib.fileset.fileFilter (file: file.hasExt "tel") src)
    ];
  };

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
in
{
  # The `telomare` command, bend/Main.bend compiled to a native binary.
  telomare = bendCommand "telomare" bendSrc ''
    mkdir -p $out/bin
    bend bend/Main.bend -o $out/bin/telomare
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
