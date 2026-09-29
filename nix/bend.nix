# The Bend sources and the checks over them. A build sees the .bend files
# under bend/ and nothing else, so an edit to prose or Nix rebuilds nothing.
{
  pkgs,
  src,
  bend,
}:
let
  inherit (pkgs) lib;

  bendSrc = lib.fileset.toSource {
    root = src;
    fileset = lib.fileset.fileFilter (file: file.hasExt "bend") (src + "/bend");
  };

  # Each test under bend/tests prints one `ok NAME` line per group it checks
  # (`FAIL NAME` when one breaks); these are the lines it must print, in order.
  # A test file missing here fails the check rather than going unrun.
  tests = {
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

  # `bend` in the sandbox: its release launcher keeps state under HOME and
  # checks for updates unless told not to.
  bendCommand =
    name: script:
    pkgs.runCommand name { nativeBuildInputs = [ bend ]; } ''
      export HOME=$TMPDIR BEND_NO_TELEMETRY=1
      cp -r ${bendSrc}/bend bend
      chmod -R u+w bend
      ${script}
      touch $out
    '';
in
{
  # Every module type-checks, terminates and proves its laws.
  check = bendCommand "bend-check" ''
    bend bend/Everything.bend | tee result
    grep -qx "ALL PROOFS CHECK" result
  '';

  # Every test, compiled to a native binary (C through clang) and run.
  tests = bendCommand "bend-tests" ''
    cd bend/tests
    for test in *.bend; do
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
        bend ${name}.bend -o "$TMPDIR/${name}"
        "$TMPDIR/${name}" > ${name}.out
        printf 'ok %s\n' ${lib.escapeShellArgs lines} | diff - ${name}.out
      '') tests
    )}
  '';
}
