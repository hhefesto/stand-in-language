# `nix develop`: the pinned `bend`, which checks, runs and compiles the port
# (`bend bend/Everything.bend`, `bend FILE.bend -o OUT`). corepkgs has no
# plain `mkShell` (its `mkDevShell` adds process-compose and service
# directories), so the shell is the derivation such a `mkShell` makes. No C
# compiler of its own: Bend brings the clang it compiles with.
{ pkgs, bend }:
{
  default = pkgs.stdenvNoCC.mkDerivation {
    name = "telomare";
    nativeBuildInputs = [ bend ];
    # Bend's launcher otherwise checks for a newer release on every run.
    # (Under structured attributes only `env` reaches the environment.)
    env.BEND_NO_TELEMETRY = "1";
    # corepkgs builds with structured attributes, which leave `name` an
    # unexported shell variable: direnv drops it, and prompts that show the
    # environment's name (any-nix-shell's reads `$name`) have none.
    shellHook = ''
      export name
    '';
    phases = [ "buildPhase" ];
    buildPhase = ''
      echo "This derivation is not meant to be built, only to be used with nix develop"
      touch $out
    '';
  };
}
