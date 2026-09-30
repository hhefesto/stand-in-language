# Everything the flake exposes, as plain Nix over a package set and the pinned
# Bend: the packages, the development shell, the apps and the checks.
# flake.nix calls this with the flake's source; default.nix and shell.nix call
# it through nix/legacy.nix.
{
  pkgs,
  src,
  bend,
}:
let
  project = import ./bend.nix { inherit pkgs src bend; };
  devShells = import ./devshell.nix { inherit pkgs bend; };
  tools = import ./tools.nix {
    inherit pkgs;
    devShellNames = builtins.attrNames devShells;
    checkNames = builtins.attrNames checks;
    appNames = builtins.attrNames apps;
  };
  telomare = project.telomare;
  packages = {
    inherit telomare bend;
    default = telomare;
  };

  apps = {
    default = "${telomare}/bin/telomare";
    telomare = "${telomare}/bin/telomare";
    bend = "${bend}/bin/bend";
    push-cachix = "${tools.pushCachix}/bin/telomare-push-cachix";
  };

  # `nix flake check` builds the command, checks every Bend module (types,
  # termination, laws), runs the tests, each built to a native binary, and
  # runs the command on the goldens it covers.
  checks = {
    inherit telomare;
    bend-check = project.check;
    bend-tests = project.tests;
    goldens = project.goldens;
    push-cachix = tools.pushCachix;
  };
in
{
  inherit
    packages
    devShells
    apps
    checks
    ;
}
