# Everything the flake exposes, as plain Nix over a package set and the pinned
# Bend: the packages, the development shell, the apps and the checks.
# flake.nix calls this with the flake's source; default.nix and shell.nix call
# it through nix/legacy.nix.
#
# Until the port has a `telomare` command, the package is Bend itself.
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
  packages = {
    inherit bend;
    default = bend;
  };

  apps = {
    bend = "${bend}/bin/bend";
    push-cachix = "${tools.pushCachix}/bin/telomare-push-cachix";
  };

  # `nix flake check` checks every Bend module (types, termination, laws) and
  # runs the tests, each built to a native binary.
  checks = {
    bend-check = project.check;
    bend-tests = project.tests;
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
