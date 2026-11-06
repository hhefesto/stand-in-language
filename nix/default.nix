# Everything the flake exposes, as plain Nix over a package set and the pinned
# Bend: the packages, the development shell, the apps and the checks.
# flake.nix calls this with the flake's source; default.nix and shell.nix call
# it through nix/legacy.nix.
{
  pkgs,
  src,
  bend,
  leanPkgs,
  lspVersion ? "unknown",
}:
let
  project = import ./bend.nix {
    inherit
      pkgs
      src
      bend
      leanPkgs
      ;
  };
  devShells = import ./devshell.nix {
    inherit pkgs bend;
    inherit (project) bendtt;
  };
  tools = import ./tools.nix {
    inherit pkgs lspVersion;
    inherit (project) telomare;
    devShellNames = builtins.attrNames devShells;
    checkNames = builtins.attrNames checks;
    appNames = builtins.attrNames apps;
  };
  telomare = project.telomare;
  packages = {
    inherit telomare bend;
    inherit (project) bendtt;
    default = telomare;
  };

  # One app per executable under its own name, plus the short names (as
  # master's flake has them: the Emacs mode runs `#lsp`).
  apps = {
    default = "${telomare}/bin/telomare";
    telomare = "${telomare}/bin/telomare";
    repl = "${telomare}/bin/telomare-repl";
    telomare-repl = "${telomare}/bin/telomare-repl";
    lsp = "${tools.telomareLsp}/bin/telomare-lsp";
    telomare-lsp = "${tools.telomareLsp}/bin/telomare-lsp";
    bend = "${bend}/bin/bend";
    push-cachix = "${tools.pushCachix}/bin/telomare-push-cachix";
  };

  # `nix flake check` builds the command, checks every Bend module (types,
  # termination, laws), re-checks the proofs with BendTT's kernel, runs the
  # tests, each built to a native binary, runs the command on the goldens
  # it covers, and the language server on its sessions.
  checks = {
    inherit telomare;
    bend-check = project.check;
    bend-proof = project.proof;
    ic-generated = project.icGenerated;
    bend-tests = project.tests;
    goldens = project.goldens;
    lsp = project.lsp;
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
