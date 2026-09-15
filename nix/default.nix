# Everything the flake exposes, as plain Nix over a package set: the package,
# the development shell, the apps and the checks. flake.nix calls this with
# the flake's own source and `self`-derived version stamp; default.nix and
# shell.nix call it through nix/legacy.nix.
{
  pkgs,
  src,
  lspVersion ? "unknown",
}:
let
  hs = import ./haskell.nix { inherit pkgs; };
  telomare = import ./telomare.nix {
    inherit pkgs src;
    hsPkgs = hs.hsPkgs;
  };
  devShells = import ./devshell.nix {
    inherit telomare;
    hsPkgs = hs.hsPkgs;
    tools = hs.tools;
  };
  tools = import ./tools.nix {
    inherit
      pkgs
      src
      lspVersion
      telomare
      ;
    tools = hs.tools;
    executables = hs.executables;
    devShellNames = builtins.attrNames devShells;
  };
  packages = {
    inherit telomare;
    default = telomare;
  };
in
{
  inherit packages devShells;

  # One app per executable under its own name (`nix run .#telomare-repl`, as
  # CI does), plus the short names and the tooling.
  apps = {
    default = "${telomare}/bin/telomare";
    telomare = "${telomare}/bin/telomare";
    repl = "${telomare}/bin/telomare-repl";
    telomare-repl = "${telomare}/bin/telomare-repl";
    lsp = "${tools.telomareLsp}/bin/telomare-lsp";
    telomare-lsp = "${tools.telomareLsp}/bin/telomare-lsp";
    format = "${tools.telomareFormat}/bin/telomare-format";
    format-lint = "${tools.telomareFormatLint}/bin/telomare-format-lint-check";
    push-cachix = "${tools.pushCachix}/bin/telomare-push-cachix";
  };

  # `nix flake check` builds the package — with its five test suites — and
  # verifies formatting and linting.
  checks = packages // {
    format-lint = tools.formatLintCheck;
    push-cachix = tools.pushCachix;
  };
}
