# `nix develop`: the project's dependencies, GHC and cabal-install — the
# minimum that builds telomare. `nix develop .#full` adds the editor and
# linting tools: haskell-language-server, hlint, stylish-haskell, ghcid.
# Hoogle is not built for either shell (haskell-flake used to build a
# database over every dependency); `withHoogle = true` brings it back.
{ hsPkgs, tools, telomare }:
let
  shell = extra: hsPkgs.shellFor {
    packages = _: [ telomare ];
    withHoogle = false;
    nativeBuildInputs = [ tools.cabal-install ] ++ extra;
  };
in
{
  default = shell [ ];
  full = shell [
    tools.haskell-language-server
    tools.hlint
    tools.stylish-haskell
    tools.ghcid
  ];
}
