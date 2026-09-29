# What default.nix and shell.nix build: the project over the pinned package
# set and the pinned Bend, from the working tree. (The flake builds from its
# own source, which is the tracked files; either way the builds see only the
# .bend files, so both give the same derivations.)
{
  system ? builtins.currentSystem,
}:
let
  pins = import ./pins.nix;
in
import ./. {
  pkgs = import ./pkgs.nix { inherit system; };
  src = ./..;
  bend = pins.bend.packages.${system}.default;
}
