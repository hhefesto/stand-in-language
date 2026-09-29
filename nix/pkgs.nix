# The package set: corepkgs, as the flake builds it, for callers without a
# flake.
{
  system ? builtins.currentSystem,
}:
let
  pins = import ./pins.nix;
in
import pins.corepkgs { inherit system; }
