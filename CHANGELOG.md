# Revision history for telomare

## Unreleased (branch `bend-port`)

* New: `bend/` — a port of the telomare compiler to Bend (HVM2): lexer,
  parser, shared-let resolver, the full Possible.hs recursion-sizing
  abstract interpreter, and a native-Bend emission backend — compiled
  programs are emitted as defunctionalized Bend code executed directly by
  HVM. Fully type-annotated; verified against the Haskell compiler
  (see `bend/PORT.md` for the engineering log and `COMPARISON.md` for the
  three-way Haskell/Agda/Bend comparison).
* New flake app: `nix run .#telomare-bend -- <program.tel> < moves` —
  two-stage driver (compile under `bend run-rs`, cached by source hash;
  run under `hvm run-c`), shell/awk only.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
