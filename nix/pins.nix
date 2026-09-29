# The flake's inputs for the flake-less entry points (default.nix, shell.nix),
# read from flake.lock so that both roads lead to the same package set and the
# same Bend — the way ekapkgs' own pins.nix does it.
let
  lock = builtins.fromJSON (builtins.readFile ../flake.lock);
  fetch =
    name:
    let
      node = lock.nodes.${name}.locked;
    in
    if node.type == "path" then
      builtins.fetchTree { inherit (node) type path narHash; }
    else
      builtins.fetchTree {
        inherit (node)
          type
          owner
          repo
          rev
          narHash
          ;
      };
  # A locked flake's outputs, called the way Nix calls them: its inputs are
  # the nodes the lock resolved them to, and `self` is the flake itself. Only
  # direct node references are followed, which is all Bend's lock holds.
  callFlake =
    name:
    let
      sourceInfo = fetch name;
      inputs = builtins.mapAttrs (_: callFlake) (lock.nodes.${name}.inputs or { });
      outputs = (import "${sourceInfo}/flake.nix").outputs (inputs // { self = flake; });
      flake =
        outputs
        // sourceInfo
        // {
          inherit inputs outputs sourceInfo;
          _type = "flake";
        };
    in
    flake;
in
{
  corepkgs = fetch "corepkgs";
  bend = callFlake "bend";
}
