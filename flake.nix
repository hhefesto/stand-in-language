{
  description = "Telomare: a simple but robust virtual machine";

  inputs = {
    # The ekala package ecosystem: corepkgs supplies stdenv and the build
    # helpers the checks and the shell are made of.
    corepkgs.url = "github:ekala-project/corepkgs";
    # corepkgs' formatter pulls nixpkgs in through treefmt-nix; nothing this
    # flake evaluates uses it, so it follows an input that is already here.
    corepkgs.inputs.treefmt-nix.inputs.nixpkgs.follows = "corepkgs/nix-lib";
    # Bend 2, the language Telomare is written in. Its flake packages the
    # release archive over its own nixpkgs (bun, clang, autoPatchelf), which
    # is the one nixpkgs in the lock: only the `bend` command comes from it.
    bend.url = "github:bendlang/bend";
    # Lean 4.34, which builds BendTT's kernel: `bend --verdict` re-checks the
    # proofs with it (the `bend-proof` check). Bend's own nixpkgs has Lean
    # 4.30, which cannot build the kernel. Only `lean4` comes from here.
    lean.url = "github:NixOS/nixpkgs/e7439b6b14ad3cc35d05608ebca9bce01a25f5f8";
  };

  # An input's nixConfig is not applied transitively, so the caches this build
  # can draw on are named here: `telomare` holds everything this flake builds;
  # `ekala-corepkgs` holds the base system. Bend's closure comes from
  # cache.nixos.org.
  nixConfig = {
    extra-substituters = [
      "https://telomare.cachix.org"
      "https://ekala-corepkgs.cachix.org"
    ];
    extra-trusted-public-keys = [
      "telomare.cachix.org-1:H0qRjVstxtb9oyEPvDDpmPSLyJ9oViAsTgwR02ra6Dk="
      "ekala-corepkgs.cachix.org-1:DcZV+vegWoEzacbSdXFXU4S7728C0eS9RfGpKeyHd6w="
    ];
  };

  outputs =
    {
      self,
      corepkgs,
      bend,
      lean,
    }:
    let
      project =
        pkgs:
        import ./nix {
          inherit pkgs;
          src = ./.;
          bend = bend.packages.${pkgs.stdenv.hostPlatform.system}.default;
          leanPkgs = lean.legacyPackages.${pkgs.stdenv.hostPlatform.system};
        };
    in
    corepkgs.lib.mkFlake {
      # corepkgs' stdenv is checked on x86_64-linux alone for now.
      systems = [ "x86_64-linux" ];
      packages = pkgs: (project pkgs).packages;
      devShells = pkgs: (project pkgs).devShells;
      checks = pkgs: (project pkgs).checks;
      apps = pkgs: (project pkgs).apps;
    };
}
