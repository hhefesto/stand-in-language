{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    felix = {
      url = "github:conal/felix";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, flake-compat, flake-parts, haskell-flake, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      imports = [ inputs.haskell-flake.flakeModule ];
      perSystem = { self', system, pkgs, ... }: {
        haskellProjects.default = {
          basePackages = pkgs.haskell.packages.ghc96;
          # To get access to non-Haskell dependencies one most add them to `extraBuildDepends`
          # and then use the haskell package `which` to locate the Filepath of the executable
          # that's being added. In this toy example we'll be using the non-Haskell dependency
          # `cowsay` findable in nixpkgs like so:
          #
          # telomare = {
          #   extraBuildDepends = [ pkgs.cowsay
          #                       ];
          # };
          #
          # An example of Haskell code using `cowsay` would be:
          # ```haskell
          # cowsayBin :: FilePath
          # cowsayBin = $(staticWhich "cowsay")

          # cowsay :: IO String
          # cowsay = do
          #   (_, mhout, _, _) <- createProcess (shell $ show cowsayBin <> " hola") { std_out = CreatePipe }
          #   case mhout of
          #     Just hout -> hGetContents hout
          #     Nothing -> pure "mhout failed"
          # ```
          # settings = {
          #   semaphore-compat = {
          #     check = false;
          #     jailbreak = true;
          #   };
          # };
          devShell = {
            enable = true;
            tools = hp: {
              inherit (hp) cabal-install haskell-language-server;
            };
            mkShellArgs = {
              nativeBuildInputs =
                let
                  agdaWithStdlib = pkgs.agda.withPackages (p: [ p.standard-library ]);
                  # Pre-compile felix interfaces so agda finds _build/ in $out
                  # (parent of the -i include path) and never tries to write to
                  # the read-only nix store.
                  felixCompiled = pkgs.stdenv.mkDerivation {
                    name = "felix-compiled";
                    src = inputs.felix;
                    nativeBuildInputs = [ agdaWithStdlib ];
                    # Compile from $out/src so that the paths baked into the
                    # .agdai files match the final nix store location.
                    # _build/ lands at $out/ (parent of the -i include path).
                    buildPhase = ''
                      mkdir -p $out/src
                      cp -r src/. $out/src/
                      cd $out
                      agda -i src -i ${pkgs.agdaPackages.standard-library}/src src/Felix/Homomorphism.agda
                    '';
                    installPhase = ":";
                  };
                  myAgda = pkgs.symlinkJoin {
                    name = "agda-with-felix";
                    paths = [ agdaWithStdlib ];
                    buildInputs = [ pkgs.makeWrapper ];
                    postBuild = ''
                      wrapProgram $out/bin/agda \
                        --add-flags "-i ${felixCompiled}/src"
                    '';
                  };
                in [
                  myAgda
                  pkgs.glibcLocales
                ];
              shellHook = ''
                export LOCALE_ARCHIVE="${pkgs.glibcLocales}/lib/locale/locale-archive"
                export LC_ALL="en_US.UTF-8"
                echo "Agda ready. Compile with:"
                echo "  agda --compile telomare.agda"
              '';
            };
          };
      };

      packages.default = self'.packages.telomare;

      packages.agda-telomare =
        let
          stdlib = pkgs.agdaPackages.standard-library;
        in
        pkgs.stdenv.mkDerivation {
          name = "agda-telomare";
          src = pkgs.lib.cleanSource ./.;
          nativeBuildInputs = [ pkgs.agda pkgs.ghc pkgs.glibcLocales ];
          LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
          LC_ALL = "en_US.UTF-8";
          buildPhase = ''
            cp -r ${inputs.felix}/src felix-src
            chmod -R u+w felix-src
            agda -i ${stdlib}/src -i felix-src --compile telomare.agda
          '';
          installPhase = ''
            mkdir -p $out/bin
            cp telomare $out/bin/agda-telomare
          '';
        };

      apps.agda-telomare = {
        type = "app";
        program = "${self'.packages.agda-telomare}/bin/agda-telomare";
      };

      apps.default = {
        type = "app";
        program = "${self'.packages.agda-telomare}/bin/agda-telomare";
      };
      apps.repl = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare-repl";
      };
      apps.evaluare = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare-evaluare";
      };
      apps.lsp = {
        type = "app";
        program = "${self.packages.${system}.telomare}/bin/telomare-lsp";
      };

      checks = self'.packages;
    };
  };
}
