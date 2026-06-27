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
    # Conal Elliott's Compile-to-Categories / ConCat packages (GHC plugin).
    concat.url = "github:compiling-to-categories/concat";
  };

  outputs = inputs@{ self, nixpkgs, flake-compat, flake-parts, haskell-flake, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      imports = [ inputs.haskell-flake.flakeModule ];
      perSystem = { self', system, pkgs, ... }:
      let
        # ── Conal Elliott's ConCat (Compile-to-Categories) toolchain ──────────
        # The `concat-plugin` is a GHC compiler plugin locked to GHC 9.4.8, so the
        # `ctc` showcase lives in its OWN pinned toolchain (ghc948 + ConCat's
        # overlay), separate from telomare's default ghc96 haskell-flake project.
        # This mirrors the working arrangement in ~/src/modArTransformer.
        ctcPkgs = import inputs.concat.inputs.nixpkgs {
          inherit system;
          overlays = [ inputs.concat.overlays.default ];
        };
        ctcHaskellPackages = ctcPkgs.haskell.packages.ghc948.extend (final: prev: {
          concat-inline = ctcPkgs.haskell.lib.dontHaddock prev.concat-inline;
          concat-plugin = ctcPkgs.haskell.lib.dontCheck prev.concat-plugin;
        });
        ctcPackage = ctcHaskellPackages.callCabal2nix "ctc" ./ctc { };
      in {
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

      # Type-check telomare-backwards.agda (denotational design with Felix)
      packages.agda-telomare-backwards =
        let
          stdlib = pkgs.agdaPackages.standard-library;
        in
        pkgs.stdenv.mkDerivation {
          name = "agda-telomare-backwards";
          src = pkgs.lib.cleanSource ./.;
          nativeBuildInputs = [ pkgs.agda pkgs.glibcLocales ];
          LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
          LC_ALL = "en_US.UTF-8";
          buildPhase = ''
            cp -r ${inputs.felix}/src felix-src
            chmod -R u+w felix-src
            agda -i ${stdlib}/src -i felix-src telomare-backwards.agda
          '';
          installPhase = ''
            mkdir -p $out
            echo "telomare-backwards type-checked" > $out/result
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

      # ── ConCat: render the telomare _⇨S_ design as circuit diagrams ──────────

      # The `telomare-ctc` executable: ports the telomare.agda _⇨S_ Fibonacci
      # morphisms to plain Haskell and emits their ConCat circuit DOT graphs.
      packages.ctc = ctcPackage;

      # Cabal dev shell for hacking on `ctc` (ConCat's ghc948 toolchain + GraphViz).
      #   cd ctc && nix develop ..#ctc && cabal run exe:telomare-ctc
      devShells.ctc = ctcHaskellPackages.shellFor {
        packages = p: [ ctcPackage ];
        nativeBuildInputs = [ ctcPkgs.cabal-install ctcPkgs.graphviz ];
        withHoogle = false;
      };

      # Just run the binary (writes out/*.dot, prints the Syn combinator forms).
      apps.ctc = {
        type = "app";
        program = "${self'.packages.ctc}/bin/telomare-ctc";
      };

      # The deliverable: generate the SVG diagrams.  Runs the ConCat binary to
      # write out/*.dot, then renders each to SVG with GraphViz (bundled).  The
      # SVGs are left in ./out for you to open.  Run from the repo root:
      #   nix run .#telomare-ctc-svg
      apps.telomare-ctc-svg = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-ctc-svg";
          runtimeInputs = [ ctcPkgs.graphviz pkgs.coreutils ];
          text = ''
            # Flake apps inherit the user's $PWD; write output there.
            cd "$PWD"
            out_dir="$PWD/out"
            mkdir -p "$out_dir"
            ${self'.packages.ctc}/bin/telomare-ctc
            for d in "$out_dir"/*.dot; do
              [ -e "$d" ] || continue
              svg="''${d%.dot}.svg"
              dot -Tsvg "$d" -o "$svg"
              echo "rendered $svg"
            done
            echo "SVG diagrams written to $out_dir"
          '';
        }}/bin/telomare-ctc-svg";
      };

      # ── Bend: run a hello-world (Higher Order Co's Bend, v1 / HVM2) ─────────
      # Run a Bend hello-world via the C HVM backend (real stdout print).
      # Uses pkgs.bend 0.2.37 (bundles hvm); pkgs.gcc provides the `cc` that
      # `bend run-c` shells out to.  Run from anywhere:  nix run .#bend-hello
      apps.bend-hello = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "bend-hello";
          runtimeInputs = [ pkgs.bend pkgs.gcc pkgs.coreutils ];
          text = ''
            bend run-c ${./bend/hello.bend}
          '';
        }}/bin/bend-hello";
      };

      # Run telomare's merge-sort network on Bend/HVM (parallel runtime).  The
      # hand port in bend/merge_sort.bend mirrors mergeSortS; HVM reduces the
      # independent compare-and-swaps in parallel.  nix run .#bend-sort
      apps.bend-sort = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "bend-sort";
          runtimeInputs = [ pkgs.bend pkgs.gcc pkgs.coreutils ];
          text = ''
            echo "telomare mergeSortS, run on Bend/HVM:  [3,1,4,2] ->"
            bend run-c ${./bend/merge_sort.bend}
          '';
        }}/bin/bend-sort";
      };

      # ConCat → HVM2 backend.  Compiles telomare morphism ports (Haskell) through
      # ConCat's toCcc into the new HVM category (ctc/src/HVM.hs), emitting runnable
      # Bend programs; then RUNS them on HVM2 and emits the raw HVM2 nets.
      #   nix run .#ctc-to-hvm
      apps.ctc-to-hvm = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "ctc-to-hvm";
          runtimeInputs = [ pkgs.bend pkgs.gcc pkgs.coreutils ];
          text = ''
            cd "$PWD"
            out_dir="$PWD/out"
            mkdir -p "$out_dir"
            ${self'.packages.ctc}/bin/telomare-hvm          # emits out/hvm-*.bend
            echo ""
            echo "=== run on HVM2 (bend run-c) + emit raw HVM2 nets (bend gen-hvm) ==="
            for n in hvm-sqr hvm-fib-step hvm-merge-sort4 hvm-merge-sort8; do
              [ -e "$out_dir/$n.bend" ] || continue
              printf '%s  ->  ' "$n"
              # filter Bend's harmless "unused definition" warnings (the prelude
              # defines every combinator; each program uses a subset)
              bend run-c "$out_dir/$n.bend" 2>&1 \
                | grep -vE 'Warnings:|Definition is unused|^In ' || true
              bend gen-hvm "$out_dir/$n.bend" > "$out_dir/$n.hvm" 2>/dev/null
            done
            echo ""
            echo "=== bounded recursion through ConCat -> HVM2 (size = runtime CLI arg) ==="
            # step/init/leaf/combine go through toCcc; recursion is a primitive loop
            # in the emitted Bend, run natively (and in PARALLEL for the fold) by HVM2.
            for n in 10 20 30; do
              printf 'fib via iterS  n=%s  ->  ' "$n"
              bend run-c "$out_dir/hvm-fib-iter.bend" "$n" 2>/dev/null | sed 's/Result: //'
            done
            echo "tree-sum via foldC (parallel divide-and-conquer), depth=20:"
            bend run-c -s "$out_dir/hvm-tree-sum.bend" 20 2>/dev/null \
              | grep -iE 'Result|ITRS|TIME|MIPS'
            echo ""
            echo "Bend sources + raw HVM2 nets written to $out_dir (hvm-*.bend, hvm-*.hvm)."
          '';
        }}/bin/ctc-to-hvm";
      };

      checks = self'.packages;
    };
  };
}
