{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, flake-compat, flake-parts, haskell-flake, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      imports = [ inputs.haskell-flake.flakeModule ];
      perSystem = { self', system, pkgs, ... }:
        let
          # Agda toolchain for the telomare3 machine-checked spec
          # (telomare3/spec/, --safe, zero postulates) and for re-checking
          # design/telomare2.agda in-branch. Same idiom the `agda` branch's
          # dev shell used, so the cross-branch `nix develop ?ref=agda`
          # trick is retired.
          agdaWithStdlib = pkgs.agda.withPackages (p: [ p.standard-library ]);
          lspVersion =
            if self ? lastModifiedDate then
              let
                timestamp = self.lastModifiedDate;
                year = builtins.substring 0 4 timestamp;
                month = builtins.substring 4 2 timestamp;
                day = builtins.substring 6 2 timestamp;
                hour = builtins.substring 8 2 timestamp;
                minute = builtins.substring 10 2 timestamp;
              in "${year}-${month}-${day}T${hour}:${minute}Z"
            else
              "unknown";
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
            # bend/hvm in the dev shell serves two purposes: they are on PATH
            # for the hybrid/T2 drivers, and — because .envrc uses
            # `use flake .` with nix-direnv + keep-outputs — the direnv
            # gcroot now pins their store paths, so `nix-collect-garbage`
            # cannot sweep them again (it did once; restoring meant
            # rebuilding from the pinned nixpkgs rev, see HANDOFF.md).
            mkShellArgs = {
              nativeBuildInputs = [ pkgs.bend pkgs.hvm agdaWithStdlib ];
            };
          };
      };

      packages.default = self'.packages.telomare;

      apps.default = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare";
      };
      apps.repl = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare-repl";
      };
      # Telomare 3: greenfield reimplementation (telomare3/ package,
      # design/TELOMARE3-DESIGN.md). Spec-first: telomare3/spec/ (Agda)
      # is the source of truth, checked by checks.telomare3-spec.
      apps.telomare3 = {
        type = "app";
        program = self.packages.${system}.telomare3 + "/bin/telomare3";
      };
      apps.evaluare = {
        type = "app";
        program = self.packages.${system}.telomare + "/bin/telomare-evaluare";
      };
      # telomare compiler hosted on Bend/HVM2 (bend/ — see bend/PORT.md).
      # Two stages: the compiler runs under `bend run-rs` (lazy Rust runtime)
      # and returns the generated program as a pure result value; the
      # generated (defunctionalized) program runs under the standalone HVM C
      # interpreter. Scripted: `nix run .#telomare-bend -- game.tel < moves`.
      apps.telomare-bend = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-bend";
          runtimeInputs = [ pkgs.bend pkgs.hvm pkgs.gawk pkgs.gnused pkgs.coreutils ];
          text = ''
            export BEND_BIN=bend
            export HVM_BIN=hvm
            exec "${self}/bend/run_telomare_bend.sh" "$@"
          '';
        }}/bin/telomare-bend";
      };
      # Hybrid pipeline: the Haskell compiler front end (parse/resolve/
      # Possible.hs recursion sizing) emits a defunctionalized Bend program
      # (`telomare --emit-hvm`, src/Telomare/HvmBackend.hs) which HVM2
      # executes natively. `nix run .#telomare-hvm -- game.tel < moves`.
      apps.telomare-hvm = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-hvm";
          runtimeInputs = [ pkgs.bend pkgs.hvm pkgs.gcc pkgs.gawk pkgs.coreutils ];
          text = ''
            export TELOMARE_BIN="${self.packages.${system}.telomare}/bin/telomare"
            export BEND_BIN=bend
            export HVM_BIN=hvm
            exec "${self}/bend/run_telomare_hvm.sh" "$@"
          '';
        }}/bin/telomare-hvm";
      };
      # Telomare 2 backend: same front end, but emission follows the T2
      # affine discipline (design/TELOMARE2-DESIGN.md par.12; explicit forced
      # duplication at contraction/box sites, src/Telomare/T2Backend.hs).
      # `nix run .#telomare2 -- game.tel < moves`. Env overrides pass through
      # (TELOMARE_HVM_RUNNER, TELOMARE_HVM_TIMEOUT, TELOMARE_EMIT_FLAG=
      # --emit-t2-lazy for the discipline-off baseline, ...).
      apps.telomare2 = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare2";
          runtimeInputs = [ pkgs.bend pkgs.hvm pkgs.gcc pkgs.gawk pkgs.gnused pkgs.coreutils ];
          text = ''
            export TELOMARE_BIN="${self.packages.${system}.telomare}/bin/telomare"
            export BEND_BIN=bend
            export HVM_BIN=hvm
            export TELOMARE_EMIT_FLAG="''${TELOMARE_EMIT_FLAG:---emit-t2}"
            # gen-c-big: single-threaded compiled runtime with the arena and
            # def-table sizes large programs (tictactoe) need.
            export TELOMARE_HVM_RUNNER="''${TELOMARE_HVM_RUNNER:-gen-c-big}"
            exec "${self}/bend/run_telomare_hvm.sh" "$@"
          '';
        }}/bin/telomare2";
      };
      apps.lsp = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-lsp";
          text = ''
            export TELOMARE_LSP_VERSION="${lspVersion}"
            exec "${self.packages.${system}.telomare}/bin/telomare-lsp" "$@"
          '';
        }}/bin/telomare-lsp";
      };
      apps.format-lint = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-format-lint-check";
          runtimeInputs = [
            pkgs.diffutils
            pkgs.git
            # Use the project's GHC 9.6 tools so format-lint matches the
            # hlint/stylish-haskell that the devShell and CI use.
            pkgs.haskell.packages.ghc96.hlint
            pkgs.haskell.packages.ghc96.stylish-haskell
          ];
          text = ''
            mapfile -t hs_files < <(git ls-files '*.hs')
            tmp_dir="$(mktemp -d)"
            trap 'rm -rf "$tmp_dir"' EXIT

            format_status=0
            if [ "''${#hs_files[@]}" -gt 0 ]; then
              for hs_file in "''${hs_files[@]}"; do
                formatted_file="$tmp_dir/$(basename "$hs_file")"
                stylish-haskell "$hs_file" > "$formatted_file"

                if ! cmp -s "$hs_file" "$formatted_file"; then
                  printf '%s needs formatting. Suggested diff:\n' "$hs_file"
                  diff -u "$hs_file" "$formatted_file" || true
                  format_status=1
                fi
              done
            fi

            lint_status=0
            hlint . || lint_status=$?

            if [ "$format_status" -ne 0 ]; then
              printf 'Formatting check failed\n'
            fi
            if [ "$lint_status" -ne 0 ]; then
              printf 'Linting check failed\n'
            fi
            if [ "$format_status" -ne 0 ] || [ "$lint_status" -ne 0 ]; then
              exit 1
            fi

            printf 'Formatting and linting are OK\n'
          '';
        }}/bin/telomare-format-lint-check";
      };
      apps.push-cachix = {
        type = "app";
        program = "${pkgs.writeShellApplication {
          name = "telomare-push-cachix";
          runtimeInputs = [
            pkgs.cachix
            pkgs.jq
            pkgs.nixVersions.nix_2_31
          ];
          text = ''
            cache_name=telomare
            tmp_dir="$(mktemp -d)"
            trap 'rm -rf "$tmp_dir"' EXIT

            direct_paths="$tmp_dir/direct-paths"
            closure_paths="$tmp_dir/closure-paths"
            key_paths="$tmp_dir/key-paths"
            : > "$direct_paths"
            : > "$key_paths"

            build_target() {
              local target="$1"
              local output_path
              printf 'Building %s\n' "$target"
              output_path="$(nix build --no-link --print-out-paths "$target")"
              printf '%s\n' "$output_path" >> "$direct_paths"
              printf '%s\n' "$output_path" >> "$key_paths"
            }

            build_target ".#packages.${system}.default"
            build_target ".#checks.${system}.default"
            build_target ".#devShells.${system}.default"

            printf 'Building nix develop environment closure\n'
            dev_env_profile="$tmp_dir/dev-env-profile"
            nix print-dev-env --profile "$dev_env_profile" ".#devShells.${system}.default" >/dev/null
            dev_env_path="$(nix path-info "$dev_env_profile")"
            printf '%s\n' "$dev_env_path" >> "$direct_paths"
            printf '%s\n' "$dev_env_path" >> "$key_paths"

            printf 'Building legacy default.nix with nix-build\n'
            legacy_build_path="$(nix-build --no-out-link)"
            printf '%s\n' "$legacy_build_path" >> "$direct_paths"
            printf '%s\n' "$legacy_build_path" >> "$key_paths"

            printf 'Building legacy shell.nix closure with nix-store\n'
            legacy_shell_drv="$(nix-instantiate shell.nix)"
            legacy_shell_path="$(nix-store --realise "$legacy_shell_drv")"
            printf '%s\n' "$legacy_shell_path" >> "$direct_paths"
            printf '%s\n' "$legacy_shell_path" >> "$key_paths"
            nix-store --query --requisites --include-outputs "$legacy_shell_drv" >> "$direct_paths"

            printf 'Archiving flake source and inputs\n'
            nix flake archive --json \
              | jq -r '.. | objects | .path? // empty' \
              >> "$direct_paths"

            for app_name in default repl evaluare lsp format-lint; do
              app_program="$(nix eval --raw ".#apps.${system}.$app_name.program")"
              if [[ "$app_program" =~ ^(/nix/store/[^/]+) ]]; then
                printf '%s\n' "''${BASH_REMATCH[1]}" >> "$direct_paths"
              fi
            done

            sort -u "$direct_paths" \
              | xargs nix path-info --recursive \
              | sort -u \
              > "$closure_paths"

            path_count="$(wc -l < "$closure_paths")"
            printf 'Pushing %s store paths to Cachix cache %s\n' "$path_count" "$cache_name"
            cachix push "$cache_name" < "$closure_paths"

            printf 'Verifying key paths in Cachix cache %s\n' "$cache_name"
            while IFS= read -r key_path; do
              printf 'Verifying %s\n' "$key_path"
              nix path-info --store "https://$cache_name.cachix.org" "$key_path" >/dev/null
            done < "$key_paths"

            printf 'Cachix push completed for cache %s\n' "$cache_name"
          '';
        }}/bin/telomare-push-cachix";
      };

      checks = self'.packages // {
        # Type-check the telomare3 Agda specification (--safe, no
        # postulates). Copied out of the store because agda writes .agdai
        # interface files next to the sources.
        telomare3-spec = pkgs.runCommand "telomare3-spec"
          {
            nativeBuildInputs = [ agdaWithStdlib pkgs.glibcLocales ];
            # agda needs a UTF-8 locale for its Unicode-heavy output/sources
            LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
            LC_ALL = "en_US.UTF-8";
          } ''
            cp -r ${./telomare3/spec} spec
            chmod -R u+w spec
            cd spec
            agda --safe Everything.agda
            touch $out
          '';
      };
    };
  };
}
