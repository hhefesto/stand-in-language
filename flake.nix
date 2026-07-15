{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      perSystem = { self', system, pkgs, ... }:
        let
          agdaWithStdlib = pkgs.agda.withPackages (p: [ p.standard-library ]);
          hp = pkgs.haskell.packages.ghc96;
          telomare = hp.mkDerivation {
            pname = "telomare";
            version = "0.1.0.0";
            src = ./.;
            isLibrary = true;
            isExecutable = true;
            libraryHaskellDepends = with hp; [
              base
              bytestring
              containers
              cryptonite
              data-fix
              deepseq
              deriving-compat
              dlist
              filepath
              free
              genvalidity
              lens
              megaparsec
              memory
              mtl
              recursion-schemes
              strict
              transformers
              utf8-string
              validity
            ];
            executableHaskellDepends = with hp; [
              base
              containers
              optparse-applicative
            ];
            testHaskellDepends = with hp; [
              base
              containers
              directory
              free
              QuickCheck
            ];
            testToolDepends = [ pkgs.bend ];
            preCheck = ''
              export TELOMARE_BEND=${pkgs.bend}/bin/bend
            '';
            doCheck = true;
            homepage = "https://github.com/hhefesto/stand-in-language";
            description = "Total language runtime with knowable bounds";
            license = pkgs.lib.licenses.asl20;
            mainProgram = "telomare";
          };
        in {
          packages = {
            default = telomare;
            inherit telomare;
          };

          devShells.default = pkgs.mkShell {
            nativeBuildInputs = [
              agdaWithStdlib
              hp.cabal-install
              hp.haskell-language-server
              pkgs.bend
            ];
          };

          apps.default = {
            type = "app";
            program = self'.packages.telomare + "/bin/telomare";
            meta.description = "Compile and run a typed affine .tel2 program";
          };

          apps.bend = {
            type = "app";
            program = "${pkgs.writeShellApplication {
              name = "telomare-bend-run";
              runtimeInputs = [
                pkgs.bend
                pkgs.coreutils
                self'.packages.telomare
              ];
              text = ''
                if [ "$#" -ne 3 ]; then
                  printf 'usage: telomare-bend-run init|step PROGRAM.tel2 BEND_INPUT\n' >&2
                  exit 2
                fi

                entry="$1"
                program="$2"
                input="$3"
                case "$entry" in
                  init|step) ;;
                  *)
                    printf 'entry must be init or step\n' >&2
                    exit 2
                    ;;
                esac

                tmp_dir="$(mktemp -d)"
                trap 'rm -rf "$tmp_dir"' EXIT

                telomare --emit-transport "$entry" "$program" > "$tmp_dir/program.transport"
                telomare-bend "$tmp_dir/program.transport" > "$tmp_dir/program.bend"
                printf '\ndef main():\n  return telomare_run(%s)\n' "$input" >> "$tmp_dir/program.bend"
                timeout 30s bend run-c "$tmp_dir/program.bend"
              '';
            }}/bin/telomare-bend-run";
            meta.description = "Compile and run a .tel2 entry with the Bend backend";
          };

          apps.format-lint = {
            type = "app";
            program = "${pkgs.writeShellApplication {
              name = "telomare-format-lint-check";
              runtimeInputs = [
                pkgs.diffutils
                pkgs.git
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
                    [ -f "$hs_file" ] || continue
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
            meta.description = "Check Haskell formatting and hlint hints";
          };

          checks = {
            inherit telomare;
            telomare-spec = pkgs.runCommand "telomare-spec"
              {
                nativeBuildInputs = [ agdaWithStdlib pkgs.glibcLocales ];
                LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
                LC_ALL = "en_US.UTF-8";
              } ''
                cp -r ${./spec} spec
                chmod -R u+w spec
                cd spec
                agda --safe Everything.agda
                touch $out
              '';
          };
        };
    };
}
