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

  outputs = inputs@{ self, nixpkgs, flake-parts, haskell-flake, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" ];
      imports = [ inputs.haskell-flake.flakeModule ];
      perSystem = { self', system, pkgs, ... }:
        let
          agdaWithStdlib = pkgs.agda.withPackages (p: [ p.standard-library ]);
        in {
          haskellProjects.default = {
            basePackages = pkgs.haskell.packages.ghc96;
            devShell = {
              enable = true;
              tools = hp: {
                inherit (hp) cabal-install haskell-language-server;
              };
              mkShellArgs = {
                nativeBuildInputs = [ agdaWithStdlib ];
              };
            };
          };

          packages.default = self'.packages.telomare;

          apps.default = {
            type = "app";
            program = self'.packages.telomare + "/bin/telomare";
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

          checks = self'.packages // {
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
