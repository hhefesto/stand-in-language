# The shell apps and the format/lint check, as they were in the flake before
# the move to ekapkgs. Scripts are linted with shellcheck explicitly:
# corepkgs' `writeShellApplication` refers to a `shellcheck-minimal` that the
# package set does not define, so the default check phase cannot evaluate.
# `gitMinimal` rather than `git`: the scripts only list and read tracked files,
# and the full git brings its manual (asciidoc, perl) into the closure.
{
  pkgs,
  src,
  lspVersion,
  telomare,
  tools,
  executables,
}:
let
  inherit (pkgs) lib;
  system = pkgs.stdenv.hostPlatform.system;

  mkScript =
    args:
    pkgs.writeShellApplication (
      args
      // {
        checkPhase = ''
          runHook preCheck
          ${pkgs.stdenv.shellDryRun} "$target"
          ${lib.getExe executables.shellcheck} "$target"
          runHook postCheck
        '';
      }
    );

  # `telomare-lsp` reports the checkout's timestamp as its version; the flake
  # knows it, so hand it over. The binary shells out to git for the same
  # purpose, hence git on its PATH.
  telomareLsp = mkScript {
    name = "telomare-lsp";
    runtimeInputs = [ pkgs.gitMinimal ];
    text = ''
      export TELOMARE_LSP_VERSION="${lspVersion}"
      exec "${telomare}/bin/telomare-lsp" "$@"
    '';
  };

  # Format and lint the tracked Haskell files. `--check` reports needed
  # changes without applying them; otherwise formatting is applied in
  # place. Scoping to `git ls-files` is what keeps this identical to CI:
  # recursing over `.` locally wanders into untracked trees like
  # .direnv/ and dist-newstyle/ and aborts on read-only store files.
  telomareFormat = mkScript {
    name = "telomare-format";
    runtimeInputs = [
      pkgs.diffutils
      pkgs.gitMinimal
      tools.hlint
      tools.stylish-haskell
    ];
    text = ''
      mapfile -t hs_files < <(git ls-files '*.hs')
      if [ "''${#hs_files[@]}" -eq 0 ]; then
        echo "No tracked Haskell files found"
        exit 0
      fi

      format_status=0
      if [ "''${1:-}" = "--check" ]; then
        tmp_dir="$(mktemp -d)"
        trap 'rm -rf "$tmp_dir"' EXIT
        for hs_file in "''${hs_files[@]}"; do
          formatted_file="$tmp_dir/$(basename "$hs_file")"
          stylish-haskell "$hs_file" > "$formatted_file"
          if ! cmp -s "$hs_file" "$formatted_file"; then
            printf '%s needs formatting. Suggested diff:\n' "$hs_file"
            diff -u "$hs_file" "$formatted_file" || true
            format_status=1
          fi
        done
      else
        echo "Formatting ''${#hs_files[@]} tracked Haskell files"
        stylish-haskell -i "''${hs_files[@]}"
      fi

      lint_status=0
      hlint "''${hs_files[@]}" || lint_status=$?

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
  };

  telomareFormatLint = pkgs.writeShellScriptBin "telomare-format-lint-check" ''
    exec ${telomareFormat}/bin/telomare-format --check
  '';

  # `nix flake check` verifies formatting and linting over the flake source,
  # which is the tracked files — the same set `nix run .#format` and the CI
  # format/lint steps see.
  formatLintCheck =
    pkgs.runCommand "telomare-format-lint-check"
      {
        nativeBuildInputs = [
          pkgs.diffutils
          pkgs.findutils
          tools.hlint
          tools.stylish-haskell
        ];
        LC_ALL = "C.UTF-8";
      }
      ''
        cp -r ${src} source
        chmod -R u+w source
        cd source
        find . -type f -name '*.hs' -print0 | xargs -0 stylish-haskell -i
        cd ..
        if ! diff -ru ${src} source; then
          echo "Formatting check failed: stylish-haskell has the suggestions diffed above."
          echo "Run 'nix run .#format' to apply them."
          exit 1
        fi
        cd source
        if ! find . -type f -name '*.hs' -print0 | xargs -0 hlint; then
          echo "Linting check failed: fix the hints above or add exceptions to .hlint.yaml."
          exit 1
        fi
        touch $out
      '';

  pushCachix = mkScript {
    name = "telomare-push-cachix";
    runtimeInputs = [
      executables.cachix
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

      # The shell apps. Naming them by interpolation rather than by
      # `nix eval` of `apps.<name>.program` makes them build inputs of
      # this script, so they are realised whenever it runs; an evaluated
      # path is merely a name, and `nix path-info` rejects it when the
      # derivation behind it has not been built. The `default` and `repl`
      # apps need no entry: they live in the package built above.
      printf 'Including the shell apps\n'
      printf '%s\n' \
        "${telomareLsp}" \
        "${telomareFormat}" \
        "${telomareFormatLint}" \
        >> "$direct_paths"

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
  };
in
{
  inherit
    telomareLsp
    telomareFormat
    telomareFormatLint
    formatLintCheck
    pushCachix
    ;
}
