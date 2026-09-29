# The maintainer's cache push. Scripts get a syntax check only: corepkgs'
# `writeShellApplication` refers to a `shellcheck-minimal` that the package set
# does not define, so the default check phase cannot evaluate, and ShellCheck
# itself came from the Haskell package set, which this flake no longer has.
{
  pkgs,
  devShellNames,
  checkNames,
  appNames,
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
          runHook postCheck
        '';
      }
    );

  # Neither cachix nor nix is pinned here: the ekapkgs snapshot has no cachix
  # that builds (its amazonka 2.0 dependencies predate GHC 9.8), corepkgs'
  # Nix is a from-source build nothing else needs, and this is a maintainer's
  # tool, so it uses the cachix already installed for `cachix use telomare`
  # and the nix the flake is being used with.
  pushCachix = mkScript {
    name = "telomare-push-cachix";
    runtimeInputs = [ pkgs.jq ];
    text = ''
      for tool in cachix nix; do
        if ! command -v "$tool" >/dev/null; then
          echo "$tool not found on PATH: install it (https://docs.cachix.org) and log in first" >&2
          exit 1
        fi
      done
      cache_name=telomare
      tmp_dir="$(mktemp -d)"
      trap 'rm -rf "$tmp_dir"' EXIT

      direct_paths="$tmp_dir/direct-paths"
      closure_paths="$tmp_dir/closure-paths"
      key_paths="$tmp_dir/key-paths"
      : > "$direct_paths"
      : > "$key_paths"

      # Everything built here stays a garbage collector root until the push
      # is over: Nix may collect garbage while this runs (Determinate Nix
      # does on its own when the disk runs low), and an unrooted output is
      # garbage as soon as it is built.
      roots="$tmp_dir/roots"
      mkdir "$roots"

      build_target() {
        local target="$1"
        local output_path
        printf 'Building %s\n' "$target"
        output_path="$(nix build --out-link "$(mktemp -u "$roots/XXXXXXXX")" \
          --print-out-paths "$target")"
        printf '%s\n' "$output_path" >> "$direct_paths"
        printf '%s\n' "$output_path" >> "$key_paths"
      }

      build_target ".#packages.${system}.default"

      # Every check, so that `nix flake check` in CI substitutes all of them.
      for check_name in ${lib.escapeShellArgs checkNames}; do
        build_target ".#checks.${system}.$check_name"
      done

      # Include every declared shell and the environment used by nix develop.
      for shell_name in ${lib.escapeShellArgs devShellNames}; do
        shell_target=".#devShells.${system}.$shell_name"
        build_target "$shell_target"
        printf 'Building nix develop environment closure for %s\n' "$shell_name"
        dev_env_profile="$tmp_dir/dev-env-profile-$shell_name"
        nix print-dev-env --profile "$dev_env_profile" "$shell_target" >/dev/null
        dev_env_path="$(nix path-info "$dev_env_profile")"
        printf '%s\n' "$dev_env_path" >> "$direct_paths"
        printf '%s\n' "$dev_env_path" >> "$key_paths"
      done

      printf 'Archiving flake source and inputs\n'
      source_count=0
      while IFS= read -r source_path; do
        source_count=$((source_count + 1))
        nix-store --realise --add-root "$roots/source-$source_count" \
          "$source_path" >/dev/null
        printf '%s\n' "$source_path" >> "$direct_paths"
      done < <(nix flake archive --json | jq -r '.. | objects | .path? // empty')

      # Every app, built from the derivation its program comes from: an
      # evaluated program path is merely a name, and `nix path-info`
      # rejects it until that derivation is built.
      for app_name in ${lib.escapeShellArgs appNames}; do
        app_drv="$(nix eval --raw ".#apps.${system}.$app_name.program" \
          --apply 'program: builtins.head (builtins.attrNames (builtins.getContext program))')"
        build_target "$app_drv^*"
      done

      sort -u "$direct_paths" \
        | xargs nix path-info --recursive \
        | sort -u \
        > "$closure_paths"

      path_count="$(wc -l < "$closure_paths")"
      printf 'Pushing %s store paths to Cachix cache %s\n' "$path_count" "$cache_name"
      cachix push "$cache_name" < "$closure_paths"

      # A lookup that missed before the push is remembered by Nix for an
      # hour (narinfo-cache-negative-ttl), so verify without that memory.
      printf 'Verifying key paths in Cachix cache %s\n' "$cache_name"
      while IFS= read -r key_path; do
        printf 'Verifying %s\n' "$key_path"
        nix path-info --store "https://$cache_name.cachix.org" \
          --narinfo-cache-negative-ttl 0 "$key_path" >/dev/null
      done < "$key_paths"

      printf 'Cachix push completed for cache %s\n' "$cache_name"
    '';
  };
in
{
  inherit pushCachix;
}
