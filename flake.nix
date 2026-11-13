{
  description = "Lean 4 project using nixpkgs leanPackages (Mathlib prebuilt)";

  inputs = {
    # flake.lock is the real pin. Mathlib is fetched prebuilt from cache.nixos.org
    # and only one nixpkgs rev is cached at a time, so before running
    # `nix flake update nixpkgs`, check `nix build` still substitutes.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs = inputs @ { nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "aarch64-darwin" "aarch64-linux" "x86_64-darwin" "x86_64-linux" ];

      perSystem = { pkgs, ... }:
        let
          lp = pkgs.leanPackages;
          # Mathlib plus its transitive Lean deps (batteries, aesop, Qq, ...).
          deps = [ lp.mathlib ] ++ lp.mathlib.passthru.allLeanDeps;
          # Tells `lake build` to take these deps from the nix store instead of
          # cloning them from git (lake never needs network).
          lakeOverrides = pkgs.writeText "lake-overrides.json" (builtins.toJSON {
            schemaVersion = "1.2.0";
            packages = map (d: {
              type = "path";
              name = d.passthru.lakePackageName or d.pname;
              inherited = false;
              dir = d.outPath;
            }) deps;
          });
          # Lake has no env var for package overrides, only `--packages=<json>`,
          # so shadow `lake` in the dev shell with one that always passes the
          # store paths. Keeps `lake build` / `lake serve` (the LSP) flag-free.
          lake = pkgs.writeShellScriptBin "lake" ''
            real="${lp.lean4}/bin/lake"
            case "''${1-}" in
              build | query | serve | lean | env | exe | check-build)
                if [[ -n "''${LAKE_OVERRIDES-}" && " $* " != *--packages* ]]; then
                  exec "$real" "$1" --packages="$LAKE_OVERRIDES" "''${@:2}"
                fi
                ;;
            esac
            exec "$real" "$@"
          '';
        in
        {
          packages.default = lp.buildLakePackage {
            pname = "Example";
            version = "0.1.0";
            src = ./.;
            leanDeps = [ lp.mathlib ];
          };

          devShells.default = pkgs.mkShell {
            # z3 is the oracle the checker talks to over SMT-LIB text (book/ Ch 3).
            packages = [ lake lp.lean4 pkgs.z3 ];
            # The LSP / plain `lean` resolve Mathlib straight from the store.
            LEAN_PATH = pkgs.lib.concatStringsSep ":"
              (map (d: "${d}/.lake/build/lib/lean") deps);
            LAKE_OVERRIDES = "${lakeOverrides}";
            # Mathlib's post-update hook would run `lake exe cache get`; its
            # .ltar files fail to unpack with nixpkgs' leantar, and the oleans
            # come from the store anyway.
            MATHLIB_NO_CACHE_ON_UPDATE = "1";
          };
        };
    };

  # --- Flake Local Nix Configuration -------------------------------
  # Substitute the Mathlib closure from our own cache instead of rebuilding it
  # (push with `just push`). Nix asks once before trusting a new substituter;
  # `accept-flake-config = true` in nix.conf skips the prompt.
  nixConfig = {
    extra-substituters = [ "https://lean4math.cachix.org" ];
    extra-trusted-public-keys = [ "lean4math.cachix.org-1:lo4ur+c1M7f5i9VqM0YzEdZ1KpzXdlVqmFfrqfxmY5g=" ];
  };
}
