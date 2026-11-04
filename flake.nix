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
        in
        {
          packages.default = lp.buildLakePackage {
            pname = "Example";
            version = "0.1.0";
            src = ./.;
            leanDeps = [ lp.mathlib ];
          };

          devShells.default = pkgs.mkShell {
            packages = [ lp.lean4 ];
            # The LSP / plain `lean` resolve Mathlib straight from the store.
            LEAN_PATH = pkgs.lib.concatStringsSep ":"
              (map (d: "${d}/.lake/build/lib/lean") deps);
            LAKE_OVERRIDES = "${lakeOverrides}";
          };
        };
    };
}
