# learn-lean

Tutorial in progress: a refinement type checker for sprite, written chapter by chapter in
[book/](book) — plan in [PLAN.md](PLAN.md).

Lean 4 + Mathlib, all from nixpkgs `leanPackages`. Mathlib is a prebuilt
download (no compile), and Lake never needs the network: the dev shell wraps
`lake` so every build gets `--packages=$LAKE_OVERRIDES`, which points the deps
at the store.

```sh
direnv allow
lake build                              # incremental build
lean Sprite/Cli.lean                    # check one file (this is what the LSP does)
nix build                               # reproducible build of the package
```

Editing: the Lean VS Code extension needs `lean` and `LEAN_PATH` from this
shell, so start the editor from a direnv'd terminal.

Adding deps: if `pkgs.leanPackages` has it, add `lp.<name>` to `leanDeps` (for
`nix build`) and to `deps` (for the dev shell), plus a `require` line in
`lakefile.lean`. Otherwise you're back to Lake's git deps and a real
`lake-manifest.json`.

`lake update` is not needed (the manifest exists only so plain Lake tooling is
happy); the shell sets `MATHLIB_NO_CACHE_ON_UPDATE=1` so it skips Mathlib's
olean cache, which the nix `leantar` cannot unpack.

`nix flake update nixpkgs` moves Mathlib; cache.nixos.org only keeps one rev,
so expect a multi-hour rebuild unless the new rev is already cached.
