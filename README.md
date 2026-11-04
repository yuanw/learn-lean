# learn-lean

Lean 4 + Mathlib, all from nixpkgs `leanPackages`. Mathlib is a prebuilt
download (no compile), and Lake never needs the network: deps are injected
from the store via `--packages`.

```sh
direnv allow
lake build --packages=$LAKE_OVERRIDES   # incremental build
lean Example.lean                       # check one file (this is what the LSP does)
nix build                               # reproducible build of the package
```

Editing: the Lean VS Code extension needs `lean` and `LEAN_PATH` from this
shell, so start the editor from a direnv'd terminal.

Adding deps: if `pkgs.leanPackages` has it, add `lp.<name>` to `leanDeps` (for
`nix build`) and to `deps` (for the dev shell), plus a `require` line in
`lakefile.lean`. Otherwise you're back to Lake's git deps and a real
`lake-manifest.json`.

`nix flake update nixpkgs` moves Mathlib; cache.nixos.org only keeps one rev,
so expect a multi-hour rebuild unless the new rev is already cached.
