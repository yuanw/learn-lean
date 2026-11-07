# Push build outputs (incl. the Mathlib closure) to https://app.cachix.org/cache/lean4math
# Needs CACHIX_AUTH_TOKEN in the env, or a prior `cachix authtoken ...`.
push:
    nix build --no-link --print-out-paths .#default | cachix push lean4math
    nix develop --profile .direnv/push-profile -c true
    cachix push lean4math .direnv/push-profile
