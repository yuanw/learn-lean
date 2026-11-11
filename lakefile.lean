import Lake
open Lake DSL

package Example

-- Tag matches lean-toolchain; mathlib4's default branch is `master`, not `main`.
require "leanprover-community" / "mathlib" @ git "v4.35.0"

@[default_target]
lean_lib Example where
  -- Only Example/*.lean (Example/NNG.lean); the scratch Example.lean is gone.
  globs := #[.submodules `Example]

-- The tutorial's checker. Deliberately imports neither Mathlib nor Lean: the edit loop
-- has to stay around a second. See book/.
@[default_target]
lean_lib Sprite where
  globs := #[.andSubmodules `Sprite]

@[default_target]
lean_exe sprite where
  root := `Sprite.Main
