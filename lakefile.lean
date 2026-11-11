import Lake
open Lake DSL

package Example

-- Tag matches lean-toolchain; mathlib4's default branch is `master`, not `main`.
require "leanprover-community" / "mathlib" @ git "v4.35.0"

@[default_target]
lean_lib Example where
  -- Only Example/*.lean (Example/NNG.lean); the scratch Example.lean is gone.
  globs := #[.submodules `Example]

-- Core linters for the checker sources. `linter.all` turns on every registered linter
-- (unused variables, missing docstrings, deprecated usage, redundant visibility, …) and
-- `warningAsError` makes `lake build` fail on any of them: the book's code cannot accumulate
-- style debt between chapters. Deliberately scoped to Sprite/ only -- Example/NNG.lean holds
-- Number Game proofs and is nobody's style exemplar.
def lintArgs : Array String := #["-Dlinter.all=true", "-DwarningAsError=true"]

-- The tutorial's checker. Deliberately imports neither Mathlib nor Lean: the edit loop
-- has to stay around a second. See book/.
@[default_target]
lean_lib Sprite where
  globs := #[.andSubmodules `Sprite]
  moreLeanArgs := lintArgs

@[default_target]
lean_exe sprite where
  root := `Sprite.Main
  moreLeanArgs := lintArgs
