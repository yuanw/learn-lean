import Lake
open Lake DSL

package Example

-- Tag matches lean-toolchain; mathlib4's default branch is `master`, not `main`.
require "leanprover-community" / "mathlib" @ git "v4.35.0"

@[default_target]
lean_lib Example
