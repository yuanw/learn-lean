import Lake
open Lake DSL

package Example

require "leanprover-community" / "mathlib" @ git "main"

@[default_target]
lean_lib Example
