import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.30.0"

package «lean4-axiomatic» {
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    -- This linter rule can make proof readability harder in some cases.
    ⟨`weak.linter.tacticAnalysis.introMerge, false⟩,
  ]
}

lean_lib Lean4Axiomatic {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4-axiomatic» {
  root := `Main
}
