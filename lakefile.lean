import Lake
open Lake DSL

package «lean4-axiomatic» {
  -- add package configuration options here
}

lean_lib Lean4Axiomatic {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4-axiomatic» {
  root := `Main
}
