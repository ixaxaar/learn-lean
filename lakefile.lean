import Lake
open Lake DSL

package "learn_lean" where
  -- add package configuration options here

lean_lib «LearnLean» where
  -- add library configuration options here

@[default_target]
lean_exe "learn_lean" where
  root := `Main
