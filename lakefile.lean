import Lake
open Lake DSL

package lean_snakebird

lean_lib Snakebird

@[default_target]
lean_exe snakebird where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "v4.8.0-rc1"
