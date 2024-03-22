import Lake
open Lake DSL

package lean_snakebird

lean_lib Snakebird

@[default_target]
lean_exe snakebird where
  root := `Main
