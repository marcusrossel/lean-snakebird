import Lake
open Lake DSL

package lean_snakebird 

lean_lib Snakebird 

@[defaultTarget]
lean_exe snakebird where
  root := `Main