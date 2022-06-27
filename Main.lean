import Snakebird.Interface

open Menu (menu)
open Instructions (instructions) 
open Play (play)

partial def main : IO Unit := do
  match ← menu with
  | .exit => return
  | .instructions => instructions; main
  | .level levelIdx => 
    play <| Play.State.fromGame (levels.get! levelIdx) (levelNumber := levelIdx)
    main