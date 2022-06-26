import Snakebird.Interface

open Menu (menu) 
open Play (play)

partial def main : IO Unit := do
  match ← Menu.menu 0 with
  | none => return
  | some levelIdx => 
    play <| Play.State.fromGame (levels.get! levelIdx)
    main