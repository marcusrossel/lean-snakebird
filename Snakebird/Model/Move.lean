import Snakebird.Model.Game

structure Move where
  snakeIdx : Nat
  dir : Dir

inductive Move.Error.Kind
  | unknownSnake   
  | blockedByRock  
  | blockedBySaw   
  | blockedByWater 
  | blockedBySnake (barrierIdx : Nat)
  | fellInWater    
  | fellOnSaw      

structure Move.Error where
  snakeIdx : Nat
  kind : Error.Kind

instance : ToString Move.Error where
  toString e :=
  match e.kind with
  | .unknownSnake              => s!"Unknown Snake: \"{e.snakeIdx}\""
  | .blockedByRock             => s!"Move blocked by rock."
  | .blockedBySaw              => s!"Move blocked by saw."
  | .blockedByWater            => s!"Move blocked by water."
  | .blockedBySnake barrierIdx =>
    if e.snakeIdx == barrierIdx 
    then s!"Move blocked by snake itself."
    else s!"Move blocked by snake {barrierIdx}."
  | .fellInWater               => s!"Invalid move: Snake {e.snakeIdx} would fall into the water."
  | .fellOnSaw                 => s!"Invalid move: Snake {e.snakeIdx} would fall onto a saw."

inductive Move.Result
  | success (g : Game)
  | failure (e : List Move.Error)
deriving Inhabited
