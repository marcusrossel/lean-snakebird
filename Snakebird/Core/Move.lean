import Snakebird.Core.Game

structure Move where
  snakeIdx : Nat
  dir      : Dir

namespace Move

inductive Error.Kind
  | unknownSnake
  | blockedByRock
  | blockedBySaw
  | blockedByWater
  | blockedBySnake (barrierIdx : Nat)
  | fellInWater
  | fellOnSaw

structure Error where
  snakeIdx : Nat
  kind     : Error.Kind

instance : ToString Move.Error where
  toString e :=
    match e.kind with
    | .unknownSnake              => s!"Unknown Snake: \"{e.snakeIdx}\""
    | .blockedByRock             => "Move blocked by rock."
    | .blockedBySaw              => "Move blocked by saw."
    | .blockedByWater            => "Move blocked by water."
    | .blockedBySnake barrierIdx =>
      if e.snakeIdx == barrierIdx
      then "Move blocked by snake itself."
      else s!"Move blocked by snake {barrierIdx}."
    | .fellInWater               => s!"Invalid move: Snake {e.snakeIdx} would fall into the water."
    | .fellOnSaw                 => s!"Invalid move: Snake {e.snakeIdx} would fall onto a saw."

inductive Result
  | success (g : Game)
  | failure (e : List Move.Error)
  deriving Inhabited
