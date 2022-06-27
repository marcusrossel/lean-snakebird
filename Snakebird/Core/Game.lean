import Snakebird.Core.Snake
import Snakebird.Core.Map

structure Game where
  map : Map
  snakes : List Snake
deriving Inhabited

namespace Game

def isSnakePos (g : Game) (p : Pos) : Bool :=
  g.snakes.any (·.positions.contains p)

partial def floatingSnakes (g : Game) : List Nat :=
  let allSnakes := g.snakes.enum
  let initFloating := allSnakes.filter fun (_, s) => 
    !s.below.any g.map.isStablePos
  transFloating allSnakes initFloating |>.map Prod.fst
where 
  transFloating (all : List $ Nat × Snake) (floating : List $ Nat × Snake) : List (Nat × Snake) :=
    let stableSnakes := all.filterMap fun (i, s) => 
      if floating.any (·.fst == i) then none else some s
    let stableFields := stableSnakes.map Snake.positions |>.join
    let newStable := floating.filter fun (_, s) => 
      s.below.any (stableFields.contains ·)
    if newStable.isEmpty then floating else transFloating all (floating.subtract newStable)

def isCompleted (g : Game) : Bool :=
  g.map.fruit.isEmpty && g.snakes.isEmpty

end Game