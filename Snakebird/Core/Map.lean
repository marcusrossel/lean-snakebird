import Snakebird.Core.Basic

structure Map where
  goal  : Pos
  rocks : List Pos
  fruit : List Pos
  saws  : List Pos
  -- Water level is at y = 0.
deriving Inhabited

namespace Map

-- Positions a snake can stand on.
def isStablePos (m : Map) (p : Pos) : Bool :=
  (m.rocks ++ m.fruit).contains p

def goalIsUnlocked (m : Map) : Bool := 
  m.fruit.isEmpty

end Map