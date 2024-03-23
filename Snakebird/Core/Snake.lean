import Snakebird.Core.Basic

structure Snake where
  head : Pos
  body : List Pos
  deriving DecidableEq, Inhabited

namespace Snake

def positions (s : Snake) : List Pos :=
  s.head :: s.body

def tail (s : Snake) : Pos :=
  s.positions.getLast (by simp [positions])

def move (s : Snake) (d : Dir) : Snake where
  head := s.head.move d
  body := (s.head :: s.body).dropLast

def shift (s : Snake) (d : Dir) : Snake where
  head := s.head.move d
  body := s.body.map (.move · d)

def isCoherent (s : Snake) : Bool := Id.run do
  unless s.positions.Nodup do return false
  let neighbors := s.positions.zip s.positions.rotateRight
  return neighbors.dropLast.all fun (p₁, p₂) => p₁.isNeighbor p₂

-- Positions that lie directly below the snake.
-- These may partially overlap with the snake itself.
def below (s : Snake) : List Pos :=
  (s.shift .down).positions

end Snake
