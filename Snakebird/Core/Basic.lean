import Snakebird.Core.Extensions

inductive Dir
  | up
  | down
  | right
  | left
deriving BEq, Inhabited

def Dir.all : List Dir := [Dir.up, Dir.down, Dir.right, Dir.left]

def Dir.opposite : Dir → Dir
  | up    => down
  | down  => up
  | right => left
  | left  => right

structure Pos where
  x : Int
  y : Int
deriving BEq, Inhabited

def Pos.move (p : Pos) : Dir → Pos
  | .up    => { p .. with y := p.y + 1 }
  | .down  => { p .. with y := p.y - 1 }  
  | .right => { p .. with x := p.x + 1 }
  | .left  => { p .. with x := p.x - 1 }

def Pos.isNeighbor (p₁ p₂ : Pos) : Bool :=
  let Δx := (p₁.x - p₂.x).abs
  let Δy := (p₁.y - p₂.y).abs
  Δx + Δy == 1

instance : ToString Pos where
  toString p := s!"[x:{p.x},y:{p.y}]"