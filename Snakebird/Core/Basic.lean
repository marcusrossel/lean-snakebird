import Snakebird.Core.Extensions

inductive Dir
  | up
  | down
  | right
  | left
  deriving DecidableEq, Inhabited

def Dir.all : List Dir := [.up, .down, .right, .left]

def Dir.opposite : Dir → Dir
  | up    => down
  | down  => up
  | right => left
  | left  => right

structure Pos where
  x : Int
  y : Int
  deriving DecidableEq, Inhabited

def Pos.move (p : Pos) : Dir → Pos
  | .up    => { p with y := p.y + 1 }
  | .down  => { p with y := p.y - 1 }
  | .right => { p with x := p.x + 1 }
  | .left  => { p with x := p.x - 1 }

def Pos.isNeighbor (p₁ p₂ : Pos) : Bool :=
  let Δx := (p₁.x - p₂.x).natAbs
  let Δy := (p₁.y - p₂.y).natAbs
  Δx + Δy == 1

instance : ToString Pos where
  toString p := s!"⟨{p.x}, {p.y}⟩"
