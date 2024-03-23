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
  x : Nat
  y : Nat
  deriving DecidableEq, Inhabited

def Pos.move (p : Pos) : Dir → Pos
  | .up    => { p with y := p.y + 1 }
  | .down  => { p with y := p.y - 1 }
  | .right => { p with x := p.x + 1 }
  | .left  => { p with x := p.x - 1 }

def Pos.isNeighbor (p₁ p₂ : Pos) : Bool :=
  (p₁.x.dist p₂.x) + (p₁.y.dist p₂.y) == 1

instance : ToString Pos where
  toString p := s!"⟨{p.x}, {p.y}⟩"
