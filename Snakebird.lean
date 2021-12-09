import Lean

def List.isUnique [BEq α] (l : List α) : Bool :=
  l.length == l.eraseDups.length

def List.indices (l : List α) : List Nat :=
  l.enum.map Prod.fst

def List.indicesWhere' (l : List α) (p : Nat → α → Bool) : List Nat :=
  l.enum.filterMap λ (i, a) => if p i a then i else none

def List.indicesWhere (l : List α) (p : α → Bool) : List Nat :=
  l.indicesWhere' (λ _ a => p a)

def Int.abs (i : Int) : Int :=
  if i < 0 then -i else i

/- --------------------------------------------------------------------- -/

inductive Dir -- Direction
  | up
  | down
  | right
  | left

structure Pos where -- Position
  x : Int
  y : Int
deriving BEq

def Pos.move (p : Pos) : Dir → Pos
  | Dir.up    => { p .. with y := p.y + 1 }
  | Dir.down  => { p .. with y := p.y - 1 }  
  | Dir.right => { p .. with x := p.x + 1 }
  | Dir.left  => { p .. with x := p.x - 1 }

def Pos.isNeighbor (p₁ p₂ : Pos) : Bool :=
  let Δx := (p₁.x - p₂.x).abs
  let Δy := (p₁.y - p₂.y).abs
  Δx + Δy == 1

structure Snake where
  head : Pos
  tail : List Pos
deriving BEq

namespace Snake

def fields (s : Snake) : List Pos := 
  s.head :: s.tail

theorem fields_ne_nil (s : Snake) : s.fields ≠ [] := by 
  simp [fields]

def butt (s : Snake) : Pos := 
  s.fields.getLast (Snake.fields_ne_nil _)

def move (s : Snake) (d : Dir) : Snake := {
  head := s.head.move d,
  tail := (s.head :: s.tail).dropLast
}

def shift (s : Snake) (d : Dir) : Snake := {
  head := s.head.move d,
  tail := s.tail.map (Pos.move · d)
}

def isCoherent (s : Snake) : Bool :=
  let c₁ := s.fields.isUnique
  let neighbors := s.fields.zip s.fields.rotateRight
  let c₂ := neighbors.dropLast.all λ (p₁, p₂) => p₁.isNeighbor p₂
  c₁ && c₂

-- Positions that lie directly below the snake.
-- These may partially overlap with the snake itself.
def below (s : Snake) : List Pos :=
  (s.shift Dir.down).fields

end Snake

structure Map where
  goal  : Pos
  rocks : List Pos
  fruit : List Pos
  saws  : List Pos
  -- Water level is at y = 0.
deriving BEq

namespace Map

-- Positions a snake can stand on.
def isPlatformPos (m : Map) (p : Pos) : Bool :=
  (m.rocks ++ m.fruit).contains p

def goalIsUnlocked (m : Map) : Bool := 
  m.fruit.isEmpty

end Map

structure Game where
  map : Map
  snakes : List Snake
  snakeHasDied : Bool
deriving BEq

namespace Game

def isSnakeField (g : Game) (p : Pos) : Bool :=
  g.snakes.any (·.fields.contains p)

partial def floatingSnakes (g : Game) : List Nat := do
  let onPlatform := g.snakes.indicesWhere (·.below.any g.map.isPlatformPos)
  let stable := stableSnakes g onPlatform
  return g.snakes.indices.filter (stable.contains ·)
where 
  stableSnakes (g : Game) (stable : List Nat) : List Nat :=
    let snakes := stable.filterMap (g.snakes.get? ·) 
    let new := g.snakes.indicesWhere' λ i s => stable.notElem i && (s.below.any λ b => snakes.any (·.fields.contains b))
    if new.isEmpty then stable else stableSnakes g (stable ++ new)

-- The list of snakes that also need to move, if the snake at a given
-- index moves in a given direction.
partial def snakesLinkedToMove (g : Game) (idx : Nat) (d : Dir) : List Nat :=
  match g.snakes.get? idx with
  | none => []
  | some s => 
    let h' := s.head.move d
    let is := g.snakes.indicesWhere (·.fields.contains h')
    is ++ (is.map λ i => snakesLinkedToShift g i d).join
where 
  snakesLinkedToShift (g : Game) (idx : Nat) (d : Dir) : List Nat :=
    match g.snakes.get? idx with
    | none => []
    | some s =>  
      let f' := (s.shift d).fields
      let idxs := g.snakes.indicesWhere λ s' => s'.fields.any (f'.contains ·)
      let idxs' := idxs.erase idx -- We have to remove the snake in consideration, otherwise we can get infinite recursion.
      idxs' ++ (idxs'.map λ i => snakesLinkedToShift g i d).join 

inductive MoveError 
  | unknownSnake   (idx : Nat)
  | blockedByRock  (idx : Nat)
  | blockedBySaw   (idx : Nat)
  | blockedByWater (idx : Nat)
  | blockedBySnake (idx : Nat) (barrierIdx : Nat)
  | fellInWater    (idx : Nat)
  | fellOnSaw      (idx : Nat)

inductive MoveResult
  | success (g : Game)
  | failure (e : List MoveError)
deriving Inhabited

def MoveResult.orElse (r : MoveResult) (g : Game) : Game :=
  match r with
  | success g' => g'
  | failure _ => g

partial def applyGravity (g : Game) : MoveResult :=
  if g.floatingSnakes.isEmpty 
  then MoveResult.success g 
  else
    let snakes' := g.snakes.enum.map λ (i, s) => if g.floatingSnakes.contains i then s.shift Dir.down else s
    let g' := { g .. with snakes := snakes' }
    let deaths := g'.snakes.enum.filterMap λ (i, s) =>
      if s.fields.any (g.map.saws.contains ·) then MoveError.fellOnSaw i
      else if s.fields.any (·.y == 0) then MoveError.fellInWater i
      else none
    if deaths.isEmpty 
    then applyGravity g'
    else MoveResult.failure deaths

partial def move (g : Game) (snakeIdx : Nat) (d : Dir) : MoveResult := do
  match g.snakes.get? snakeIdx with
  | none => MoveResult.failure [MoveError.unknownSnake snakeIdx]
  | some s =>
    match move' g s d snakeIdx with
    | MoveResult.failure e => MoveResult.failure e
    | MoveResult.success g' => applyGravity g'
where
  move' (g : Game) (s : Snake) (d : Dir) (idx : Nat) : MoveResult :=
    let s' := s.move d
    let m := g.map
    let h' := s'.head
    if m.fruit.contains h' then
      -- If the head runs into a fruit, elongate the snake and remove the fruit.
      let se := { s' .. with tail := s'.tail ++ [s.butt] }
      let m' := { m .. with fruit := m.fruit.erase h' }
      MoveResult.success { g .. with map := m', snakes := g.snakes.set idx se }
    else if m.goal == h' && m.goalIsUnlocked then
      -- If the head moves into the goal and the goal is unlocked, remove the snake.
      MoveResult.success { g .. with snakes := g.snakes.drop idx }
    else if g.isSnakeField h' then
      -- If the head runs into a snake body that does not belong to the same snake,
      -- check if the other snake/s can be moved, and if so move it/them as well.
      let moveGroup := g.snakesLinkedToMove idx d
      if moveGroup.contains idx 
      then MoveResult.failure [MoveError.blockedBySnake idx idx] -- The snake is blocked by itself.
      else
        -- Move the target snake and shift all linked snakes.
        let snakes' := g.snakes.enum.map λ (i, s) => 
          if i == idx then s'
          else if moveGroup.contains i then s.shift d
          else s
        -- If there are collisions, error out.
        -- Note, we don't need to check for deaths, as this can not be caused
        -- by a shift (but only by the gravity thereafter).
        if snakes'.any λ s => s.fields.any ((g.map.rocks ++ g.map.fruit ++ g.map.saws).contains ·)
        then MoveResult.failure $ [MoveError.blockedBySnake idx moveGroup.getLast!]
        else MoveResult.success { g .. with snakes := snakes' }
    else if m.rocks.contains h' then
      MoveResult.failure [MoveError.blockedByRock idx]
    else if m.saws.contains h' then
      MoveResult.failure [MoveError.blockedBySaw idx]
    else if h'.y == 0 then
      MoveResult.failure [MoveError.blockedByWater idx]
    else 
      -- If the move was trivial, update the snake state.
      MoveResult.success { g .. with snakes := g.snakes.set idx s' }

def completed (g : Game) : Bool :=
  g.map.fruit.isEmpty && g.snakes.isEmpty && !g.snakeHasDied

def completable (g : Game) : Prop :=
  ∃ moves : List (Nat × Dir), 
    Game.completed $ moves.foldl (init := g) λ g' (i, d) => (g'.move i d).orElse g'

end Game