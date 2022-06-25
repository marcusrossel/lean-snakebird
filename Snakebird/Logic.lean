import Snakebird.Extensions

inductive Dir -- Direction
  | up
  | down
  | right
  | left
deriving Inhabited, BEq

def Dir.all : List Dir := [Dir.up, Dir.down, Dir.right, Dir.left]

def Dir.opposite : Dir → Dir
  | up    => down
  | down  => up
  | right => left
  | left  => right

instance : ToString Dir where
  toString (d : Dir) :=
  match d with
  | Dir.up => "Dir.up"
  | Dir.down => "Dir.down"
  | Dir.right => "Dir.right"
  | Dir.left => "Dir.left"

structure Pos where -- Position
  x : Int
  y : Int
deriving BEq, Inhabited

instance : ToString Pos where
  toString (p : Pos) := s!"⟨{p.x},{p.y}⟩"

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
  body : List Pos
deriving BEq, Inhabited

namespace Snake

def fields (s : Snake) : List Pos := 
  s.head :: s.body

instance : ToString Snake where
  toString (s : Snake) := 
    s.fields.foldl (init := "⟨") λ r p => r ++ s!"{p}" 
    |>.append "⟩"

theorem fields_ne_nil (s : Snake) : s.fields ≠ [] := by 
  simp [fields]

def tail (s : Snake) : Pos := 
  s.fields.getLast (Snake.fields_ne_nil _)

def move (s : Snake) (d : Dir) : Snake := {
  head := s.head.move d,
  body := (s.head :: s.body).dropLast
}

def shift (s : Snake) (d : Dir) : Snake := {
  head := s.head.move d,
  body := s.body.map (Pos.move · d)
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
deriving BEq, Inhabited

namespace Map

instance : ToString Map where
  toString (m : Map) := 
    let rocks := m.rocks.foldl (init := "") λ r p => r ++ s!"{p}"
    let fruit := m.fruit.foldl (init := "") λ r p => r ++ s!"{p}"
    let saws  := m.saws.foldl  (init := "") λ r p => r ++ s!"{p}"
    s!"⟨\n\tgoal: {m.goal}\n\trocks: {rocks}\n\tfruit: {fruit}\n\tsaws: {saws}\n⟩"

-- Positions a snake can stand on.
def isPlatformPos (m : Map) (p : Pos) : Bool :=
  (m.rocks ++ m.fruit).contains p

def goalIsUnlocked (m : Map) : Bool := 
  m.fruit.isEmpty

end Map

structure Game where
  map : Map
  snakes : List Snake
deriving BEq, Inhabited

namespace Game

instance : ToString Game where
  toString (g : Game) := s!"⟨\n{g.map}\n\tsnakes: {g.snakes}\n⟩"

def isSnakeField (g : Game) (p : Pos) : Bool :=
  g.snakes.any (·.fields.contains p)

def floatingSnakes (g : Game) : List Nat :=
  let allSnakes := g.snakes.enum
  let initFloating := allSnakes.filter λ (_, s) => !s.below.any g.map.isPlatformPos
  transFloating allSnakes initFloating |>.map Prod.fst
where 
  transFloating (all : List $ Nat × Snake) (floating : List $ Nat × Snake) : List (Nat × Snake) :=
    let stableSnakes := all.filterMap λ (i, s) => if floating.any (·.fst == i) then none else some s
    let stableFields := stableSnakes.map Snake.fields |>.join
    let newStable := floating.filter λ (_, s) => s.below.any (stableFields.contains ·)
    if newStable.isEmpty 
    then floating 
    else transFloating all $ List.subtract floating newStable
  termination_by _ => floating.length
  decreasing_by sorry -- apply List.subtract_decreasing

structure Move where
  snakeIdx : Nat
  dir : Dir

inductive Move.Error 
  | unknownSnake   (idx : Nat)
  | blockedByRock  (idx : Nat)
  | blockedBySaw   (idx : Nat)
  | blockedByWater (idx : Nat)
  | blockedBySnake (idx : Nat) (barrierIdx : Nat)
  | fellInWater    (idx : Nat)
  | fellOnSaw      (idx : Nat)

inductive Move.Result
  | success (g : Game)
  | failure (e : List Move.Error)
deriving Inhabited
    
def Move.Result.getD (r : Move.Result) (g : Game) : Game :=
  match r with
  | success g' => g'
  | failure _ => g

open Move

-- The list of snakes that also need to move, if the snake at a given
-- index moves in a given direction.
def snakesLinkedToMove (g : Game) (m : Move) : List Nat :=
  match g.snakes.get? m.snakeIdx with
  | none => []
  | some s => 
    let head' := s.head.move m.dir
    match g.snakes.findIndex? (·.fields.contains head') with -- There can be at most one snake that contains a specific field.
    | none => []
    | some i => 
      let candidates := g.snakes.enum.eraseIdx i
      i :: snakesLinkedToShift candidates i m.dir
where 
  snakesLinkedToShift (candidates : List $ Nat × Snake) (idx : Nat) (d : Dir) : List Nat :=
    match candidates.find? (·.fst == idx) with
    | none => []
    | some (_, s) => -- This index is the given idx.  
      let fields' := (s.shift d).fields
      let affected := candidates.filter λ (_, s') => s'.fields.any (fields'.contains ·)
      if affected.isEmpty then [] else 
        let candidates' := candidates.subtract affected
        let linked' := affected.map (snakesLinkedToShift candidates' ·.fst d)
        affected.map (·.fst) ++ linked'.join
  termination_by _ => candidates.length
  decreasing_by sorry -- apply List.subtract_decreasing

def applyGravity (g : Game) : Result :=
  if g.floatingSnakes.isEmpty
  then Result.success g 
  else
    let snakes' := g.snakes.enum.map λ (i, s) => if g.floatingSnakes.contains i then s.shift Dir.down else s
    let g' := { g .. with snakes := snakes' }
    let deaths := g'.snakes.enum.filterMap λ (i, s) =>
      if s.fields.any (g.map.saws.contains ·) then Error.fellOnSaw i
      else if s.fields.any (·.y == 0) then Error.fellInWater i
      else none
    if deaths.isEmpty 
    then applyGravity g'
    else Result.failure deaths
  termination_by _ => g.snakes.foldl (init := 0) λ r s => r + s.tail.y.natAbs
  decreasing_by sorry

def move (g : Game) (m : Move) : Result := 
  match g.snakes.get? m.snakeIdx with
  | none => Result.failure [Error.unknownSnake m.snakeIdx]
  | some s =>
    match move' g s m with
    | Result.failure e => Result.failure e
    | Result.success g' => applyGravity g'
where
  move' (g : Game) (s : Snake) (m : Move) : Result :=
    let s' := s.move m.dir
    let map := g.map
    let h' := s'.head
    if map.fruit.contains h' then
      -- If the head runs into a fruit, elongate the snake and remove the fruit.
      let se := { s' .. with body := s'.body ++ [s.tail] }
      let m' := { map .. with fruit := map.fruit.erase h' }
      Result.success { g .. with map := m', snakes := g.snakes.set m.snakeIdx se }
    else if map.goal == h' && map.goalIsUnlocked then
      -- If the head moves into the goal and the goal is unlocked, remove the snake.
      Result.success { g .. with snakes := g.snakes.eraseIdx m.snakeIdx }
    else if g.isSnakeField h' then
      -- If the head runs into a snake body that does not belong to the same snake,
      -- check if the other snake/s can be moved, and if so move it/them as well.
      let moveGroup := g.snakesLinkedToMove m
      if moveGroup.contains m.snakeIdx 
      then Result.failure [Error.blockedBySnake m.snakeIdx m.snakeIdx] -- The snake is blocked by itself.
      else
        -- Move the target snake and shift all linked snakes.
        let snakes' := g.snakes.enum.map λ (i, s) => 
          if i == m.snakeIdx then s'
          else if moveGroup.contains i then s.shift m.dir
          else s
        -- If there are collisions, error out.
        -- Note, we don't need to check for deaths, as this can not be caused
        -- by a shift (but only by the gravity thereafter).
        if snakes'.any λ s => s.fields.any ((g.map.rocks ++ g.map.fruit ++ g.map.saws).contains ·)
        then Result.failure $ [Error.blockedBySnake m.snakeIdx moveGroup.getLast!]
        else Result.success { g .. with snakes := snakes' }
    else if map.rocks.contains h' then
      Result.failure [Error.blockedByRock m.snakeIdx]
    else if map.saws.contains h' then
      Result.failure [Error.blockedBySaw m.snakeIdx]
    else if h'.y == 0 then
      Result.failure [Error.blockedByWater m.snakeIdx]
    else 
      -- If the move was trivial, update the snake state.
      Result.success { g .. with snakes := g.snakes.set m.snakeIdx s' }

def completed (g : Game) : Prop :=
  g.map.fruit.isEmpty && g.snakes.isEmpty

open Move.Result
inductive completable : Game → Prop 
  | completed {g} : g.completed → completable g
  | move {g₁ g₂ : Game} {m} : (g₁.move m = success g₂) → completable g₂ → completable g₁

end Game