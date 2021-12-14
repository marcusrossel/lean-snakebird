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

partial def applyGravity (g : Game) : Result :=
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

partial def move (g : Game) (m : Move) : Result := do
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
      let se := { s' .. with tail := s'.tail ++ [s.butt] }
      let m' := { map .. with fruit := map.fruit.erase h' }
      Result.success { g .. with map := m', snakes := g.snakes.set m.snakeIdx se }
    else if map.goal == h' && map.goalIsUnlocked then
      -- If the head moves into the goal and the goal is unlocked, remove the snake.
      Result.success { g .. with snakes := g.snakes.drop m.snakeIdx }
    else if g.isSnakeField h' then
      -- If the head runs into a snake body that does not belong to the same snake,
      -- check if the other snake/s can be moved, and if so move it/them as well.
      let moveGroup := g.snakesLinkedToMove m.snakeIdx m.dir
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

def completed (g : Game) : Bool :=
  g.map.fruit.isEmpty && g.snakes.isEmpty && !g.snakeHasDied

-- TODO: This definition of completability is bad.
--       It would allow a sequence of failing moves as a witness for completion, when
--       the initial game is already completed.
open Move.Result
inductive completable : Game → Prop 
  | completed {g} : g.completed → completable g
  | move {g₁ g₂ : Game} {m} : (g₁.move m = success g₂) → completable g₂ → completable g₁

end Game

/- -------------------------------------------------------------------------------------------------- -/

declare_syntax_cat map_field
declare_syntax_cat water_row
declare_syntax_cat map_row

syntax "·" : map_field -- Air
syntax "▦" : map_field -- Rock
syntax "✸" : map_field -- Saw
syntax "◎" : map_field -- Goal
syntax "*" : map_field -- Fruit
syntax "┃" : map_field -- Snake body vertical
syntax "━" : map_field -- Snake body horizontal
syntax "┏" : map_field -- Snake body corner bottom to right
syntax "┗" : map_field -- Snake body corner top to right
syntax "┓" : map_field -- Snake body corner left to bottom
syntax "┛" : map_field -- Snake body corner left to top
syntax "A" : map_field -- Snake 0 head
syntax "B" : map_field -- Snake 1 head
syntax "C" : map_field -- Snake 2 head

syntax map_field+ : map_row -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Invalid.20parser
syntax "∼"+ : water_row 
syntax:max map_row+ water_row : term 

inductive Field.SnakeBody
  | vertical
  | horizontal
  | cornerBottomToRight
  | cornerTopToRight
  | cornerLeftToBottom
  | cornerLeftToTop

-- If we enter the given snake body by moving in the given direction,
-- this function returns the direction in which the next snake body
-- must be located (i.e. where the other entrance/exit of this body
-- points). If we enter from an invalid direction, `none` is returned.
open Field.SnakeBody Dir in
def Field.SnakeBody.outDirForIn : SnakeBody → Dir → Option Dir
  | vertical,            up    => up
  | vertical,            down  => down
  | vertical,            left  => none
  | vertical,            right => none
  | horizontal,          up    => none
  | horizontal,          down  => none
  | horizontal,          left  => left
  | horizontal,          right => right
  | cornerBottomToRight, up    => right
  | cornerBottomToRight, down  => none
  | cornerBottomToRight, left  => down
  | cornerBottomToRight, right => none
  | cornerTopToRight,    up    => none
  | cornerTopToRight,    down  => right
  | cornerTopToRight,    left  => up
  | cornerTopToRight,    right => none
  | cornerLeftToBottom,  up    => left
  | cornerLeftToBottom,  down  => none
  | cornerLeftToBottom,  left  => down
  | cornerLeftToBottom,  right => none
  | cornerLeftToTop,     up    => none
  | cornerLeftToTop,     down  => left
  | cornerLeftToTop,     left  => none
  | cornerLeftToTop,     right => up

open Field in
inductive Field
  | air
  | rock
  | saw
  | goal
  | fruit
  | snakeBody (b : SnakeBody)
  | snake0Head
  | snake1Head
  | snake2Head
deriving Inhabited

/- -------------------------------------------------------------------------------------------------- -/

def Game.fromFields (f' : List (List Field)) : Game :=
  let f := f'.join
  let m := f'.getLast?.map (·.length) |> (Option.getD · 1) 
  sorry

/- -------------------------------------------------------------------------------------------------- -/

open Field.SnakeBody in
def fieldToTerm : Lean.Macro
  | `(map_field| ·) => `(Field.air)
  | `(map_field| ▦) => `(Field.rock)
  | `(map_field| ✸) => `(Field.saw)
  | `(map_field| ◎) => `(Field.goal)
  | `(map_field| *) => `(Field.fruit)
  | `(map_field| ┃) => `(Field.snakeBody vertical)
  | `(map_field| ━) => `(Field.snakeBody horizontal)
  | `(map_field| ┏) => `(Field.snakeBody cornerBottomToRight)
  | `(map_field| ┗) => `(Field.snakeBody cornerTopToRight)
  | `(map_field| ┓) => `(Field.snakeBody cornerLeftToBottom)
  | `(map_field| ┛) => `(Field.snakeBody cornerLeftToTop )
  | `(map_field| A) => `(Field.snake0Head)
  | `(map_field| B) => `(Field.snake1Head)
  | `(map_field| C) => `(Field.snake2Head)
  | _ => Lean.Macro.throwError "Unknown map field."

open Lean in
def rowToTerm : Syntax → MacroM (Syntax × Nat)
  | `(map_row| $fields:map_field*) => do
    let fieldTerms ← Array.mapM fieldToTerm fields
    let syn ← `([$fieldTerms,*])
    (syn, fields.size)
  | _ => Macro.throwError "Unknown map row."

macro_rules
  | `($rows:map_row* $water:water_row) => do
    let synsAndSizes ← Array.mapM rowToTerm rows
    unless synsAndSizes.all (·.snd == water.getNumArgs) 
      do Lean.Macro.throwError "Map does not have consistent width."
    let syns := synsAndSizes.map Prod.fst
    `(Game.fromFields [$syns,*])

/- -------------------------------------------------------------------------------------------------- -/

def game := -- The missing newlines in the syntax declaration are producing the error.
········▦▦·····◎······
········▦▦▦▦··········
····▦····▦▦···········
······▦··▦···*·▦······
···━━A···▦·▦···▦▦···*·
▦▦▦▦▦▦▦▦···▦▦·······▦▦ 
▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦▦
▦▦▦▦▦▦▦▦▦·▦▦▦▦▦▦▦▦▦▦▦·
·▦▦▦▦▦▦▦▦··▦▦▦▦▦▦▦▦▦▦·
∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼∼

  