import Snakebird.Logic
import Lean 
open Lean

declare_syntax_cat map_field
declare_syntax_cat water_field
declare_syntax_cat water_row
declare_syntax_cat map_row

syntax "•" : map_field -- Air
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
syntax "╻" : map_field -- Snake tail bottom
syntax "╹" : map_field -- Snake tail top
syntax "╸" : map_field -- Snake tail left
syntax "╺" : map_field -- Snake tail right
syntax num : map_field -- Snake head

syntax "∼" : water_field

syntax map_field+ "|" linebreak : map_row 
syntax water_field+ : water_row 
syntax:max map_row* water_row : term 

inductive Field.SnakeBody
  | vertical
  | horizontal
  | cornerBottomToRight
  | cornerTopToRight
  | cornerLeftToBottom
  | cornerLeftToTop
deriving BEq

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

-- The snake tails are named in a similar style to `Field.SnakeBody.outDirForIn`.
-- E.g. a `snakeTail Dir.up` is the tail character you should see when moving from 
-- the snake body upwards.
open Field in
inductive Field
  | air
  | rock
  | saw
  | goal
  | fruit
  | snakeBody (b : SnakeBody)
  | snakeTail (d : Dir)
  | snakeHead (n : Nat)
deriving Inhabited, BEq

open Field in
instance : ToString Field where
  toString (f : Field) := 
  match f with 
  | air => "•"
  | rock => "▦"
  | saw => "✸"
  | goal => "◎"
  | fruit => "*"
  | snakeBody SnakeBody.vertical => "┃"
  | snakeBody SnakeBody.horizontal => "━"
  | snakeBody SnakeBody.cornerBottomToRight => "┏"
  | snakeBody SnakeBody.cornerTopToRight => "┗"
  | snakeBody SnakeBody.cornerLeftToBottom => "┓"
  | snakeBody SnakeBody.cornerLeftToTop => "┛"
  | snakeTail Dir.up => "╻"
  | snakeTail Dir.down => "╹"
  | snakeTail Dir.left => "╸"
  | snakeTail Dir.right => "╺"
  | snakeHead n => s!"{n}"

/- -------------------------------------------------------------------------------------------------- -/

def Map.fromFields (fs : List (Pos × Field)) : MacroM Map := do
  let goalPos := fs.filterMap λ (p, f) => match f with | Field.goal => some p | _ => none
  match goalPos with
  | [] => Macro.throwError "Missing goal portal." 
  | g :: (g' :: tl) => Macro.throwError "Found more than one goal portal."
  | g :: [] =>
    return {
      goal  := g,
      rocks := fs.filterMap λ (p, f) => if f == Field.rock  then some p else none,
      fruit := fs.filterMap λ (p, f) => if f == Field.fruit then some p else none,
      saws  := fs.filterMap λ (p, f) => if f == Field.saw   then some p else none
    }

partial def Game.snakesFromFields (fs : List (Pos × Field)) : MacroM (List Snake) := do
  let mut heads : List (Pos × Nat) := fs.filterMap λ (p, f) => match f with | Field.snakeHead n => (p, n) | _ => none
  let headIDs := heads.map Prod.snd
  unless headIDs.isUnique 
    do Macro.throwError "Duplicate snake ID." 
  unless headIDs.all λ h => h ≥ 0 ∧ h ≤ 9 
    do Macro.throwError "Invalid snake ID (has to be single digit)." 
  let mut remainingFs : List (Pos × Field) := fs
  let mut snakes : List Snake := []
  for idx in List.range 10 do
    match heads.find? (·.snd == idx) with
    | none => break
    | some h =>
      let snake := { head := h.fst, body := [] }
      let completed ← completeSnake remainingFs snake none
      remainingFs := completed.fst
      snakes := snakes ++ [completed.snd]
      heads := heads.erase h
  -- Check that snake heads started at 0 and had no gaps.
  unless heads.isEmpty do Macro.throwError "Snake heads need to be numbered from 0."
  -- Check that there are no remaining snake parts (no snake is headless).
  unless remainingFs.all λ (_, f) => 
    match f with 
    | Field.snakeBody _ => false 
    | Field.snakeTail _ => false 
    | _ => true
  do Macro.throwError "Not all snakes have heads."
  return snakes
where 
  completeSnake (remainingFs : List (Pos × Field)) (snake : Snake) (nextDir? : Option Dir) : MacroM $ (List (Pos × Field)) × Snake := do
    match nextDir? with
    | none => -- This case can only occur when the snake only has a head so far.
      for d in Dir.all do
        let p := snake.tail.move d 
        match remainingFs.find? (·.fst == p) with
        | some (_, Field.snakeBody b) =>  if b.outDirForIn d != none then return ← completeSnake remainingFs snake d
        | some (_, Field.snakeTail dt) => 
          if dt == d then return ← completeSnake remainingFs snake d
        | _ => continue
      return (remainingFs, snake)
    | some nextDir =>
      let p := snake.tail.move nextDir
      match remainingFs.find? (·.fst == p) with
      | some (_, Field.snakeBody b) => 
        match b.outDirForIn nextDir with
        | none => Macro.throwError s!"Invalid snake connection at {p}." 
        | some d' =>
          let fs' := remainingFs.erase (p, Field.snakeBody b)
          let snake' := { snake .. with body := snake.body ++ [p] }
          return ← completeSnake fs' snake' d'
      | some (_, Field.snakeTail dt) => 
        if dt == nextDir 
        then return (remainingFs.erase (p, Field.snakeTail dt), { snake .. with body := snake.body ++ [p] })
      | _ => Macro.throwError s!"Invalid snake connection at {p}." 
      Macro.throwError s!"Invalid snake connection at {p}." 
    
def Game.fromFields (fs : List (List Field)) : MacroM Game := do
  let posFields : List (Pos × Field) := 
    (fs.reverse.enum.map λ (y, row) => row.enum.map λ (x, f) => (⟨x, y + 1⟩, f)) -- +1 so that water level is 0
      |> List.join
      |> List.filter λ (_, f) => match f with | Field.air => false | _ => true
  let map ← Map.fromFields posFields
  let snakes ← Game.snakesFromFields posFields
  return { map := map, snakes := snakes }

/- -------------------------------------------------------------------------------------------------- -/

instance : Quote Pos where
  quote (p : Pos) := Unhygienic.run `(Pos.mk $(quote p.x) $(quote p.y))

instance : Quote Snake where
  quote (s : Snake) := Unhygienic.run `(Snake.mk $(quote s.head) $(quote s.body))

instance : Quote Map where
  quote (m : Map) := Unhygienic.run `(Map.mk $(quote m.goal) $(quote m.rocks) $(quote m.fruit) $(quote m.saws))

instance : Quote Game where
  quote (g : Game) := Unhygienic.run `(Game.mk $(quote g.map) $(quote g.snakes))

/- -------------------------------------------------------------------------------------------------- -/

open Field.SnakeBody in
def fieldFromSyntax : Syntax → MacroM (List Field)
  | `(map_field| •) => [Field.air]
  | `(map_field| ▦) => [Field.rock]
  | `(map_field| ✸) => [Field.saw]
  | `(map_field| ◎) => [Field.goal]
  | `(map_field| *) => [Field.fruit]
  | `(map_field| ┃) => [Field.snakeBody vertical]
  | `(map_field| ━) => [Field.snakeBody horizontal]
  | `(map_field| ┏) => [Field.snakeBody cornerBottomToRight]
  | `(map_field| ┗) => [Field.snakeBody cornerTopToRight]
  | `(map_field| ┓) => [Field.snakeBody cornerLeftToBottom]
  | `(map_field| ┛) => [Field.snakeBody cornerLeftToTop]
  | `(map_field| ╻) => [Field.snakeTail Dir.up]
  | `(map_field| ╹) => [Field.snakeTail Dir.down]
  | `(map_field| ╸) => [Field.snakeTail Dir.right]
  | `(map_field| ╺) => [Field.snakeTail Dir.left]
  | `(map_field| $n:numLit) => 
    match n.isNatLit? with
    | none => Macro.throwError "Unknown map field."
    | some n => 
      if n >= 0 && n <= 10 
      then n.digits.map Field.snakeHead
      else Macro.throwError "Sneak heads have to be single digits." 
  | _ => Macro.throwError "Unknown map field."

def fieldRowFromSyntax : Syntax → MacroM (List Field)
  | `(map_row|$fields:map_field*|
  ) => do (← Array.mapM fieldFromSyntax fields).data.join
  | _ => Macro.throwError "Unknown map row."

def waterFieldCount : Syntax → MacroM Nat 
  | `(water_row|$f:water_field*) => f.data.length
  | _ => Macro.throwError "Unknown water row."

macro_rules
  | `($rows:map_row* $water:water_row) => do
    let fields ← Array.mapM fieldRowFromSyntax rows
    let waterLength ← waterFieldCount water
    unless fields.all (·.length == waterLength) 
      do Macro.throwError "All rows must have the same length."
    quote (← Game.fromFields fields.data)
