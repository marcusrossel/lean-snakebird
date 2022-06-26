import Snakebird.Levels.Field
import Lean

open Lean

def Map.fromFields (fields : List (Pos × Field)) : MacroM Map := do
  let mut goals : List Pos := []
  let mut rocks : List Pos := []
  let mut fruit : List Pos := []
  let mut saws  : List Pos := [] 
  for ⟨pos, field⟩ in fields do
    match field with
    | .goal =>  goals := goals ++ [pos] 
    | .rock =>  rocks := rocks ++ [pos]
    | .fruit => fruit := fruit ++ [pos]
    | .saw =>   saws  := saws  ++ [pos]
    | _ => continue
  match goals with
  | []            => Macro.throwError "Missing goal portal." 
  | _ :: (_ :: _) => Macro.throwError "Found more than one goal portal."
  | goal :: []    => return { goal := goal, rocks := rocks, fruit := fruit, saws := saws }

-- TODO: Clean up

partial def Game.snakesFromFields (fs : List (Pos × Field)) : MacroM (List Snake) := do
  let mut heads : List (Pos × Nat) := fs.filterMap λ (p, f) => match f with | .head n => (p, n) | _ => none
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
    | .snake .. => false 
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
        | some (_, .snake src dst) => if d == src || d.opposite == dst then return ← completeSnake remainingFs snake d
        | _ => continue
      return (remainingFs, snake)
    | some nextDir =>
      let p := snake.tail.move nextDir
      match remainingFs.find? (·.fst == p) with
      | some (_, .snake src (some dst)) => 
        let mut d'? : Option Dir := none
        if      nextDir == src          then d'? := dst
        else if nextDir == dst.opposite then d'? := src.opposite
        match d'? with
        | none => Macro.throwError s!"Invalid snake connection at {p}." 
        | some d' =>
          let fs' := remainingFs.erase (p, .snake src dst)
          let snake' := { snake with body := snake.body ++ [p] }
          return ← completeSnake fs' snake' d'
      | some (_, .snake dt none) => 
        if dt == nextDir 
        then return (remainingFs.erase (p, .snake dt none), { snake .. with body := snake.body ++ [p] })
      | _ => Macro.throwError s!"Invalid snake connection at {p}." 
      Macro.throwError s!"Invalid snake connection at {p}." 

def Game.fromFields (fs : List (List Field)) : MacroM Game := do
  let posFields : List (Pos × Field) := 
    (fs.reverse.enum.map λ (y, row) => row.enum.map λ (x, f) => (⟨x, y + 1⟩, f)) -- +1 so that water level is 0
      |> List.join
      |> List.filter λ (_, f) => match f with | .air => false | _ => true
  let map ← Map.fromFields posFields
  let snakes ← Game.snakesFromFields posFields
  return { map := map, snakes := snakes }

declare_syntax_cat map_field
declare_syntax_cat water_field

syntax "•" : map_field -- Air
syntax "▦" : map_field -- Rock
syntax "✸" : map_field -- Saw
syntax "◎" : map_field -- Goal
syntax "*" : map_field -- Fruit
syntax "┃" : map_field -- Snake body
syntax "━" : map_field -- Snake body
syntax "┏" : map_field -- Snake body
syntax "┗" : map_field -- Snake body
syntax "┓" : map_field -- Snake body
syntax "┛" : map_field -- Snake body
syntax "╻" : map_field -- Snake body
syntax "╹" : map_field -- Snake body
syntax "╸" : map_field -- Snake body
syntax "╺" : map_field -- Snake body
syntax num : map_field -- Snake head
syntax "∼" : water_field

declare_syntax_cat map_row
declare_syntax_cat water_row

syntax map_field (noWs map_field)* linebreak : map_row
syntax water_field+ : water_row
syntax:max map_row+ water_row : term

open Dir in
def fieldFromSyntax : Syntax → MacroM (List Field)
  | `(map_field| •) => return [.air]
  | `(map_field| ▦) => return [.rock]
  | `(map_field| ✸) => return [.saw]
  | `(map_field| ◎) => return [.goal]
  | `(map_field| *) => return [.fruit]
  | `(map_field| ┃) => return [.snake up    up]
  | `(map_field| ━) => return [.snake right right]
  | `(map_field| ┏) => return [.snake up    right]
  | `(map_field| ┗) => return [.snake down  right]
  | `(map_field| ┓) => return [.snake right down]
  | `(map_field| ┛) => return [.snake right up]
  | `(map_field| ╻) => return [.snake up    none]
  | `(map_field| ╹) => return [.snake down  none]
  | `(map_field| ╸) => return [.snake right none]
  | `(map_field| ╺) => return [.snake left  none]
  | `(map_field| $n:num) => 
    match n.isNatLit? with
    | none => Macro.throwError "Unknown map field."
    | some n => 
      if n < 10 
      then return n.digits.map .head
      else Macro.throwError "Sneak heads have to be single digits." 
  | _ => Macro.throwError "Unknown map field."

def fieldRowFromSyntax : Syntax → MacroM (List Field)
  | `(map_row|$first:map_field$fields:map_field*
    ) => return (← Array.mapM fieldFromSyntax (#[first] ++ fields)).data.join
  | _ => Macro.throwError "Unknown map row."

instance : Quote Int where
  quote (i : Int) := 
    match i with
    | Int.ofNat n   => Unhygienic.run `(Int.ofNat $(quote n))
    | Int.negSucc n => Unhygienic.run `(Int.negSucc $(quote n))

instance : Quote Pos where
  quote (p : Pos) := Unhygienic.run `(Pos.mk $(quote p.x) $(quote p.y))

instance : Quote Snake where
  quote (s : Snake) := Unhygienic.run `(Snake.mk $(quote s.head) $(quote s.body))

instance : Quote Map where
  quote (m : Map) := Unhygienic.run `(Map.mk $(quote m.goal) $(quote m.rocks) $(quote m.fruit) $(quote m.saws))

instance : Quote Game where
  quote (g : Game) := Unhygienic.run `(Game.mk $(quote g.map) $(quote g.snakes))

macro_rules
  | `($rows:map_row* $water:water_field*) => do
  let fields ← Array.mapM fieldRowFromSyntax rows
  let waterLength := water.size
  unless fields.all (·.length == waterLength) 
    do Macro.throwError "All rows must have the same length."
  return quote (← Game.fromFields fields.data)