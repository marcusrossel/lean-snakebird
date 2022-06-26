import Snakebird

structure State.History where
  initialGame : Game
  moves : List Move := []

structure State where
  game : Game
  selectedSnake : Nat := 0
  errorMessage : String := ""
  history : State.History

inductive SnakeSelection
  | next
  | idx (idx : Nat)

inductive Command
  | move (dir : Dir)
  | selectSnake (sel : SnakeSelection)
  | undo 

def Command.fromString (s : String) : Option Command :=
  if s.isEmpty then none else -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/isNat.3F
  match s.toNat? with
  | some n => some $ .selectSnake (.idx n)
  | none =>
    match s.toLower with
    | "w" => some $ .move .up
    | "a" => some $ .move .left
    | "s" => some $ .move .down
    | "d" => some $ .move .right
    | "q" => some $ .undo
    | "e" => some $ .selectSnake .next
    | _ => none

def refreshDisplay (state : State) : IO Unit := do
  dbg_trace ← IO.Process.run { cmd := "clear" }
  IO.println s!"Selected Snake: {state.selectedSnake}\n"
  IO.println state.game
  unless state.errorMessage.isEmpty do IO.println state.errorMessage
  IO.print "Command: "

def performMove (state : State) (dir : Dir) : State :=
  let move : Move := { dir := dir, snakeIdx := state.selectedSnake } 
  match state.game.move move with
  | .success game => 
    let history := { state.history with moves := state.history.moves ++ [move] }
    { state with game := game, history := history }
  | .failure errors => 
    let message := errors.map toString |>.foldl (init := "") (· ++ s!"{·}\n")
    { state with errorMessage := message }

def performUndo (state : State) : State :=
  if state.history.moves.isEmpty then { state with errorMessage := "Nothing to undo.¬" } else 
    let moves := state.history.moves.dropLast
    let game := apply state.history.initialGame moves
    { state with game := game, history := { state.history with moves := moves } }
where 
  apply (game : Game) : List Move → Game
  | [] => game
  | move :: remaining => 
    match game.move move with
    | .failure _ => panic! "Replay of move history failed."
    | .success game' => apply game' remaining

def performSnakeSelection (state : State) : SnakeSelection → State
  | .next    => { state with selectedSnake := (state.selectedSnake + 1) % state.game.snakes.length }
  | .idx idx => { state with selectedSnake := idx }

partial def runLoop (state : State) : IO Unit := do
  refreshDisplay state
  let input ← (← IO.getStdin).getLine
  let mut state := { state with errorMessage := "" }
  match Command.fromString input.trim with
  | some $ .move dir =>        state := performMove state dir
  | some $ .selectSnake sel => state := performSnakeSelection state sel
  | some $ .undo =>            state := performUndo state
  | none =>                    _ := 0 -- noop    
  runLoop state

def main : IO Unit :=
  runLoop { game := level3, history := { initialGame := level3 } }