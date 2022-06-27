import Snakebird.Levels

namespace Play

def commandPalette := "\n--------------------------------\n\n       w : up\n       a : left\n       s : down\n       d : right\n       q : undo move\n       e : select next snake\n<number> : select snake <number>\n restart : restart level\n    exit : exit to menu\n"

structure State.History where
  initialGame : Game
  moves : List Move

structure State where
  levelNumber : Nat
  game : Game
  selectedSnake : Nat
  errorMessage : String
  history : State.History

def State.fromGame (game : Game) (levelNumber : Nat) : State := {
  levelNumber := levelNumber,
  game := game,
  selectedSnake := 0,
  errorMessage := "",
  history := {
    initialGame := game,
    moves := []
  }
}
  
inductive SnakeSelection
  | next
  | idx (idx : Nat)

inductive Command
  | move (dir : Dir)
  | selectSnake (sel : SnakeSelection)
  | undo 
  | restart 
  | exit 

def Command.fromString (s : String) : Option Command :=
  match s.toNat? with
  | some n => some $ .selectSnake (.idx n)
  | none =>
    match s.toLower with
    | "w"       => some (.move .up)
    | "a"       => some (.move .left)
    | "s"       => some (.move .down)
    | "d"       => some (.move .right)
    | "q"       => some .undo
    | "e"       => some (.selectSnake .next)
    | "restart" => some .restart
    | "exit"    => some .exit
    | _         => none

def refreshDisplay (state : State) : IO Unit := do
  dbg_trace ← IO.Process.run { cmd := "clear" }
  IO.println s!"Level {state.levelNumber}\n"
  IO.println state.game
  IO.println s!"Selected Snake: {state.selectedSnake}"
  IO.println commandPalette
  if !state.errorMessage.isEmpty then IO.println state.errorMessage
  if state.game.isCompleted then IO.println "Goal accomplished 🎉\n"
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
  if state.history.moves.isEmpty then { state with errorMessage := "Nothing to undo.\n" } else 
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

def performRestart (state : State) : State :=
  { state with 
    game := state.history.initialGame,
    selectedSnake := 0,
    history := { state.history with moves := [] }
  }

partial def play (state : State) : IO Unit := do
  refreshDisplay state
  let input ← (← IO.getStdin).getLine
  let mut state := { state with errorMessage := "" }
  match Command.fromString input.trim with
  | some (.move dir) =>        state := performMove state dir
  | some (.selectSnake sel) => state := performSnakeSelection state sel
  | some .undo =>              state := performUndo state
  | some .restart =>           state := performRestart state
  | some .exit =>              return
  | none =>                    _ := 0 -- noop    
  play state