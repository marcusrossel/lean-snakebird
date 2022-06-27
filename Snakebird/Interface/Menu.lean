import Snakebird.Levels

namespace Menu

def banner := "  _                                        _        _     _         _ \n | |                                      | |      | |   (_)       | |\n | | ___  __ _ _ __ ______ ___ _ __   __ _| | _____| |__  _ _ __ __| |\n | |/ _ \\/ _` | \'_ \\______/ __| \'_ \\ / _` | |/ / _ \\ \'_ \\| | \'__/ _` |\n | |  __/ (_| | | | |     \\__ \\ | | | (_| |   <  __/ |_) | | | | (_| |\n |_|\\___|\\__,_|_| |_|     |___/_| |_|\\__,_|_|\\_\\___|_.__/|_|_|  \\__,_|\n"

def commandPalette := "\n---------------------------\n\n    w : move selection up\n    s : move selection down\nENTER : select"

inductive Selection
  | exit 
  | instructions
  | level (idx : Nat)
deriving BEq

def Selection.next : Selection → Selection
  | exit => .instructions
  | instructions => if levels.length > 0 then .level 0 else .exit
  | level idx => if idx + 1 < levels.length then .level (idx + 1) else .exit

def Selection.previous : Selection → Selection
  | exit => if levels.length > 0 then .level (levels.length - 1) else .instructions
  | instructions => .exit
  | level idx => if idx > 0 then .level (idx - 1) else .instructions

inductive Command
  | next
  | previous
  | select

def Command.fromString (s : String) : Option Command :=
  match s.toLower with
  | ""  => some .select
  | "w" => some .previous
  | "s" => some .next
  | _   => none

def refreshDisplay (selection : Selection) : IO Unit := do
  dbg_trace ← IO.Process.run { cmd := "clear" }
  IO.println banner
  IO.println <| (if selection == .exit         then "> " else "  ") ++ "Exit"
  IO.println <| (if selection == .instructions then "> " else "  ") ++ "Instructions"
  for levelIdx in [0:levels.length] do
    IO.println <| (if selection == .level levelIdx then "> " else "  ") ++ s!"Level {levelIdx}"
  IO.println commandPalette
  IO.print "\nCommand: " 

partial def menu (selection : Selection := .exit) : IO Selection := do
  refreshDisplay selection
  let input ← (← IO.getStdin).getLine
  match Command.fromString input.trim with
  | some .next => menu selection.next
  | some .previous => menu selection.previous
  | some .select => return selection
  | none => menu selection