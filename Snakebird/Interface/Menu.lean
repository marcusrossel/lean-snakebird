import Snakebird.Levels

namespace Menu

def banner := "  _                                        _        _     _         _ \n | |                                      | |      | |   (_)       | |\n | | ___  __ _ _ __ ______ ___ _ __   __ _| | _____| |__  _ _ __ __| |\n | |/ _ \\/ _` | \'_ \\______/ __| \'_ \\ / _` | |/ / _ \\ \'_ \\| | \'__/ _` |\n | |  __/ (_| | | | |     \\__ \\ | | | (_| |   <  __/ |_) | | | | (_| |\n |_|\\___|\\__,_|_| |_|     |___/_| |_|\\__,_|_|\\_\\___|_.__/|_|_|  \\__,_|\n"

inductive Command
  | move (n : Int)
  | select

def Command.fromString (s : String) : Option Command :=
  match s.toLower with
  | ""  => some .select
  | "w" => some (.move (-1 : Int))
  | "s" => some (.move 1)
  | _   => none

def refreshDisplay (selection : Nat) : IO Unit := do
  dbg_trace ← IO.Process.run { cmd := "clear" }
  IO.println banner
  IO.println <| (if selection == 0 then "> " else "  ") ++ "Exit"
  for levelIdx in [0:levels.length] do
    IO.println <| (if selection == levelIdx + 1 then "> " else "  ") ++ s!"Level {levelIdx}"
  IO.print "\nCommand: " 

partial def menu (selection : Nat) : IO (Option Nat) := do
  refreshDisplay selection
  let input ← (← IO.getStdin).getLine
  match Command.fromString input.trim with
  | some (.move n) => 
    let mod : Int := levels.length + 1
    let selection := Int.toNat <| (selection + n + mod) % mod
    menu selection
  | some .select =>
    match selection with
    | 0 => return none
    | levelIdx + 1 => return levelIdx
  | none => menu selection