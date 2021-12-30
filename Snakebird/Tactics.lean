import Snakebird.Delab
open Lean

elab t1:tactic " ⟨|⟩ " t2:tactic : tactic =>
   try Lean.Elab.Tactic.evalTactic t1
   catch err => Lean.Elab.Tactic.evalTactic t2

elab "fail" m:term : tactic => 
  throwError m

macro "complete" : tactic => 
  `((apply Game.completable.completed; simp only [Game.completed]) ⟨|⟩ fail "Game is not complete.")

open Lean Elab.Tactic Game.Move in
elab (name := move) "move " i:num d:term : tactic => do
  evalTactic (← `(tactic| refine Game.completable.move (m := Game.Move.mk $i $d) rfl ?_))

def test :=
◎╺━0•••┆
▦▦▦▦▦▦▦┆
▦▦▦••▦•┆
∼∼∼∼∼∼∼┆
  
  
  
  

