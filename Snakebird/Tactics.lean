import Snakebird.Delab
open Lean

elab t1:tactic " ⟨|⟩ " t2:tactic : tactic =>
   try Lean.Elab.Tactic.evalTactic t1
   catch err => Lean.Elab.Tactic.evalTactic t2

elab "fail" m:term : tactic => 
  throwError m

macro "complete" : tactic => 
  `((apply Game.completable.completed; simp only [Game.completed]) ⟨|⟩ fail "Game is not complete.")

macro "move " i:num d:term : tactic => 
  `(tactic| refine Game.completable.move (m := Game.Move.mk $i $d) rfl ?_)

def test :=
◎╺━0•••┆
▦▦▦▦▦▦▦┆
▦▦▦••▦•┆
∼∼∼∼∼∼∼┆

theorem test_completable : test.completable := by
  move 0 Dir.right
  move 0 Dir.right
  sorry
  
  
  
  

