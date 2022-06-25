import Snakebird.Delab
open Lean

elab t1:tactic " ⟨|⟩ " t2:tactic : tactic =>
   try Lean.Elab.Tactic.evalTactic t1
   catch _ => Lean.Elab.Tactic.evalTactic t2

elab "fail" m:term : tactic => 
  throwError m

macro "complete" : tactic => 
  `((apply Game.completable.completed (by decide)) ⟨|⟩ fail "Game is not complete.")

macro "move " i:num d:term : tactic => 
  `(tactic| refine Game.completable.move (m := Game.Move.mk $i $d) rfl ?_)
  
  
  
  

