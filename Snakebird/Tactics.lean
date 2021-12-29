import Snakebird.Delab

elab t1:tactic " ⟨|⟩ " t2:tactic : tactic =>
   try Lean.Elab.Tactic.evalTactic t1
   catch err => Lean.Elab.Tactic.evalTactic t2

elab "fail" m:term : tactic => 
  throwError m

macro "complete" : tactic => 
  `(apply Game.completable.completed; simp only [Game.completed] ⟨|⟩ fail "Game is not complete.")

syntax "move" term term : tactic

macro_rules 
  | `(tactic| move $i:term $d:term) => do
    let g' ← getGoalState



