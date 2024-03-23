import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Snakebird.Core.Snake
import Snakebird.Core.Map

structure Game where
  map    : Map
  snakes : List Snake
  deriving Inhabited

namespace Game

def isSnakePos (g : Game) (p : Pos) : Bool :=
  g.snakes.any (·.positions.contains p)

def floatingSnakes (g : Game) : List (Nat × Snake) :=
  let allSnakes := g.snakes.enum
  let initFloating := allSnakes.filter fun (_, s) => !s.below.any g.map.isStablePos
  transitivelyFloating allSnakes initFloating
where
  transitivelyFloating (all floating : List (Nat × Snake)) : List (Nat × Snake) :=
    let stableSnakes := all.filterMap fun (i, s) =>
      if floating.any (·.fst == i) then none else some s
    let stableFields := stableSnakes.map Snake.positions |>.join
    let newStable := floating.filter fun (_, s) => s.below.any (stableFields.contains ·)
    if newStable.isEmpty then floating else transitivelyFloating all (floating.diff' newStable)
  termination_by floating.length
  decreasing_by
    simp_wf
    cases floating <;> simp [List.isEmpty] at *
    case cons hd tl h =>
      cases hs : newStable <;> simp_all [hs]
      case cons hd' tl' =>
        simp_arith [List.diff']
        have h₀ := List.diff_length_le (@List.erase _ instBEq (hd :: tl) hd') tl'
        have h₁ := hs.symm ▸ List.mem_cons_self hd' tl'
        have h₂ := (List.mem_filter.mp h₁).left
        have h₃ := List.length_erase_of_mem' h₂
        exact Nat.le_trans h₀ (by simp [h₃])

def isCompleted (g : Game) : Bool :=
  g.map.fruit.isEmpty && g.snakes.isEmpty

end Game
