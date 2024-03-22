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

def floatingSnakes (g : Game) : List Nat :=
  let allSnakes := g.snakes.enum
  let initFloating := allSnakes.filter fun (_, s) => !s.below.any g.map.isStablePos
  transitivelyFloating allSnakes initFloating |>.map Prod.fst
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
        apply Nat.le_trans <| List.diff_length_le (@List.erase _ instBEq (hd :: tl) hd') tl'
        have h := List.mem_filter.mp (hs.symm ▸ List.mem_cons_self hd' tl') |>.left
        simp [@List.length_erase_of_mem _ instBEq instLawfulBEq _ _ h]

def isCompleted (g : Game) : Bool :=
  g.map.fruit.isEmpty && g.snakes.isEmpty

end Game
