import Std.Data.List.Basic
import Snakebird.Core.Move

namespace Game

-- The list of snakes that need to move, if the snake at a given index moves in a given direction.
def snakesLinkedToMove (g : Game) (m : Move) : List Nat := Id.run do
  let some s := g.snakes.get? m.snakeIdx | return []
  let head' := s.head.move m.dir
  -- There can be at most one snake that contains a specific field.
  let some i := g.snakes.findIdx? (·.positions.contains head') | return []
  let candidates := g.snakes.enum.eraseIdx i
  return i :: snakesLinkedToShift candidates i m.dir
where
  snakesLinkedToShift (candidates : List (Nat × Snake)) (idx : Nat) (d : Dir) : List Nat := Id.run do
    let some (_, s) := candidates.find? (·.fst == idx) | return []
    let positions := (s.shift d).positions
    let affected := candidates.filter fun (_, s') => s'.positions.any (positions.contains ·)
    if affected.isEmpty then
      return []
    else
      let candidates' := candidates.diff' affected
      let linked' := affected.map (snakesLinkedToShift candidates' ·.fst d)
      return affected.map (·.fst) ++ linked'.join
  termination_by candidates.length
  decreasing_by
    simp_wf
    cases candidates <;> simp [List.isEmpty] at *
    case cons hd tl h =>
      cases ha : affected <;> simp_all [ha]
      case cons hd' tl' =>
        simp_arith
        simp_arith [List.diff']
        have h₀ := List.diff_length_le (@List.erase _ instBEq (hd :: tl) hd') tl'
        have h₁ := ha.symm ▸ List.mem_cons_self hd' tl'
        have h₂ := (List.mem_filter.mp h₁).left
        have h₃ := List.length_erase_of_mem' h₂
        exact Nat.le_trans h₀ (by simp [h₃])

-- The termination metric used for `applyGravity`.
private def floatingSnakeHeight (g : Game) : Nat :=
  g.floatingSnakes.foldl (init := 0) (· + ·.snd.head.y)

partial def applyGravity (g : Game) : Move.Result :=
  if g.floatingSnakes.isEmpty then
    .success g
  else
    let snakes' := g.snakes.enum.map fun (i, s) =>
      if g.floatingSnakes.any (·.fst == i) then s.shift Dir.down else s
    let g' := { g with snakes := snakes' }
    let deaths := g'.snakes.enum.filterMap fun (i, s) =>
      if s.positions.any (g.map.saws.contains ·) then some ⟨i, .fellOnSaw⟩
      else if s.positions.any (·.y == 0)         then some ⟨i, .fellInWater⟩
      else none
    if deaths.isEmpty then applyGravity g' else .failure deaths
-- TODO: termination_by floatingSnakeHeight g

def move (g : Game) (m : Move) : Move.Result := Id.run do
  let some s := g.snakes.get? m.snakeIdx | return .failure [⟨m.snakeIdx, .unknownSnake⟩]
  match move' g s m with
  | .failure e  => return .failure e
  | .success g' => return applyGravity g'
where
  move' (g : Game) (s : Snake) (m : Move) : Move.Result :=
    let s' := s.move m.dir
    let map := g.map
    let h' := s'.head
    if map.fruit.contains h' then
      -- If the head runs into a fruit, elongate the snake and remove the fruit.
      let se := { s' with body := s'.body ++ [s.tail] }
      let m' := { map with fruit := map.fruit.erase h' }
      .success { g with map := m', snakes := g.snakes.set m.snakeIdx se }
    else if map.goal == h' && map.goalIsUnlocked then
      -- If the head moves into the goal and the goal is unlocked, remove the snake.
      .success { g with snakes := g.snakes.eraseIdx m.snakeIdx }
    else if g.isSnakePos h' then
      -- If the head runs into a snake body that does not belong to the same snake,
      -- check if the other snake/s can be moved, and if so move it/them as well.
      let moveGroup := g.snakesLinkedToMove m
      if moveGroup.contains m.snakeIdx then
        .failure [⟨m.snakeIdx, .blockedBySnake m.snakeIdx⟩] -- The snake is blocked by itself.
      else
        -- Move the target snake and shift all linked snakes.
        let snakes' := g.snakes.enum.map fun (i, s) =>
          if i == m.snakeIdx then s'
          else if moveGroup.contains i then s.shift m.dir
          else s
        -- If there are collisions, error out.
        -- Note, we don't need to check for deaths, as this can not be caused
        -- by a shift (but only by the gravity thereafter).
        if snakes'.any fun s => s.positions.any ((g.map.rocks ++ g.map.fruit ++ g.map.saws).contains ·)
        then .failure [⟨m.snakeIdx, .blockedBySnake moveGroup.getLast!⟩]
        else .success { g .. with snakes := snakes' }
    else if map.rocks.contains h' then .failure [⟨m.snakeIdx, .blockedByRock⟩]
    else if map.saws.contains h' then  .failure [⟨m.snakeIdx, .blockedBySaw⟩]
    else if h'.y == 0 then             .failure [⟨m.snakeIdx, .blockedByWater⟩]
    else
      -- If the move was trivial, update the snake state.
      .success { g with snakes := g.snakes.set m.snakeIdx s' }
