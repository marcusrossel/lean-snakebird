import Snakebird.Model.Move

-- The list of snakes that also need to move, if the snake at a given
-- index moves in a given direction.
partial def Game.snakesLinkedToMove (g : Game) (m : Move) : List Nat :=
  match g.snakes.get? m.snakeIdx with
  | none => []
  | some s => 
    let head' := s.head.move m.dir
    match g.snakes.findIndex? (·.positions.contains head') with -- There can be at most one snake that contains a specific field.
    | none => []
    | some i => 
      let candidates := g.snakes.enum.eraseIdx i
      i :: snakesLinkedToShift candidates i m.dir
where 
  snakesLinkedToShift (candidates : List $ Nat × Snake) (idx : Nat) (d : Dir) : List Nat :=
    match candidates.find? (·.fst == idx) with
    | none => []
    | some (_, s) => -- This index is the given idx.  
      let positions := (s.shift d).positions
      let affected := candidates.filter fun (_, s') => 
        s'.positions.any (positions.contains ·)
      if affected.isEmpty then [] else 
        let candidates' := candidates.subtract affected
        let linked' := affected.map (snakesLinkedToShift candidates' ·.fst d)
        affected.map (·.fst) ++ linked'.join

partial def Game.applyGravity (g : Game) : Move.Result :=
  if g.floatingSnakes.isEmpty then .success g else
    let snakes' := g.snakes.enum.map fun (i, s) => 
      if g.floatingSnakes.contains i then s.shift Dir.down else s
    let g' := { g .. with snakes := snakes' }
    let deaths := g'.snakes.enum.filterMap fun (i, s) =>
      if s.positions.any (g.map.saws.contains ·) then some ⟨i, .fellOnSaw⟩
      else if s.positions.any (·.y == 0) then some ⟨i, .fellInWater⟩ 
      else none
    if deaths.isEmpty then applyGravity g' else .failure deaths

def Game.move (g : Game) (m : Move) : Move.Result := 
  match g.snakes.get? m.snakeIdx with
  | none => .failure [⟨m.snakeIdx, .unknownSnake⟩]
  | some s =>
    match move' g s m with
    | .failure e => .failure e
    | .success g' => applyGravity g'
where
  move' (g : Game) (s : Snake) (m : Move) : Move.Result :=
    let s' := s.move m.dir
    let map := g.map
    let h' := s'.head
    if map.fruit.contains h' then
      -- If the head runs into a fruit, elongate the snake and remove the fruit.
      let se := { s' .. with body := s'.body ++ [s.tail] }
      let m' := { map .. with fruit := map.fruit.erase h' }
      .success { g .. with map := m', snakes := g.snakes.set m.snakeIdx se }
    else if map.goal == h' && map.goalIsUnlocked then
      -- If the head moves into the goal and the goal is unlocked, remove the snake.
      .success { g .. with snakes := g.snakes.eraseIdx m.snakeIdx }
    else if g.isSnakePos h' then
      -- If the head runs into a snake body that does not belong to the same snake,
      -- check if the other snake/s can be moved, and if so move it/them as well.
      let moveGroup := g.snakesLinkedToMove m
      if moveGroup.contains m.snakeIdx 
      then .failure [⟨m.snakeIdx, .blockedBySnake m.snakeIdx⟩] -- The snake is blocked by itself.
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
        then .failure $ [⟨m.snakeIdx, .blockedBySnake moveGroup.getLast!⟩]
        else .success { g .. with snakes := snakes' }
    else if map.rocks.contains h' then .failure [⟨m.snakeIdx, .blockedByRock⟩]
    else if map.saws.contains h' then  .failure [⟨m.snakeIdx, .blockedBySaw⟩]
    else if h'.y == 0 then             .failure [⟨m.snakeIdx, .blockedByWater⟩]
    else 
      -- If the move was trivial, update the snake state.
      .success { g .. with snakes := g.snakes.set m.snakeIdx s' }