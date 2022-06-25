import Snakebird.Exprable
open Lean
open PrettyPrinter

def Field.SnakeBody.fromTo : Dir → Dir → Option SnakeBody
  | .up,    .up => vertical
  | .up,    .down => none
  | .up,    .left => corner .right .down
  | .up,    .right => corner .up .right
  | .down,  .up => none
  | .down,  .down => vertical
  | .down,  .left => corner .right .up
  | .down,  .right => corner .down .right
  | .left,  .up => corner .down .right
  | .left,  .down => corner .up .right
  | .left,  .left => horizontal
  | .left,  .right => none
  | .right, .up => corner .right .up 
  | .right, .down => corner .right .down
  | .right, .left => none
  | .right, .right => horizontal

def Snake.fields' (s : Snake) (idx : Nat) : List (Pos × Field) := Id.run do
  let mut fields : List (Pos × Field) := [(s.head, Field.snakeHead idx)]
  for (idx, pos) in s.body.enum do
    let pred := fields.getLast!.fst
    let mut srcDir := Dir.all.filter (pred.move · == pos) |>.getLast! -- This is a singleton.
    match s.body.get? (idx + 1) with
    | some succ => 
      let dstDir := Dir.all.filter (pos.move · == succ) |>.getLast! -- This is a singleton.
      let body := Field.SnakeBody.fromTo srcDir dstDir |>.get!
      fields := fields ++ [(pos, Field.snakeBody body)]
    | none => 
      fields := fields ++ [(pos, Field.snakeTail srcDir)]
  return fields

def Map.fields (m : Map) : List (Pos × Field) :=
  (m.goal, Field.goal) ::
  m.rocks.map ((·, Field.rock)) ++
  m.fruit.map ((·, Field.fruit)) ++
  m.saws.map ((·, Field.saw))

def Game.fields (g : Game) : Array (Array Field) := Id.run do
  let allFields := g.map.fields ++ (g.snakes.enum.map λ (i, s) => s.fields' i).join
  let minX := allFields.map (·.fst.x) |>.minimum?.get!
  let maxX := allFields.map (·.fst.x) |>.maximum?.get!
  let minY := allFields.map (·.fst.y) |>.minimum?.get!
  let maxY := allFields.map (·.fst.y) |>.maximum?.get!
  let xRange := (maxX - minX).natAbs + 1
  let yRange := (maxY - minY).natAbs + 1
  let xs := List.range xRange |>.map λ n => (Int.ofNat n) + minX
  let ys := List.range yRange |>.map λ n => (Int.ofNat n) + minY
  let mut rows : Array (Array Field) := #[]
  for y in ys do
    let mut row : Array Field := #[]
    for x in xs do
      match allFields.find? (·.fst == ⟨x, y⟩) with
      | none => row := row ++ [Field.air]
      | some (_, f) => row := row ++ [f]
    rows := rows ++ [row]
  return rows.reverse

open Field SnakeBody
def Field.delab : Field → Delaborator.Delab
  | air                              => `(map_field|•)
  | rock                             => `(map_field|▦)
  | saw                              => `(map_field|✸)
  | goal                             => `(map_field|◎)
  | fruit                            => `(map_field|*)
  | snakeBody vertical               => `(map_field|┃)
  | snakeBody horizontal             => `(map_field|━)
  | snakeBody (.corner .up .right)   => `(map_field|┏)
  | snakeBody (.corner .down .right) => `(map_field|┗)
  | snakeBody (.corner .right .down) => `(map_field|┓)
  | snakeBody (.corner .right .up)   => `(map_field|┛)
  | snakeBody (.corner _ _)          => throwError "Invalid Corner"
  | snakeTail .up                    => `(map_field|╻)
  | snakeTail .down                  => `(map_field|╹)
  | snakeTail .right                 => `(map_field|╸)
  | snakeTail .left                  => `(map_field|╺)
  | snakeHead n                      => `(map_field|$(quote n))

def Game.delab (e : Expr) : Delaborator.Delab := do
  let g : Game ← Exprable.fromExpr e
  let fields ← g.fields.mapM (·.mapM Field.delab)
  let rows ← fields.mapM λ fs => `(map_row|•$fs:map_field*•
                                  )
  let water := Array.mkArray (fields.data.getLast!.size + 2) $ ← `(water_field|∼)
  `($rows:map_row* $water:water_field*)

@[delab app.Game.mk] def delabGameMk : Delaborator.Delab := do
  Game.delab (← Delaborator.SubExpr.getExpr)