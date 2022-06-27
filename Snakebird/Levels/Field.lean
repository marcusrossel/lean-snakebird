import Snakebird.Core

inductive Field
  | air
  | rock
  | water
  | saw
  | goal
  | fruit
  | snake (src : Dir) (dst : Option Dir)
  | head (idx : Nat)
deriving BEq, Inhabited

open Dir in
instance : ToString Field where
  toString
  | .air => "·"
  | .rock => "▦"
  | .water => "~"
  | .saw => "✸"
  | .goal => "◎"
  | .fruit => "*"
  | .snake up    up    | .snake down  down   => "┃"
  | .snake left  left  | .snake right right  => "━" 
  | .snake up    right | .snake left  down   => "┏"
  | .snake down  right | .snake left  up     => "┗"
  | .snake right down  | .snake up    left   => "┓"
  | .snake right up    | .snake down  left   => "┛"
  | .snake up    none => "╻"
  | .snake down  none => "╹"
  | .snake left  none => "╺"
  | .snake right none => "╸"
  | .head idx => s!"{idx}"
  | .snake .. => panic! "Invalid snake field."

def Snake.fields (s : Snake) (idx : Nat) : List (Pos × Field) := Id.run do
  let mut fields : List (Pos × Field) := [(s.head, .head idx)]
  for (idx, pos) in s.body.enum do
    let pred := fields.getLast!.fst
    let mut srcDir := Dir.all.filter (pred.move · == pos) |>.getLast! -- This is a singleton.
    match s.body.get? (idx + 1) with
    | some succ => 
      let dstDir := Dir.all.filter (pos.move · == succ) |>.getLast! -- This is a singleton.
      fields := fields ++ [(pos, .snake srcDir dstDir)]
    | none => 
      fields := fields ++ [(pos, .snake srcDir none)]
  return fields

def Map.fields (m : Map) : List (Pos × Field) :=
  (m.goal, Field.goal) ::
  m.rocks.map ((·, Field.rock)) ++
  m.fruit.map ((·, Field.fruit)) ++
  m.saws.map ((·, Field.saw))

def Game.fields (g : Game) : Array (Array Field) := Id.run do
  let allFields := g.map.fields ++ (g.snakes.enum.map λ (i, s) => s.fields i).join
  let minX := allFields.map (·.fst.x) |>.minimum?.get!
  let maxX := allFields.map (·.fst.x) |>.maximum?.get! |> (· + 2)
  let maxY := allFields.map (·.fst.y) |>.maximum?.get! |> (· + 1)
  let xRange := (maxX - minX).natAbs + 1
  let yRange := maxY.natAbs
  let xs := List.range xRange |>.map λ n => (Int.ofNat n) + minX
  let ys := List.range yRange |>.map (Int.ofNat · + 1)
  let mut rows : Array (Array Field) := #[Array.repeat .water xRange]
  for y in ys do
    let mut row : Array Field := #[]
    for x in xs do
      match allFields.find? (·.fst == ⟨x - 1, y⟩) with
      | none => row := row ++ [Field.air]
      | some (_, f) => row := row ++ [f]
    rows := rows ++ [row]
  return rows.reverse

instance : ToString Game where
  toString game := 
    game.fields.foldl (init := "") fun result row => Id.run do
      let mut row := row.map toString |>.foldl (init := "") String.append
      unless game.map.goalIsUnlocked do row := row.replace (toString Field.goal) "◍"
      return result ++ row ++ "\n"