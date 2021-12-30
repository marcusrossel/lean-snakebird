import Snakebird.Syntax
open Lean

class Exprable (α) where
  fromExpr : Expr → MetaM α

partial def List.fromExpr (α) [Exprable α] (e : Expr) : MetaM $ List α := do
  let ew ← Meta.whnf e
  match ew.getAppFn.constName!.toString with
  | "List.nil" => []
  | "List.cons" =>  
    let args := ew.getAppArgs
    let a ← Exprable.fromExpr args[1]
    let rest ← fromExpr α args[2]
    a :: rest
  | _ => throwError "Invalid list expression."

instance [Exprable α] : Exprable (List α) where
  fromExpr := List.fromExpr α

instance : Exprable Int where
  fromExpr (e : Expr) := do
    let ew ← (Meta.whnf e)
    let arg ← Meta.whnf ew.getAppArgs[0]
    match arg.natLit? with
    | none => throwError "Invalid 'Int' expression."
    | some n => 
      match ew.getAppFn.constName!.toString with
      | "Int.ofNat" => Int.ofNat n
      | "Int.negSucc" => Int.negSucc n
      | _ => throwError "Invalid 'Int' expression."

instance : Exprable Dir where
  fromExpr (e : Expr) := do
    let ew ← (Meta.whnf e)
    match ew.getAppFn.constName!.toString with
    | "Dir.up" => Dir.up
    | "Dir.down" => Dir.down
    | "Dir.right" => Dir.right
    | "Dir.left" => Dir.left
    | _ => throwError "Invalid 'Dir' expression."

instance : Exprable Pos where
  fromExpr (e : Expr) := do
    let ew ← (Meta.whnf e)
    unless ew.getAppFn.constName!.toString == "Pos.mk" 
      do throwError "Invalid 'Pos' expression."
    let args := ew.getAppArgs
    let x ← Exprable.fromExpr args[0]
    let y ← Exprable.fromExpr args[1]
    return ⟨x, y⟩

instance : Exprable Snake where
  fromExpr (e : Expr) := do
    let args := (← Meta.whnf e).getAppArgs
    let head ← Exprable.fromExpr args[0]
    let body ← Exprable.fromExpr args[1]
    return ⟨head, body⟩

instance : Exprable Map where
  fromExpr (e : Expr) := do
    let args := (← Meta.whnf e).getAppArgs
    let goal  ← Exprable.fromExpr args[0]
    let rocks ← Exprable.fromExpr args[1]
    let fruit ← Exprable.fromExpr args[2]
    let saws  ← Exprable.fromExpr args[3]
    return ⟨goal, rocks, fruit, saws⟩

instance : Exprable Game where
  fromExpr (e : Expr) := do
    let args := (← Meta.whnf e).getAppArgs
    let map ← Exprable.fromExpr args[0]
    let snakes ← Exprable.fromExpr args[1]
    return ⟨map, snakes⟩