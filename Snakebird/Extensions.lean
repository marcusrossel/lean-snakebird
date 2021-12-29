import Lean
open Lean

inductive _Debug (α) 
  | value (a : α)
  | message (m : String) 

instance [Inhabited α] : Inhabited (_Debug α) where 
  default := _Debug.value (Inhabited.default)

instance : Coe α (_Debug α) := ⟨λ a => _Debug.value a⟩

def List.isUnique [BEq α] (l : List α) : Bool :=
  l.length == l.eraseDups.length

def List.indices (l : List α) : List Nat :=
  l.enum.map Prod.fst

def List.indicesWhere' (l : List α) (p : Nat → α → Bool) : List Nat :=
  l.enum.filterMap λ (i, a) => if p i a then i else none

def List.indicesWhere (l : List α) (p : α → Bool) : List Nat :=
  l.indicesWhere' (λ _ a => p a)

def Int.abs (i : Int) : Int :=
  if i < 0 then -i else i

-- TODO: Make this non-partial.
partial def Nat.digits (n : Nat) : List Nat :=
  if n < 10 then [n] else (n / 10).digits ++ [n % 10]
  
instance : Quote Int where
  quote (i : Int) := 
    match i with
    | Int.ofNat n   => Unhygienic.run `(Int.ofNat $(quote n))
    | Int.negSucc n => Unhygienic.run `(Int.negSucc $(quote n))
