import Lean
open Lean

def List.isUnique [BEq α] (l : List α) : Bool :=
  l.length == l.eraseDups.length

def List.findIndex? (l : List α) (p : α → Bool) : Option Nat :=
  l.enum.find? (p ·.snd) |>.map Prod.fst

def List.indices (l : List α) : List Nat :=
  l.enum.map Prod.fst

def List.indicesWhere' (l : List α) (p : Nat → α → Bool) : List Nat :=
  l.enum.filterMap λ (i, a) => if p i a then i else none

def List.indicesWhere (l : List α) (p : α → Bool) : List Nat :=
  l.indicesWhere' (λ _ a => p a)

def List.subtract [BEq α] : List α → List α → List α
| [], l => []
| hd::tl, l => 
  if l.contains hd 
  then subtract tl l
  else hd :: subtract tl l

theorem List.subtract_decreasing [BEq α] {l₁ l₂ : List α} {a : α} : 
  l₁.elem a → l₂.elem a → (l₁.subtract l₂).length < l₁.length := 
  sorry

def Int.abs (i : Int) : Int :=
  if i < 0 then -i else i

theorem Nat.le_of_not_lt {a b : Nat} (h : ¬ b < a) : a ≤ b := sorry

theorem Nat.div_decreasing {m n : Nat} (hn : 1 < n) (hm : n ≤ m) : (m / n) < m := sorry

def Nat.digits (n : Nat) : List Nat :=
  if h : n < 10 then [n] else (n / 10).digits ++ [n % 10]
termination_by measure id
decreasing_by 
  simp only [measure, id, invImage, InvImage, Nat.lt_wfRel]
  apply div_decreasing <;> simp [Nat.le_of_not_lt h]
  
instance : Quote Int where
  quote (i : Int) := 
    match i with
    | Int.ofNat n   => Unhygienic.run `(Int.ofNat $(quote n))
    | Int.negSucc n => Unhygienic.run `(Int.negSucc $(quote n))
