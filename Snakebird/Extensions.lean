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
| [], _ => []
| hd::tl, l => 
  if l.elem hd 
  then subtract tl l
  else hd :: subtract tl l

theorem List.elem_cons [BEq α] {a hd : α} {tl : List α} : (hd::tl).elem a → hd = a ∨ tl.elem a := 
  sorry  

theorem Nat.succ_lt {n m : Nat} : n < m → n.succ < m.succ := sorry

theorem List.subtract_decreasing [BEq α] {l₁ l₂ : List α} {a : α} : 
  l₁.elem a → l₂.elem a → (l₁.subtract l₂).length < l₁.length := by
  intro h₁ h₂
  induction l₁
  case nil => contradiction
  case cons hd tl hi => 
    simp only [subtract]
    split
    case inl hs =>
      sorry
    case inr hs =>
      cases List.elem_cons h₁
      case inl hc => rw [hc] at hs; contradiction
      case inr hc => simp only [List.length_cons, Nat.succ_lt, hi hc]

def Int.abs (i : Int) : Int :=
  if i < 0 then -i else i

theorem Nat.le_of_not_lt {a b : Nat} (h : ¬ b < a) : a ≤ b := sorry

theorem Nat.div_decreasing {m n : Nat} (hn : 1 < n) (hm : n ≤ m) : (m / n) < m := sorry

def Nat.digits (n : Nat) : List Nat :=
  if h : n < 10 then [n] else (n / 10).digits ++ [n % 10]
termination_by _ => n
decreasing_by apply div_decreasing <;> simp [Nat.le_of_not_lt h]
  
instance : Quote Int where
  quote (i : Int) := 
    match i with
    | Int.ofNat n   => Unhygienic.run `(Int.ofNat $(quote n))
    | Int.negSucc n => Unhygienic.run `(Int.negSucc $(quote n))
