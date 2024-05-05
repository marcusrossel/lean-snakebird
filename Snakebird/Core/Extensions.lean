import Std.Data.List.Lemmas

def Nat.dist (n m : Nat) : Nat :=
  if n > m then n - m else m - n

def Array.repeat (a : α) (n : Nat) : Array α :=
  List.replicate n a |>.toArray

def List.diff' [DecidableEq α] (l₁ l₂ : List α) : List α :=
  @List.diff _ instBEqOfDecidableEq l₁ l₂

theorem List.diff_length_le [DecidableEq α] (l₁ l₂ : List α) : (l₁.diff l₂).length ≤ l₁.length := by
  induction l₂ generalizing l₁ <;> simp [List.diff]
  case cons hd tl hi =>
    split
    case inr   => apply hi
    case inl h => apply Nat.le_trans (hi ..); simp [List.length_erase_of_mem h]; omega

theorem List.length_erase_of_mem' [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    length (l.erase a) = Nat.pred (length l) :=
  List.length_erase_of_mem h

def Nat.digits (n : Nat) : List Nat :=
  if n < 10 then [n] else (n / 10).digits ++ [n % 10]
