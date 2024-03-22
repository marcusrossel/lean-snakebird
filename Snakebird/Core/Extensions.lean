import Std.Data.List.Lemmas

def Array.repeat (a : α) (n : Nat) : Array α :=
  List.replicate n a |>.toArray

def List.isUnique [BEq α] (l : List α) : Bool :=
  l.length == l.eraseDups.length

def List.diff' [DecidableEq α] (l₁ l₂ : List α) : List α :=
  @List.diff _ instBEq l₁ l₂

theorem List.diff_length_le [DecidableEq α] (l₁ l₂ : List α) :
    (@List.diff _ instBEq l₁ l₂).length ≤ l₁.length := by
  induction l₂ generalizing l₁ <;> simp [List.diff]
  case cons hd tl hi =>
    split
    case inr   => apply hi
    case inl h => apply Nat.le_trans (hi ..); simp [List.length_erase_of_mem h]

instance instLawfulBEq [DecidableEq α] : @LawfulBEq α instBEq where
  eq_of_beq := by simp_all
  rfl       := by simp

-- TODO: This termination proof should be automatic or provable by `omega` in future verions of Lean.
def Nat.digits (n : Nat) : List Nat :=
  if n < 10 then [n] else (n / 10).digits ++ [n % 10]
termination_by n
decreasing_by exact div_lt_self (Nat.le_trans (by simp : 1 ≤ 10) (not_lt_eq .. ▸ ‹_›)) (by simp)
