def Int.abs (i : Int) : Int :=
  if i < 0 then -i else i

def Array.repeat (a : α) : Nat → Array α 
  | 0 => #[]
  | n + 1 => #[a] ++ («repeat» a n)

def List.isUnique [BEq α] (l : List α) : Bool :=
  l.length == l.eraseDups.length

def List.findIndex? (l : List α) (p : α → Bool) : Option Nat :=
  l.enum.find? (p ·.snd) |>.map Prod.fst

def List.subtract [BEq α] : List α → List α → List α
  | [], _ => []
  | hd::tl, l => 
    if l.elem hd 
    then subtract tl l
    else hd :: subtract tl l

partial def Nat.digits (n : Nat) : List Nat :=
  if n < 10 then [n] else (n / 10).digits ++ [n % 10]