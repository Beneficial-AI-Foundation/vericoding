-- <vc-preamble>
def stringToList (s : String) : List Char := s.data

def listToString (l : List Char) : String := String.mk l

def charListOrdered (l₁ l₂ : List Char) : Bool :=
  match l₁, l₂ with
  | [], [] => true
  | x::xs, y::ys => if x.val < y.val then true
                    else if x.val = y.val then charListOrdered xs ys
                    else false
  | _, _ => false

def countChar (c : Char) (s : String) : Nat :=
  s.data.foldl (fun acc x => if x = c then acc + 1 else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minInteger (num : String) (k : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minInteger_length (num : String) (k : Nat) :
  (minInteger num k).length = num.length :=
sorry

theorem minInteger_leq_input (num : String) (k : Nat) :
  minInteger num k ≤ num :=
sorry

theorem minInteger_zero_k (num : String) :
  minInteger num 0 = num :=
sorry

theorem minInteger_monotonic (num : String) (k₁ k₂ : Nat) :
  k₁ ≤ k₂ → minInteger num k₂ ≤ minInteger num k₁ :=
sorry

theorem minInteger_char_count (num : String) (k : Nat) (c : Char) :
  countChar c (minInteger num k) = countChar c num :=
sorry
-- </vc-theorems>