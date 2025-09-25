-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + List.sum xs

def sumDigits (n : Nat) : Nat :=
  sorry

def stringToNat (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def dropDigits (s : String) (i : Nat) : String :=
  s.drop i
-- </vc-definitions>

-- <vc-theorems>
theorem sum_digits_non_negative (n : Nat) :
  sumDigits n ≥ 0 := sorry

theorem sum_digits_upper_bound (n : Nat) :
  sumDigits n ≤ n * (toString n).length := sorry 

theorem sum_digits_single_digit (n : Nat) (h : n ≤ 9) :
  sumDigits n = n := sorry
-- </vc-theorems>