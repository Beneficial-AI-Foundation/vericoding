-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def next_num (n : Nat) : Option Nat := sorry

@[simp] def isPolydivisible (n: Nat) : Bool := sorry

@[simp] def splitDigitsUpToLength (n : Nat) (len : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_num_returns_larger_number {n : Nat} :
  match next_num n with
  | some m => m > n
  | none => True := sorry

theorem next_num_is_polydivisible {n : Nat} :
  match next_num n with
  | some m => isPolydivisible m = true
  | none => True := sorry

theorem next_num_very_large_is_none :
  next_num (10^25) = none := sorry

theorem next_num_zero_is_one :
  next_num 0 = some 1 := sorry

theorem next_num_small_numbers (i : Nat) (h : i > 0) (h2 : i < 10) :
  next_num (i-1) = some i := sorry
-- </vc-theorems>