-- <vc-preamble>
def maxDiff (n : Nat) : Nat := sorry

theorem maxDiff_single_digit (n : Nat) (h : n < 10) : maxDiff n = 8 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numDigits (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxDiff_properties (n : Nat) :
  n ≥ 10 →
  maxDiff n ≥ 0 ∧ 
  maxDiff n ≤ 999999 := sorry

theorem maxDiff_nonnegative (n : Nat) : maxDiff n ≥ 0 := sorry

-- Helper function to get number of digits

/-
info: 888
-/
-- #guard_msgs in
-- #eval maxDiff 555

/-
info: 8
-/
-- #guard_msgs in
-- #eval maxDiff 9

/-
info: 820000
-/
-- #guard_msgs in
-- #eval maxDiff 123456
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible