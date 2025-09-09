-- <vc-helpers>
-- </vc-helpers>

def count_factorial_zeros (n : Nat) : Nat := sorry

def count_actual_zeros (n : Nat) : Nat := sorry

theorem count_factorial_zeros_non_negative (k : Nat) : 
  count_factorial_zeros k ≥ 0 := sorry

theorem count_factorial_zeros_zero_case : 
  count_factorial_zeros 0 = 5 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_factorial_zeros 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_factorial_zeros 5

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_factorial_zeros 2

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible