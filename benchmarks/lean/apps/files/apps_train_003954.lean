-- <vc-helpers>
-- </vc-helpers>

def super_sum (d n : Nat) : Nat := sorry

theorem super_sum_nonnegative (d n : Nat) :
  super_sum d n ≥ 0 := sorry

theorem super_sum_arithmetic_sequence (n : Nat) : 
  super_sum 1 n = n * (n - 1) / 2 := sorry

theorem super_sum_dimension_scaling (d n : Nat) :
  d > 1 → super_sum d n = d * super_sum 1 n * n^(d-1) := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval super_sum 2 2

/-
info: 18
-/
-- #guard_msgs in
-- #eval super_sum 2 3

/-
info: 12
-/
-- #guard_msgs in
-- #eval super_sum 3 2

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible