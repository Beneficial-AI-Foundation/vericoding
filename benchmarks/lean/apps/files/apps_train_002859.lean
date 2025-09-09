-- <vc-helpers>
-- </vc-helpers>

def consecutive_sum (n : Nat) : Nat :=
  sorry

theorem result_is_positive (n : Nat) (h : n > 0) : consecutive_sum n ≥ 0 :=
  sorry

theorem min_representation (n : Nat) (h : n > 0) : consecutive_sum n ≥ 1 :=
  sorry

theorem result_less_than_input (n : Nat) (h : n > 0) : consecutive_sum n ≤ n :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval consecutive_sum 1

/-
info: 4
-/
-- #guard_msgs in
-- #eval consecutive_sum 15

/-
info: 2
-/
-- #guard_msgs in
-- #eval consecutive_sum 97

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible