-- <vc-helpers>
-- </vc-helpers>

def single_digit (n : Nat) : Nat :=
  sorry

theorem single_digit_result_bounds (n : Nat) :
  0 ≤ single_digit n ∧ single_digit n ≤ 9 :=
  sorry

theorem single_digit_fixed_point (n : Nat) :
  single_digit (single_digit n) = single_digit n :=
  sorry

theorem single_digit_identity (n : Nat) (h : n ≤ 9) :
  single_digit n = n :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval single_digit 5

/-
info: 8
-/
-- #guard_msgs in
-- #eval single_digit 999

/-
info: 1
-/
-- #guard_msgs in
-- #eval single_digit 1234444123

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible