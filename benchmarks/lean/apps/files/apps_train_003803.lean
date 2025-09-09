-- <vc-helpers>
-- </vc-helpers>

def digits_average (n : Nat) : Nat := sorry

theorem digits_average_result_in_range (n : Nat) (h : n > 0) : 
  digits_average n ≤ 9 ∧ digits_average n ≥ 0 := sorry

theorem single_digit_unchanged (n : Nat) (h1 : n > 0) (h2 : n ≤ 9) :
  digits_average n = n := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval digits_average 246

/-
info: 9
-/
-- #guard_msgs in
-- #eval digits_average 89

/-
info: 4
-/
-- #guard_msgs in
-- #eval digits_average 3700

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible