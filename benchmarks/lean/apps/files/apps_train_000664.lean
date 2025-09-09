-- <vc-helpers>
-- </vc-helpers>

def return_number (n : Int) : Int := sorry

theorem return_number_returns_input (n : Int) : 
  return_number n = n := sorry

theorem return_number_nonneg (n : Int) (h : n ≥ 0) : 
  return_number n ≥ 0 ∧ return_number n = n := sorry

theorem return_number_nonpos (n : Int) (h : n ≤ 0) :
  return_number n ≤ 0 ∧ return_number n = n := sorry

/-
info: 123
-/
-- #guard_msgs in
-- #eval return_number 123

/-
info: 0
-/
-- #guard_msgs in
-- #eval return_number 0

/-
info: 99999
-/
-- #guard_msgs in
-- #eval return_number 99999

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible