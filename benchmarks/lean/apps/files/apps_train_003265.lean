-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) : Nat := sorry

theorem solve_non_negative (n : Nat) : 
  solve n ≥ 0 := sorry

theorem solve_single_digit (n : Nat) (h : n < 10) :
  solve n = n := sorry

/-
info: 18
-/
-- #guard_msgs in
-- #eval solve 18

/-
info: 11
-/
-- #guard_msgs in
-- #eval solve 29

/-
info: 18
-/
-- #guard_msgs in
-- #eval solve 45

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible