-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) : Nat := sorry

theorem solve_positive (n : Nat) (h : n > 0) : solve n > 0 := sorry

theorem solve_small_values :
  solve 1 = 1 ∧ solve 2 = 2 ∧ solve 3 = 5 := sorry 

theorem solve_monotonic (n : Nat) (h : n > 1) : solve n > solve (n-1) := sorry

/-
info: 14
-/
-- #guard_msgs in
-- #eval solve 4

/-
info: 42
-/
-- #guard_msgs in
-- #eval solve 5

/-
info: 132
-/
-- #guard_msgs in
-- #eval solve 6

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible