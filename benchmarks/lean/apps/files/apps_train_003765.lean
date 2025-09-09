-- <vc-helpers>
-- </vc-helpers>

def solve (a b : Int) : Int := sorry

theorem solve_full_range :
  solve 0 400000 = 148 := sorry

theorem solve_boundary_cases :
  solve 8 9 = 1 ∧ 
  solve 8 8 = 0 ∧
  solve 388885 388886 = 1 ∧
  solve 388885 388885 = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve 0 100

/-
info: 14
-/
-- #guard_msgs in
-- #eval solve 0 1000

/-
info: 99
-/
-- #guard_msgs in
-- #eval solve 90 139701

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible