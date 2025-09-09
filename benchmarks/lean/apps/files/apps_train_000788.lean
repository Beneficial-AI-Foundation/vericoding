-- <vc-helpers>
-- </vc-helpers>

def max_lcm_three_nums (n: Nat) : Nat := sorry

def lcm (a b: Nat) : Nat := sorry

theorem small_cases :
  max_lcm_three_nums 1 = 1 ∧ 
  max_lcm_three_nums 2 = 2 ∧
  max_lcm_three_nums 3 = 6 := sorry

/-
info: 504
-/
-- #guard_msgs in
-- #eval max_lcm_three_nums 9

/-
info: 210
-/
-- #guard_msgs in
-- #eval max_lcm_three_nums 7

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_lcm_three_nums 3

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible