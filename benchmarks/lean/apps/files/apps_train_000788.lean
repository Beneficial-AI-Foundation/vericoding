-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_lcm_three_nums (n: Nat) : Nat := sorry

def lcm (a b: Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible