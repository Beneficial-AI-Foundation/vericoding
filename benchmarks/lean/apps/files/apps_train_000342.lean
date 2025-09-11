-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def broken_calc (start target : Nat) : Nat := sorry

theorem broken_calc_non_negative (start target : Nat) :
  broken_calc start target ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem broken_calc_equal_case (x : Nat) :
  broken_calc x x = 0 := sorry

theorem broken_calc_greater_case {start target : Nat} (h : start > target) :
  broken_calc start target = start - target := sorry

theorem broken_calc_bounds :
  broken_calc 1 (10^9) ≥ 0 ∧ broken_calc (10^9) 1 = 10^9 - 1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval broken_calc 2 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval broken_calc 5 8

/-
info: 3
-/
-- #guard_msgs in
-- #eval broken_calc 3 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible