-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_temperature_scales (n : Nat) (temps : List Nat) : Nat := sorry 

theorem single_element_is_zero (t : Nat) (h : t ≥ 1) :
  solve_temperature_scales 1 [t] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_temperature_scales 5 [1, 2, 3, 4, 5]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_temperature_scales 4 [5, 2, 3, 8]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_temperature_scales 2 [50, 53]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible