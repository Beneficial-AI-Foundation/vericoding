-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def points (radius : Nat) : Nat := sorry 

theorem points_increases_with_radius (r : Nat) :
  r > 0 → points r ≥ points (r-1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem points_greater_than_minimum (r : Nat) :
  points r ≥ 4 * r + 1 := sorry

theorem points_base_cases :
  points 0 = 1 ∧ points 1 = 5 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval points 0

/-
info: 5
-/
-- #guard_msgs in
-- #eval points 1

/-
info: 13
-/
-- #guard_msgs in
-- #eval points 2

/-
info: 29
-/
-- #guard_msgs in
-- #eval points 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible