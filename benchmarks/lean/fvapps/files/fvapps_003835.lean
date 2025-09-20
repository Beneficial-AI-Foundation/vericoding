-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>