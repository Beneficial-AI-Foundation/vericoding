-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_dish_distribution (v w : Nat) : Nat := sorry

theorem dish_distribution_lower_bound (v w : Nat) :
  solve_dish_distribution v w ≥ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dish_distribution_upper_bound (v w : Nat) :
  solve_dish_distribution v w ≤ min v w + 1 := sorry

theorem dish_distribution_equals_min_plus_one (v w : Nat) :
  solve_dish_distribution v w = min v w + 1 := sorry

theorem dish_distribution_symmetry (v w : Nat) :
  solve_dish_distribution v w = solve_dish_distribution w v := sorry
-- </vc-theorems>