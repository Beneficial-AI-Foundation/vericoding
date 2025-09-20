-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_cake_baking (time_taken : Int) : Int := sorry

theorem solve_cake_baking_positive {time_taken : Int} (h : time_taken > 0) :
  solve_cake_baking time_taken > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_cake_baking_formula {time_taken : Int} :
  solve_cake_baking time_taken = time_taken/2 + 2 := sorry

theorem solve_cake_baking_greater_than_half {time_taken : Int} (h : time_taken > 0) :
  solve_cake_baking time_taken > time_taken/2 := sorry

theorem solve_cake_baking_specific_cases :
  solve_cake_baking 2 = 3 ∧ 
  solve_cake_baking 4 = 4 ∧ 
  solve_cake_baking 10 = 7 := sorry
-- </vc-theorems>