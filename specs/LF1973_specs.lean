-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (ax ay bx b_y cx c_y : Int) : Nat := sorry

theorem solve_non_negative (ax ay bx b_y cx c_y : Int) :
  solve ax ay bx b_y cx c_y ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_symmetric_ab (ax ay bx b_y cx c_y : Int) :
  solve ax ay bx b_y cx c_y = solve bx b_y ax ay cx c_y := sorry

theorem solve_symmetric_bc (ax ay bx b_y cx c_y : Int) :
  solve ax ay bx b_y cx c_y = solve ax ay cx c_y bx b_y := sorry
-- </vc-theorems>