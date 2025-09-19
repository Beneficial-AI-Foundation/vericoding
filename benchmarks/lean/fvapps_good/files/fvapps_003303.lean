-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sequence_sum (a b step : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_sum_equal_bounds {a step : Int}
  (h_step_nonzero : step ≠ 0) : 
  sequence_sum a a step = a :=
  sorry

theorem sequence_sum_positive_monotone {a step : Int}
  (h_a_pos : a > 0)
  (h_step_pos : step > 0)
  (b : Int)
  (h_b : b = a + step * 3) :
  sequence_sum a b step ≥ a :=
  sorry
-- </vc-theorems>