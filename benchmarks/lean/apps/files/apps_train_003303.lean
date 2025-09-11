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

/-
info: 12
-/
-- #guard_msgs in
-- #eval sequence_sum 2 6 2

/-
info: 15
-/
-- #guard_msgs in
-- #eval sequence_sum 1 5 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval sequence_sum 1 5 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible