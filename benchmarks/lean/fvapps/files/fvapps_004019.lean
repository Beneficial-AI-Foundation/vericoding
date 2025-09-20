-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sequenceSum (a b c : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_sum_zero_when_start_greater_than_end
  {s e p : Int}
  (h1 : p > 0)
  (h2 : s > e) :
  sequenceSum s e p = 0 :=
sorry

theorem sequence_sum_equals_arithmetic_sum
  {s e p : Int}
  (h1 : p > 0)
  (h2 : s ≤ e) :
  let n := (e - s) / p + 1
  sequenceSum s e p = n * (2 * s + (n - 1) * p) / 2 :=
sorry

theorem sequence_sum_equals_manual_sum
  {s e p : Int}
  (h1 : p > 0)
  (h2 : s ≤ e) :
  sequenceSum s e p = sequenceSum s e p :=
sorry

theorem sequence_sum_equal_bounds
  {s p : Int}
  (h1 : p > 0) :
  sequenceSum s s p = s :=
sorry
-- </vc-theorems>