-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_series_sum (n: Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_series_sum_positive {n: Nat} (h: n > 0) : 
  calculate_series_sum n > 0 := sorry

theorem calculate_series_sum_increasing {n: Nat} (h: n > 1) :
  calculate_series_sum n > calculate_series_sum (n-1) := sorry

theorem calculate_series_sum_known_values :
  calculate_series_sum 1 = 1 ∧ calculate_series_sum 3 = 45 := sorry
-- </vc-theorems>