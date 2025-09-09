-- <vc-helpers>
-- </vc-helpers>

def calculate_series_sum (n: Nat) : Nat :=
sorry

theorem calculate_series_sum_positive {n: Nat} (h: n > 0) : 
  calculate_series_sum n > 0 := sorry

theorem calculate_series_sum_increasing {n: Nat} (h: n > 1) :
  calculate_series_sum n > calculate_series_sum (n-1) := sorry

theorem calculate_series_sum_known_values :
  calculate_series_sum 1 = 1 ∧ calculate_series_sum 3 = 45 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible