-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def series_sum (n : Int) : String := sorry

theorem series_sum_has_decimal (n : Int) :
  ∃ s₁ s₂, series_sum n = s₁ ++ "." ++ s₂ := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem series_sum_has_two_decimals (n : Int) :
  ∃ s₁ s₂, series_sum n = s₁ ++ "." ++ s₂ ∧ s₂.length = 2 := sorry

theorem series_sum_geq_one_if_positive (n : Int) :
  n > 0 → series_sum n = "1.00" ∨ series_sum n > "1.00" := sorry

theorem series_sum_monotonic (n m : Int) :
  n ≥ m → series_sum n ≥ series_sum m := sorry

theorem series_sum_zero : series_sum 0 = "0.00" := sorry

theorem series_sum_negative (n : Int) :
  n < 0 → series_sum n = "0.00" := sorry
-- </vc-theorems>