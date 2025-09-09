-- <vc-helpers>
-- </vc-helpers>

def series_sum (n : Int) : String := sorry

theorem series_sum_has_decimal (n : Int) :
  ∃ s₁ s₂, series_sum n = s₁ ++ "." ++ s₂ := sorry

theorem series_sum_has_two_decimals (n : Int) :
  ∃ s₁ s₂, series_sum n = s₁ ++ "." ++ s₂ ∧ s₂.length = 2 := sorry

theorem series_sum_geq_one_if_positive (n : Int) :
  n > 0 → series_sum n = "1.00" ∨ series_sum n > "1.00" := sorry

theorem series_sum_monotonic (n m : Int) :
  n ≥ m → series_sum n ≥ series_sum m := sorry

theorem series_sum_zero : series_sum 0 = "0.00" := sorry

theorem series_sum_negative (n : Int) :
  n < 0 → series_sum n = "0.00" := sorry

/-
info: '1.00'
-/
-- #guard_msgs in
-- #eval series_sum 1

/-
info: '1.25'
-/
-- #guard_msgs in
-- #eval series_sum 2

/-
info: '1.57'
-/
-- #guard_msgs in
-- #eval series_sum 5

/-
info: '0.00'
-/
-- #guard_msgs in
-- #eval series_sum 0

-- Apps difficulty: introductory
-- Assurance level: unguarded