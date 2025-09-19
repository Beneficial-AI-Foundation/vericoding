-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_mininum_value (s1 s2 : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_minimum_value_nonnegative (s1 s2 : String) :
  get_mininum_value s1 s2 ≥ 0 :=
sorry

theorem get_minimum_value_bounded (s1 s2 : String) :
  get_mininum_value s1 s2 ≤ min (s1.length) (s2.length) :=
sorry

theorem get_minimum_value_different_lengths (s1 s2 : String) :
  s1.length ≠ s2.length →
  get_mininum_value s1 s2 = min (s1.length) (s2.length) :=
sorry

theorem get_minimum_value_identical (s1 s2 : String) :
  s1 = s2 →
  get_mininum_value s1 s2 = s1.length :=
sorry

theorem get_minimum_value_first_difference (s1 s2 : String) :
  s1.length = s2.length →
  s1 ≠ s2 →
  (s1.take (get_mininum_value s1 s2) = s2.take (get_mininum_value s1 s2)) ∧
  (s1.take (get_mininum_value s1 s2 + 1) ≠ s2.take (get_mininum_value s1 s2 + 1)) :=
sorry

theorem get_minimum_value_identical_string (s : String) :
  get_mininum_value s s = s.length :=
sorry
-- </vc-theorems>