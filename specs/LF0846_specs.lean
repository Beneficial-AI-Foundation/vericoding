-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_deletes_for_pure_string (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_non_negative (s : String) : 
  s.length > 0 → min_deletes_for_pure_string s ≥ 0 :=
  sorry

theorem result_less_than_input_length (s : String) :
  s.length > 0 → min_deletes_for_pure_string s ≤ s.length :=
  sorry

theorem single_digit_requires_no_deletions (s : String) :
  s.length = 1 → min_deletes_for_pure_string s = 0 :=
  sorry
-- </vc-theorems>