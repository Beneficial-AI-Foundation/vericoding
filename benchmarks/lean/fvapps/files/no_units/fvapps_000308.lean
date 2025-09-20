-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_prefix (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_prefix {s : String} (h : s.length > 0) :
  (longest_prefix s).isPrefixOf s := by
  sorry

theorem output_is_suffix {s : String} (h : s.length > 0) :
  String.drop s (s.length - (longest_prefix s).length) = longest_prefix s := by
  sorry

theorem output_length_less_than_input {s : String} (h : s.length > 0) :
  (longest_prefix s).length ≤ s.length := by
  sorry

theorem output_matches_input_chars {s : String} (h : s.length > 0) :
  ∀ c, c ∈ (longest_prefix s).data → c ∈ s.data := by
  sorry
-- </vc-theorems>