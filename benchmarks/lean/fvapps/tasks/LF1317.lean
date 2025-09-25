-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_unique_strings (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_single_chars :
  count_unique_strings "c" = 0 ∧ 
  count_unique_strings "k" = 0 :=
sorry

theorem invalid_chars_property (s : String) :
  (∀ c ∈ s.data, c = 'c' ∨ c = 'k') →
  count_unique_strings s = 0 :=
sorry

theorem valid_chars_bound (s : String) :
  (∀ c ∈ s.data, c ≠ 'c' ∧ c ≠ 'k') →
  0 ≤ count_unique_strings s ∧ 
  count_unique_strings s ≤ 10^9 + 7 :=
sorry

theorem multiplication_property (string_parts : List String) :
  string_parts.length > 0 →
  (∀ s ∈ string_parts, s.length > 0) →
  (∀ s ∈ string_parts, ∀ c ∈ s.data, c = 'f' ∨ c = 'g') →
  count_unique_strings ("x".intercalate string_parts) > 0 :=
sorry
-- </vc-theorems>