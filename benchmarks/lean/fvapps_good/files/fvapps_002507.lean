-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_substring (string substr : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem substring_count_properties
  {string substr : String}
  (h : substr.length > 0) :
  let count := count_substring string substr
  (count ≥ 0 ∧ count ≤ string.length ∧
   (substr.length > string.length → count = 0)) :=
sorry

theorem string_contains_itself
  {s : String}
  (h : s.length > 0) :
  count_substring s s = 1 :=
sorry

theorem overlapping_substrings
  {s : String}
  (h : s.length ≥ 2)
  (h₂ : s.length > 0) :
  count_substring (toString (List.replicate s.length 'a')) (toString ['a']) = s.length :=
sorry

theorem repeated_substring
  {s : String}
  {n : Nat}
  (h₁ : s.length > 0)
  (h₂ : n > 0)
  (h₃ : n ≤ 10) :
  count_substring (String.append s (String.append s s)) s ≥ 2 :=
sorry
-- </vc-theorems>