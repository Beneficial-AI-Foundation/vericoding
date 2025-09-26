-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_palindrome (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_bounds (s : String) :
  0 ≤ longest_palindrome s ∧ longest_palindrome s ≤ s.length :=
  sorry

theorem empty_string :
  longest_palindrome "" = 0 :=
  sorry

theorem min_length_nonempty (s : String) :
  s ≠ "" → longest_palindrome s ≥ 1 :=
  sorry

theorem repeated_chars_min_length (c : Char) :
  longest_palindrome (String.mk [c, c]) ≥ 2 :=
  sorry

theorem palindrome_parity (s : String) :
  longest_palindrome s % 2 = 0 ∨ longest_palindrome s % 2 = 1 :=
  sorry

theorem case_sensitivity_lower (s : String) :
  longest_palindrome s.toLower ≥ longest_palindrome s :=
  sorry

theorem case_sensitivity_upper (s : String) :
  longest_palindrome s.toUpper ≥ longest_palindrome s :=
  sorry
-- </vc-theorems>