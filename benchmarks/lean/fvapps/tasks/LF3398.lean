-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_digit (s : String) : Bool := sorry

theorem is_digit_general_string_property (s : String) :
  is_digit s = (s.length = 1 ∧ s.any Char.isDigit) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_digit_string_conversion {n : Nat} :
  is_digit (toString n) = (n ≥ 0 ∧ n ≤ 9) := sorry 

theorem is_digit_non_digits_false (s : String) : 
  (∀ c ∈ s.toList, ¬c.isDigit) → ¬is_digit s := sorry

theorem is_digit_multiple_digits_false (s : String) :
  s.length > 1 → (∀ c ∈ s.toList, c.isDigit) → ¬is_digit s := sorry
-- </vc-theorems>