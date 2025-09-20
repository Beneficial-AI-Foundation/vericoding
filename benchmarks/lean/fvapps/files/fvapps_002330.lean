-- <vc-preamble>
def isLowercase (c : Char) : Bool := 'a' ≤ c ∧ c ≤ 'z'
def isUppercase (c : Char) : Bool := 'A' ≤ c ∧ c ≤ 'Z'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isTitle (s : String) : Bool := sorry
def detect_capital_use (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_lowercase_valid (s : String) : 
  (∀ c ∈ s.data, isLowercase c) → detect_capital_use s = true := sorry

theorem all_uppercase_valid (s : String) :
  (∀ c ∈ s.data, isUppercase c) → detect_capital_use s = true := sorry

theorem titlecase_valid (s : String) :
  s.length > 0 → isTitle s → detect_capital_use s = true := sorry

theorem empty_string_valid :
  detect_capital_use "" = true := sorry

theorem mixed_case_invalid (s : String) :
  s.length ≥ 2 → 
  ¬(∀ c ∈ s.data, isLowercase c) →
  ¬(∀ c ∈ s.data, isUppercase c) →
  ¬(isTitle s) →
  detect_capital_use s = false := sorry
-- </vc-theorems>