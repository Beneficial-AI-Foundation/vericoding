-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ROT135 (s : String) : String := sorry

theorem length_preserved (s : String) :
  (ROT135 s).length = s.length := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reversible (s : String) :
  ROT135 (ROT135 s) = s := by sorry

theorem letter_shifted_13 (c : Char) (h : c.isAlpha) :
  let result := ROT135 c.toString
  (result.get! 0).isUpper = c.isUpper ∧
  result.get! 0 ≠ c ∧
  (result.get! 0).isAlpha := by sorry

theorem digit_shifted_5 (d : Char) (h : d.isDigit) :
  let result := ROT135 d.toString
  (result.get! 0).isDigit ∧
  result.get! 0 ≠ d := by sorry

theorem other_chars_unchanged (c : Char) (h₁ : ¬c.isAlpha) (h₂ : ¬c.isDigit) :
  ROT135 c.toString = c.toString := by sorry
-- </vc-theorems>