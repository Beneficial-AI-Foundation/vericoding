-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isWhitespace (s: String) : Bool := sorry

theorem non_whitespace_chars_not_whitespace (s: String)
  (h: ∃ c ∈ s.data, c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '\r') :
  isWhitespace s = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_space_chars_is_whitespace (s: String)
  (h: s = "" ∨ (∀ c ∈ s.data, c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r')) :
  isWhitespace s = true := sorry
-- </vc-theorems>