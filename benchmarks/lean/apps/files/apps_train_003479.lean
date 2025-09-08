/-
Implement `String#whitespace?(str)` (Ruby), `String.prototype.whitespace(str)` (JavaScript), `String::whitespace(str)` (CoffeeScript), or `whitespace(str)` (Python), which should return `true/True` if given object consists exclusively of zero or more whitespace characters, `false/False` otherwise.
-/

-- <vc-helpers>
-- </vc-helpers>

def isWhitespace (s: String) : Bool := sorry

theorem non_whitespace_chars_not_whitespace (s: String)
  (h: ∃ c ∈ s.data, c ≠ ' ' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '\r') :
  isWhitespace s = false := sorry

theorem empty_or_space_chars_is_whitespace (s: String)
  (h: s = "" ∨ (∀ c ∈ s.data, c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r')) :
  isWhitespace s = true := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded