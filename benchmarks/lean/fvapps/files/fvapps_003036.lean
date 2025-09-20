-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def braces_status (s : String) : Bool := sorry

def count (c : Char) (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem braces_status_balanced (s : String) :
  braces_status s = true →
  count '(' s = count ')' s ∧ 
  count '[' s = count ']' s ∧
  count '{' s = count '}' s := sorry

theorem only_opening_braces (s : String) :
  (∀ c, c ∈ s.data → c ∈ ['(', '[', '{']) →
  (s ≠ "" → braces_status s = false) := sorry

theorem only_closing_braces (s : String) :
  (∀ c, c ∈ s.data → c ∈ [')', ']', '}']) →
  (s ≠ "" → braces_status s = false) := sorry

theorem empty_string_balanced :
  braces_status "" = true := sorry

theorem non_bracket_chars (s : String) :
  (∀ c, c ∈ s.data → c ∉ ['(', ')', '[', ']', '{', '}']) →
  braces_status s = true := sorry
-- </vc-theorems>