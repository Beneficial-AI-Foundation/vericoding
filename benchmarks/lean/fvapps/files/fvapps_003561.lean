-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bool_to_word (b : Bool) : String := sorry

theorem bool_to_word_returns_string (b : Bool) :
  toString (bool_to_word b) = bool_to_word b := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bool_to_word_returns_yes_or_no (b : Bool) :
  bool_to_word b = "Yes" ∨ bool_to_word b = "No" := sorry

theorem bool_to_word_matches_input (b : Bool) :
  bool_to_word b = if b then "Yes" else "No" := sorry
-- </vc-theorems>