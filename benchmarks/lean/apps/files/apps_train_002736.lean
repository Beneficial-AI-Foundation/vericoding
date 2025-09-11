-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def my_parse_int (s : String) : String ⊕ Int := sorry

theorem valid_integer_string (s : String) (h : ∀ c ∈ s.data, c.isDigit) : 
  my_parse_int s = Sum.inr (String.toInt! s) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem padded_integer_string (s : String) (n : Int) 
  (h : String.toInt! (String.trim s) = n) :
  my_parse_int s = Sum.inr n := sorry

theorem invalid_string (s : String) 
  (h : ∃ c ∈ s.data, ¬c.isDigit ∧ ¬c.isWhitespace) :
  my_parse_int s = Sum.inl "NaN" := sorry

theorem arbitrary_string (s : String) :
  (my_parse_int s = Sum.inl "NaN") ∨ 
  (my_parse_int s = Sum.inr (String.toInt! (String.trim s))) := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval my_parse_int "9"

/-
info: 9
-/
-- #guard_msgs in
-- #eval my_parse_int "  9  "

/-
info: 'NaN'
-/
-- #guard_msgs in
-- #eval my_parse_int "5 friends"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded