-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_char (s : String) (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_char_case_insensitive_char (s : String) (c : Char) :
  count_char s c = count_char s c.toUpper ∧ 
  count_char s c = count_char s c.toLower :=
sorry

theorem count_char_bounds (s : String) (c : Char) :
  0 ≤ count_char s c ∧ count_char s c ≤ s.length :=
sorry 

theorem count_char_case_insensitive_string (s : String) (c : Char) :
  count_char s c = count_char s.toUpper c ∧
  count_char s c = count_char s.toLower c :=
sorry
-- </vc-theorems>