-- <vc-preamble>
def split (s : String) (sep : Char → Bool) : List String := sorry
def trim (s : String) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_freud (s : String) : String := sorry

theorem empty_string_returns_empty :
  to_freud "" = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem only_whitespace_returns_empty (s : String) :
  trim s = "" → to_freud s = "" := sorry

theorem non_empty_only_contains_sex (s : String) :
  trim s ≠ "" →
  List.all (split (to_freud s) (· = ' ')) (· = "sex") := sorry

theorem preserves_word_count (s : String) :
  trim s ≠ "" →
  (split (to_freud s) (· = ' ')).length = (split (trim s) (· = ' ')).length := sorry

/-
info: 'sex'
-/
-- #guard_msgs in
-- #eval to_freud "test"

/-
info: 'sex sex sex sex'
-/
-- #guard_msgs in
-- #eval to_freud "This is a test"

/-
info: ''
-/
-- #guard_msgs in
-- #eval to_freud ""
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded