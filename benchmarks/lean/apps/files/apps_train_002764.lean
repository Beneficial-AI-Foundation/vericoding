-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filter_words (s : String) : String := sorry

theorem filter_words_first_char_upper {s : String} (h : filter_words s ≠ "") :
  (filter_words s).length > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem filter_words_rest_lowercase {s : String} (h : (filter_words s).length > 1) :
  ∀ (i : String.Pos), (filter_words s).get i = (filter_words s).get i := sorry

theorem filter_words_no_double_spaces (s : String) :
  ¬ (filter_words s).contains ' ' := sorry

theorem filter_words_no_leading_trailing_spaces (s : String) :
  filter_words s = (filter_words s).trim := sorry

theorem filter_words_preserves_word_count (s : String) :
  (filter_words s).split (· = ' ') = s.split (· = ' ') := sorry 

theorem filter_words_empty_produces_empty (s : String) 
  (h : s = "" ∨ s = " " ∨ s = "  ") : filter_words s = "" := sorry

/-
info: 'Hello world!'
-/
-- #guard_msgs in
-- #eval filter_words "HELLO world!"

/-
info: 'This will not pass'
-/
-- #guard_msgs in
-- #eval filter_words "This    will    not    pass "

/-
info: 'Now this is a very exciting test!'
-/
-- #guard_msgs in
-- #eval filter_words "NOW THIS is a VERY EXCITING test!"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded