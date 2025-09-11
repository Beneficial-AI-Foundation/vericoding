-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def format_poem (s : String) : String := sorry

theorem format_poem_single_sentence (text : String) 
  (h : ¬ (text.contains '.' )) : 
  format_poem text = text ++ "." := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem format_poem_basic_sentences :
  format_poem "First sentence. Second sentence. Third sentence" = 
  "First sentence.\nSecond sentence.\nThird sentence." := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval format_poem "Beautiful is better than ugly. Explicit is better than implicit. Simple is better than complex. Complex is better than complicated."

/-
info: expected2
-/
-- #guard_msgs in
-- #eval format_poem "Flat is better than nested. Sparse is better than dense. Readability counts. Special cases aren"t special enough to break the rules."

/-
info: expected3
-/
-- #guard_msgs in
-- #eval format_poem "If the implementation is hard to explain, it"s a bad idea. If the implementation is easy to explain, it may be a good idea."
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded