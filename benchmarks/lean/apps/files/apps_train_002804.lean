-- <vc-preamble>
def String.reverse (s : String) : String := sorry

def split (s : String) (sep : String) : List String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_sentence (s : String) : String := sorry

theorem word_count_preserved (words : List String) :
  let sentence := " ".intercalate words
  let reversed := reverse_sentence sentence
  (split sentence " ").length = (split reversed " ").length :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string :
  reverse_sentence "" = "" :=
sorry

theorem each_word_reversed (s : String) :
  let original_words := split s " "
  let result_words := split (reverse_sentence s) " "
  ∀ i, i < original_words.length →
    result_words[i]! = String.reverse original_words[i]! :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval reverse_sentence "Hello !Nhoj Want to have lunch?"

/-
info: expected2
-/
-- #guard_msgs in
-- #eval reverse_sentence "CodeWars rules!"

/-
info: expected3
-/
-- #guard_msgs in
-- #eval reverse_sentence ""
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded