-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseString (s : String) : String := sorry

def spinWords (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spin_words_length_five_or_more {word : String} 
  (h : word.length ≥ 5) : 
  spinWords word = reverseString word := sorry

theorem spin_words_length_less_than_five {word : String} 
  (h : word.length < 5) : 
  spinWords word = word := sorry

theorem spin_words_preserves_length (word : String) :
  (spinWords word).length = word.length := sorry

theorem spin_words_empty : 
  spinWords "" = "" := sorry

/-
info: 'emocleW'
-/
-- #guard_msgs in
-- #eval spin_words "Welcome"

/-
info: 'Hey wollef sroirraw'
-/
-- #guard_msgs in
-- #eval spin_words "Hey fellow warriors"

/-
info: 'This ecnetnes is a ecnetnes'
-/
-- #guard_msgs in
-- #eval spin_words "This sentence is a sentence"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded