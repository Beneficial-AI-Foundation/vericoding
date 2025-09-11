-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def evenize_word (word : String) : String := sorry

def evenator (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem evenize_word_properties (word : String) (h : word.length > 0) : 
  let result := evenize_word word
  (result.length % 2 = 0) ∧ 
  (result.startsWith word) ∧
  (word.length % 2 = 1 → result = word ++ word.back.toString) ∧
  (word.length % 2 = 0 → result = word) := sorry

theorem evenator_properties (words : List String) :
  let input_string := String.join words
  let result := evenator input_string
  let result_words := result.split (· = ' ')
  (∀ w ∈ result_words, w.length % 2 = 0) ∧
  (∀ c ∈ result.data, c.isAlphanum ∨ c.isWhitespace) ∧
  (let input_alnum_words := (input_string.split (· = ' ')).filter (fun w => ∃ c ∈ w.data, c.isAlphanum)
   result_words.length = input_alnum_words.length) := sorry

theorem evenator_empty_and_whitespace (s : String) 
  (h : ∀ c ∈ s.data, ¬c.isAlpha ∧ ¬c.isDigit) :
  evenator s = "" := sorry

/-
info: 'II gott aa hole in 11'
-/
-- #guard_msgs in
-- #eval evenator "I got a hole in 1!"

/-
info: 'hi howw aree youu Byee'
-/
-- #guard_msgs in
-- #eval evenator test2

/-
info: 'underr thee seAA'
-/
-- #guard_msgs in
-- #eval evenator test3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded