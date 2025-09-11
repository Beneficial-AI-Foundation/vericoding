-- <vc-preamble>
def reverseAndCombineText (text : String) : String := sorry 

-- Result length should match total chars across merged words
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countChar (c : Char) (s : String) : Nat :=
  (s.toList.filter (· = c)).length
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input_chars (text : String) : 
  String.length (reverseAndCombineText text) = 
  String.length (String.replace text " " "") := sorry

-- All input chars should appear in output in same quantities

theorem chars_preserved (text : String) (c : Char) : 
  countChar c (String.replace text " " "") = 
  countChar c (reverseAndCombineText text) := sorry

-- Number of words should roughly halve each iteration

theorem halves_words_per_iteration (text : String) :
  let wordCount := (text.split (· = ' ')).length
  let maxIterations := if wordCount ≤ 1 then 0 
                       else (wordCount - 1).log2 + 1
  ∀ result : String, result = reverseAndCombineText text →
  (result.split (· = ' ')).length ≤ 
    if wordCount ≤ 1 then 1 else wordCount / (2 ^ maxIterations) := sorry

/-
info: 'cbafed'
-/
-- #guard_msgs in
-- #eval reverse_and_combine_text "abc def"

/-
info: 'defabcjklghi'
-/
-- #guard_msgs in
-- #eval reverse_and_combine_text "abc def ghi jkl"

/-
info: 'trzwqfdstrteettr45hh4325543544hjhjh21lllll'
-/
-- #guard_msgs in
-- #eval reverse_and_combine_text "234hh54 53455 sdfqwzrt rtteetrt hjhjh lllll12  44"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded