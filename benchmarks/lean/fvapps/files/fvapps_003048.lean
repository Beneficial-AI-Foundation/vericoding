-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseWords (s : String) : String := sorry

theorem reverseWords_roundtrip (word_list : List String) (h : word_list.length > 0) :
  let sentence := String.intercalate " " word_list
  reverseWords (reverseWords sentence) = sentence := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverseWords_preserves_word_count (word_list : List String) 
  (h1 : word_list.length ≥ 2) (h2 : word_list.length ≤ 10) :
  let sentence := String.intercalate " " word_list
  let reversed := reverseWords sentence
  (sentence.split (· = ' ')).length = (reversed.split (· = ' ')).length := sorry

theorem reverseWords_empty_string :
  reverseWords "" = "" := sorry

theorem reverseWords_multiple_spaces :
  reverseWords "a  b  c" = "c  b  a" := sorry
-- </vc-theorems>