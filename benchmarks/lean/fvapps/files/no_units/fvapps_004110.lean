-- <vc-preamble>
def anagrams (word : String) (words : List String) : List String := sorry

def sameLetters (word1 word2 : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseString (s : String) : String := sorry

theorem anagram_properties (word : String) (words : List String) :
  let result := anagrams word words
  -- Result is subset of input
  (∀ w ∈ result, w ∈ words) ∧ 
  -- Each result same length as input
  (∀ w ∈ result, String.length w = String.length word) ∧
  -- Each result has same letters
  (∀ w ∈ result, sameLetters w word) ∧
  -- Contains all valid anagrams
  (∀ w ∈ words, sameLetters w word → w ∈ result) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list (word : String) :
  anagrams word [] = [] := sorry

theorem same_word (word : String) :
  anagrams word [word] = [word] := sorry 

theorem reversed_word (word : String) :
  let reversed := reverseString word
  anagrams word [reversed] = [reversed] := sorry
-- </vc-theorems>