-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def anagrams (word : String) (words : List String) : List String :=
sorry

def sameLetters (word1 word2 : String) : Bool :=
sorry

def reverseString (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem anagram_properties (word : String) (words : List String) :
  let result := anagrams word words

  (∀ w ∈ result, w ∈ words) ∧

  (∀ w ∈ result, String.length w = String.length word) ∧

  (∀ w ∈ result, sameLetters w word) ∧

  (∀ w ∈ words, sameLetters w word → w ∈ result) :=
sorry

theorem empty_list (word : String) :
  anagrams word [] = [] :=
sorry

theorem same_word (word : String) :
  anagrams word [word] = [word] :=
sorry

theorem reversed_word (word : String) :
  let reversed := reverseString word
  anagrams word [reversed] = [reversed] :=
sorry
-- </vc-theorems>