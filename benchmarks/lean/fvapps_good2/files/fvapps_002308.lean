-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_anagram (s t : String) : Bool :=
  sorry

def reverse (s : String) : String :=
  sorry

def isPermutation (s t : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_is_anagram_of_itself (s : String) :
  is_anagram s s = true :=
sorry

theorem different_length_strings_not_anagrams {s t : String}
  (h : s.length ≠ t.length) :
  is_anagram s t = false :=
sorry

theorem reversed_string_is_anagram (s : String) :
  is_anagram s (reverse s) = true :=
sorry

theorem permuted_string_is_anagram (s t : String)
  (h : isPermutation s t) :
  is_anagram s t = true :=
sorry
-- </vc-theorems>