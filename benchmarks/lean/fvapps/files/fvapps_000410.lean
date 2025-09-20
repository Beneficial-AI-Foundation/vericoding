-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countVowels (s : String) : List Char → Bool :=
  sorry

def verifySubstringVowels (s : String) (start length : Nat) : Bool :=
  sorry

def findLongestEvenVowelSubstring (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_valid_length (s : String) :
  let result := findLongestEvenVowelSubstring s
  0 ≤ result ∧ result ≤ s.length :=
sorry

theorem result_has_even_vowels (s : String) :
  let result := findLongestEvenVowelSubstring s
  result > 0 →
  ∃ i : Nat, i + result ≤ s.length ∧ verifySubstringVowels s i result :=
sorry

theorem no_longer_valid_substring_exists (s : String) :
  let result := findLongestEvenVowelSubstring s
  ∀ length : Nat, result < length → length ≤ s.length →
  ∀ i : Nat, i + length ≤ s.length →
  ¬(verifySubstringVowels s i length) :=
sorry

theorem edge_cases_empty :
  findLongestEvenVowelSubstring "" = 0 :=
sorry

theorem edge_cases_single_nonvowel (c : Char) (h : c ∉ ['a', 'e', 'i', 'o', 'u']) :
  findLongestEvenVowelSubstring (String.mk [c]) = 1 :=
sorry
-- </vc-theorems>