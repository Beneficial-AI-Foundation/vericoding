/-
Given the string s, return the size of the longest substring containing each vowel an even number of times. That is, 'a', 'e', 'i', 'o', and 'u' must appear an even number of times.

Example 1:
Input: s = "eleetminicoworoep"
Output: 13
Explanation: The longest substring is "leetminicowor" which contains two each of the vowels: e, i and o and zero of the vowels: a and u.

Example 2:
Input: s = "leetcodeisgreat"
Output: 5
Explanation: The longest substring is "leetc" which contains two e's.

Example 3:
Input: s = "bcbcbc"
Output: 6
Explanation: In this case, the given string "bcbcbc" is the longest because all vowels: a, e, i, o and u appear zero times.

Constraints:

1 <= s.length <= 5 x 10^5
s contains only lowercase English letters.
-/

def countVowels (s : String) : List Char → Bool :=
  sorry

def verifySubstringVowels (s : String) (start length : Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def findLongestEvenVowelSubstring (s : String) : Nat :=
  sorry

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

/-
info: 13
-/
-- #guard_msgs in
-- #eval find_longest_even_vowel_substring "eleetminicoworoep"

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_longest_even_vowel_substring "leetcodeisgreat"

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_longest_even_vowel_substring "bcbcbc"

-- Apps difficulty: interview
-- Assurance level: unguarded