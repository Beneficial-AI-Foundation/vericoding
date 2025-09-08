/-
A palindrome is a series of characters that read the same forwards as backwards such as "hannah", "racecar" and "lol".

For this Kata you need to write a function that takes a string of characters and returns the length, as an integer value, of longest alphanumeric palindrome that could be made by combining the characters in any order but using each character only once. The function should not be case sensitive.

For example if passed "Hannah" it should return 6 and if passed "aabbcc_yYx_" it should return 9 because one possible palindrome would be "abcyxycba".
-/

-- <vc-helpers>
-- </vc-helpers>

def longestPalindrome (s : String) : Nat :=
  sorry

theorem longestPalindrome_nonnegative (s : String) :
  longestPalindrome s ≥ 0 := sorry

theorem longestPalindrome_leq_alphanum_count (s : String) :
  longestPalindrome s ≤ (s.toList.filter Char.isAlphanum).length := sorry

theorem longestPalindrome_single_char (s : String) (h1 : s.length = 1) 
  (h2 : Char.isAlphanum (s.get 0)) :
  longestPalindrome s = 1 := sorry

theorem longestPalindrome_parity_odd (s : String) :
  let chars := s.toLower.toList.filter Char.isAlphanum
  let counts := fun c => (chars.filter (· = c)).length
  (∃ c, counts c % 2 = 1) →
  longestPalindrome s % 2 = 1 := sorry

theorem longestPalindrome_parity_even (s : String) :
  let chars := s.toLower.toList.filter Char.isAlphanum
  let counts := fun c => (chars.filter (· = c)).length
  (¬∃ c, counts c % 2 = 1) →
  longestPalindrome s > 0 →
  longestPalindrome s % 2 = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval longest_palindrome "A"

/-
info: 6
-/
-- #guard_msgs in
-- #eval longest_palindrome "Hannah"

/-
info: 13
-/
-- #guard_msgs in
-- #eval longest_palindrome "xyz__a_/b0110//a_zyx"

-- Apps difficulty: introductory
-- Assurance level: guarded