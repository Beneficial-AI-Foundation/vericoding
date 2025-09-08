/-
Given a string s, you are allowed to convert it to a palindrome by adding characters in front of it. Find and return the shortest palindrome you can find by performing this transformation.

Example 1:

Input: "aacecaaa"
Output: "aaacecaaa"

Example 2:

Input: "abcd"
Output: "dcbabcd"
-/

def shortest_palindrome (s : String) : String := sorry

def isPalindrome (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def stringReverse (s : String) : String := sorry

theorem shortest_palindrome_contains_original (s : String) :
  (shortest_palindrome s).endsWith s := sorry

theorem shortest_palindrome_is_palindrome (s : String) :
  isPalindrome (shortest_palindrome s) = true := sorry

theorem shortest_palindrome_minimal_length (s : String) :
  (shortest_palindrome s).length ≤ 2 * s.length := sorry

theorem shortest_palindrome_empty_single_char (s : String) :
  s = "" ∨ s.length = 1 → shortest_palindrome s = s := sorry

theorem shortest_palindrome_starts_with_reversed_suffix (s : String) :
  s ≠ "" →
  let result := shortest_palindrome s
  let suffixLen := result.length - s.length
  suffixLen > 0 →
  (result.take suffixLen) = stringReverse (s.takeRight suffixLen) := sorry

theorem shortest_palindrome_single_char_string (s : String) (c : Char) :
  s.all (· = c) → shortest_palindrome s = s := sorry

/-
info: 'aaacecaaa'
-/
-- #guard_msgs in
-- #eval shortest_palindrome "aacecaaa"

/-
info: 'dcbabcd'
-/
-- #guard_msgs in
-- #eval shortest_palindrome "abcd"

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval shortest_palindrome "a"

-- Apps difficulty: interview
-- Assurance level: unguarded