/-
Given a string s, determine if it is valid.
A string s is valid if, starting with an empty string t = "", you can transform t into s after performing the following operation any number of times:

Insert string "abc" into any position in t. More formally, t becomes tleft + "abc" + tright, where t == tleft + tright. Note that tleft and tright may be empty.

Return true if s is a valid string, otherwise, return false.

Example 1:
Input: s = "aabcbc"
Output: true
Explanation:
"" -> "abc" -> "aabcbc"
Thus, "aabcbc" is valid.
Example 2:
Input: s = "abcabcababcc"
Output: true
Explanation:
"" -> "abc" -> "abcabc" -> "abcabcabc" -> "abcabcababcc"
Thus, "abcabcababcc" is valid.

Example 3:
Input: s = "abccba"
Output: false
Explanation: It is impossible to get "abccba" using the operation.

Example 4:
Input: s = "cababc"
Output: false
Explanation: It is impossible to get "cababc" using the operation.

Constraints:

1 <= s.length <= 2 * 104
s consists of letters 'a', 'b', and 'c'
-/

-- <vc-helpers>
-- </vc-helpers>

def is_valid (s : String) : Bool := sorry

theorem valid_empty_string :
  is_valid "" = true := sorry

theorem valid_after_abc_removal (s : String) :
  is_valid s = is_valid (s.replace "abc" "") := sorry

theorem valid_implies_empty_after_abc_removal {s : String} :
  is_valid s = true → 
  (let final := s.replace "abc" "";
   final = "") := sorry

theorem invalid_with_other_chars {s : String} :
  s.contains 'd' → 
  is_valid s = false := sorry

theorem valid_when_only_abc_remains {s : String} :
  s.replace "abc" "" = "" →
  is_valid s = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_valid "aabcbc"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_valid "abcabcababcc"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_valid "abccba"

-- Apps difficulty: interview
-- Assurance level: unguarded