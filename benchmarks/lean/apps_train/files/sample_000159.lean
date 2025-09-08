/-
Given two strings text1 and text2, return the length of their longest common subsequence.
A subsequence of a string is a new string generated from the original string with some characters(can be none) deleted without changing the relative order of the remaining characters. (eg, "ace" is a subsequence of "abcde" while "aec" is not). A common subsequence of two strings is a subsequence that is common to both strings.

If there is no common subsequence, return 0.

Example 1:
Input: text1 = "abcde", text2 = "ace" 
Output: 3  
Explanation: The longest common subsequence is "ace" and its length is 3.

Example 2:
Input: text1 = "abc", text2 = "abc"
Output: 3
Explanation: The longest common subsequence is "abc" and its length is 3.

Example 3:
Input: text1 = "abc", text2 = "def"
Output: 0
Explanation: There is no such common subsequence, so the result is 0.

Constraints:

1 <= text1.length <= 1000
1 <= text2.length <= 1000
The input strings consist of lowercase English characters only.
-/

-- <vc-helpers>
-- </vc-helpers>

def longest_common_subsequence (s1 s2 : String) : Nat :=
  sorry

theorem lcs_length_bounded (s1 s2 : String) :
  longest_common_subsequence s1 s2 ≤ s1.length ∧ 
  longest_common_subsequence s1 s2 ≤ s2.length :=
  sorry

theorem lcs_empty (s : String) :
  longest_common_subsequence s "" = 0 ∧
  longest_common_subsequence "" s = 0 :=
  sorry

theorem lcs_identical (s : String) :
  longest_common_subsequence s s = s.length :=
  sorry

theorem lcs_symmetric (s1 s2 : String) :
  longest_common_subsequence s1 s2 = longest_common_subsequence s2 s1 :=
  sorry

theorem lcs_substring (s1 s2 s3 : String) :
  longest_common_subsequence (s1 ++ s2) s3 ≥ longest_common_subsequence s1 s3 ∧
  longest_common_subsequence (s1 ++ s2) s3 ≥ longest_common_subsequence s2 s3 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval longest_common_subsequence "abcde" "ace"

/-
info: 3
-/
-- #guard_msgs in
-- #eval longest_common_subsequence "abc" "abc"

/-
info: 0
-/
-- #guard_msgs in
-- #eval longest_common_subsequence "abc" "def"

-- Apps difficulty: interview
-- Assurance level: unguarded