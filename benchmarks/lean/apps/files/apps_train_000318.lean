/-
Given a string, find the length of the longest substring without repeating characters.

Examples:

Given "abcabcbb", the answer is "abc", which the length is 3.

Given "bbbbb", the answer is "b", with the length of 1.

Given "pwwkew", the answer is "wke", with the length of 3. Note that the answer must be a substring, "pwke" is a subsequence and not a substring.
-/

-- <vc-helpers>
-- </vc-helpers>

def lengthOfLongestSubstring (s : String) : Nat :=
  sorry

theorem length_bounds (s : String) :
  0 ≤ lengthOfLongestSubstring s ∧ lengthOfLongestSubstring s ≤ s.length := by
  sorry

theorem single_char_string (s : String) (h : s.data.eraseDups.length = 1) :
  lengthOfLongestSubstring s = 1 := by
  sorry

theorem empty_and_single (s : String) :
  (s = "") → lengthOfLongestSubstring s = 0 ∧
  (s.length = 1) → lengthOfLongestSubstring s = 1 := by
  sorry

theorem unique_chars (s : String) :
  s.data.eraseDups.length = s.length →
  lengthOfLongestSubstring s = s.length := by
  sorry

theorem concat_size (s₁ s₂ : String) :
  lengthOfLongestSubstring (s₁ ++ s₂) ≥ 
    max (lengthOfLongestSubstring s₁) (lengthOfLongestSubstring s₂) := by
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval lengthOfLongestSubstring "abcabcbb"

/-
info: 1
-/
-- #guard_msgs in
-- #eval lengthOfLongestSubstring "bbbbb"

/-
info: 3
-/
-- #guard_msgs in
-- #eval lengthOfLongestSubstring "pwwkew"

-- Apps difficulty: interview
-- Assurance level: guarded