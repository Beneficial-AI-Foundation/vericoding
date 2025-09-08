/-
Given a string s consists of upper/lower-case alphabets and empty space characters ' ', return the length of last word in the string.

If the last word does not exist, return 0.

Note: A word is defined as a character sequence consists of non-space characters only.

Example:

Input: "Hello World"
Output: 5
-/

def splitString (s: String) : List String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def lengthOfLastWord (s: String) : Nat :=
  sorry

theorem length_of_last_word_nonnegative (s: String) :
  lengthOfLastWord s ≥ 0 := sorry

theorem length_of_last_word_matches_split (s: String) :
  lengthOfLastWord s > 0 →
  match splitString s with
  | [] => True 
  | xs => lengthOfLastWord s = xs.getLast!.length
  := sorry

theorem length_of_last_word_empty_for_blank (s: String) :
  s.trim.isEmpty → lengthOfLastWord s = 0 := sorry

theorem length_of_last_word_ignores_trailing_spaces (s: String) :
  lengthOfLastWord s = lengthOfLastWord s.trim := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval length_of_last_word "Hello World"

/-
info: 0
-/
-- #guard_msgs in
-- #eval length_of_last_word "   "

/-
info: 7
-/
-- #guard_msgs in
-- #eval length_of_last_word "Hello   World   Program"

-- Apps difficulty: introductory
-- Assurance level: guarded