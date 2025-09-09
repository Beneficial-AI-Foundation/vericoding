/-
Given a string, your task is to count how many palindromic substrings in this string.

The substrings with different start indexes or end indexes are counted as different substrings even they consist of same characters. 

Example 1:

Input: "abc"
Output: 3
Explanation: Three palindromic strings: "a", "b", "c".

Example 2:

Input: "aaa"
Output: 6
Explanation: Six palindromic strings: "a", "a", "a", "aa", "aa", "aaa".

Note:

The input string length won't exceed 1000.
-/

def count_palindromic_substrings (s: String) : Nat :=
  sorry

def is_palindrome (s : String) : Bool :=
  sorry

def string_reverse (s : String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def string_repeat (c : Char) (n : Nat) : String :=
  sorry

theorem minimum_palindromes (s : String) (h : s.length > 0) : 
  count_palindromic_substrings s ≥ s.length :=
sorry 

theorem empty_string :
  count_palindromic_substrings "" = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_palindromic_substrings "abc"

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_palindromic_substrings "aaa"

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_palindromic_substrings "racecar"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible