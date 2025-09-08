/-
Given a string s. An awesome substring is a non-empty substring of s such that we can make any number of swaps in order to make it palindrome.
Return the length of the maximum length awesome substring of s.

Example 1:
Input: s = "3242415"
Output: 5
Explanation: "24241" is the longest awesome substring, we can form the palindrome "24142" with some swaps.

Example 2:
Input: s = "12345678"
Output: 1

Example 3:
Input: s = "213123"
Output: 6
Explanation: "213123" is the longest awesome substring, we can form the palindrome "231132" with some swaps.

Example 4:
Input: s = "00"
Output: 2

Constraints:

1 <= s.length <= 10^5
s consists only of digits.
-/

def longest_awesome_substring (s : String) : Nat := sorry

def is_digit (c : Char) : Bool := 
  '0' ≤ c ∧ c ≤ '9'

-- <vc-helpers>
-- </vc-helpers>

def string_reversal (s : String) : String := sorry

theorem valid_length (s : String) (h : s.length > 0) (h2 : ∀ c ∈ s.data, is_digit c) :
  let result := longest_awesome_substring s
  1 ≤ result ∧ result ≤ s.length := sorry

theorem repeated_digit_awesome (d : Char) (n : Nat) (h : is_digit d) (h2 : n > 0) :
  let s := String.mk (List.replicate n d)
  longest_awesome_substring s = s.length := sorry

theorem palindrome_awesome (s : String) (h : s.length > 0) (h2 : ∀ c ∈ s.data, is_digit c) :
  let palindrome := s ++ string_reversal s
  longest_awesome_substring palindrome = palindrome.length := sorry

theorem single_odd_count_awesome (d1 d2 : Char) (h1 : is_digit d1) (h2 : is_digit d2) (h3 : d1 ≠ d2) :
  let s := String.mk (List.replicate 10 d1 ++ [d2]) 
  longest_awesome_substring s ≥ 11 := sorry

theorem reversal_invariant (s : String) (h : s.length > 0) (h2 : ∀ c ∈ s.data, is_digit c) :
  longest_awesome_substring s = longest_awesome_substring (string_reversal s) := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval longest_awesome_substring "3242415"

/-
info: 1
-/
-- #guard_msgs in
-- #eval longest_awesome_substring "12345678"

/-
info: 6
-/
-- #guard_msgs in
-- #eval longest_awesome_substring "213123"

-- Apps difficulty: interview
-- Assurance level: unguarded