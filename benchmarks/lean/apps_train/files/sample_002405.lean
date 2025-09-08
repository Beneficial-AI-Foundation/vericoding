/-
Given alphanumeric string s. (Alphanumeric string is a string consisting of lowercase English letters and digits).
You have to find a permutation of the string where no letter is followed by another letter and no digit is followed by another digit. That is, no two adjacent characters have the same type.
Return the reformatted string or return an empty string if it is impossible to reformat the string.

Example 1:
Input: s = "a0b1c2"
Output: "0a1b2c"
Explanation: No two adjacent characters have the same type in "0a1b2c". "a0b1c2", "0a1b2c", "0c2a1b" are also valid permutations.

Example 2:
Input: s = "leetcode"
Output: ""
Explanation: "leetcode" has only characters so we cannot separate them by digits.

Example 3:
Input: s = "1229857369"
Output: ""
Explanation: "1229857369" has only digits so we cannot separate them by characters.

Example 4:
Input: s = "covid2019"
Output: "c2o0v1i9d"

Example 5:
Input: s = "ab123"
Output: "1a2b3"

Constraints:

1 <= s.length <= 500
s consists of only lowercase English letters and/or digits.
-/

def isAlpha (c : Char) : Bool := sorry
def isDigit (c : Char) : Bool := sorry

def reformat (s : String) : String := sorry

theorem reformat_empty_string (s : String) : 
  let letters := s.data.filter isAlpha |>.length
  let digits := s.data.filter isDigit |>.length
  letters - digits > 1 ∨ digits - letters > 1 →
  reformat s = "" := sorry

def countLetters (s : String) : Nat :=
  s.data.filter isAlpha |>.length

-- <vc-helpers>
-- </vc-helpers>

def countDigits (s : String) : Nat :=
  s.data.filter isDigit |>.length

theorem reformat_preserves_length (s : String) :
  reformat s ≠ "" → 
  (reformat s).length = s.length := sorry 

theorem reformat_preserves_chars (s : String) :
  reformat s ≠ "" →
  (reformat s).data = s.data := sorry

theorem reformat_alternates (s : String) :
  reformat s ≠ "" →
  ∀ i < (reformat s).length - 1,
    (isAlpha ((reformat s).data[i]!) = !isAlpha ((reformat s).data[i+1]!)) := sorry

theorem reformat_preserves_letter_count (s : String) :
  reformat s ≠ "" →
  countLetters (reformat s) = countLetters s := sorry

theorem reformat_preserves_digit_count (s : String) :
  reformat s ≠ "" →
  countDigits (reformat s) = countDigits s := sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval reformat "leetcode"

-- Apps difficulty: introductory
-- Assurance level: unguarded