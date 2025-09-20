-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPalindrome (s : String) : Bool :=
  sorry

def isSubstring (sub str : String) : Bool :=
  sorry

def longest_palindrome (s : String) : String :=
  sorry

def reverseString (s : String) : String :=
  sorry

def substring (s : String) (i j : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_palindrome {s : String} :
  let result := longest_palindrome s
  result = "" ∨ (result = reverseString result ∧ isSubstring result s)
  := by
sorry

theorem output_is_maximum_length {s : String} :
  let result := longest_palindrome s
  ∀ (i j : Nat), i ≤ s.length → j ≤ s.length →
    let substr := substring s i j
    substr = reverseString substr →
    substr.length ≤ result.length
  := by
sorry

theorem empty_and_single_char_inputs {s : String} :
  (s = "" → longest_palindrome s = "") ∧
  (s.length = 1 → longest_palindrome s = s)
  := by
sorry

theorem palindrome_input_returns_itself {s : String} :
  s ≠ "" →
  s = reverseString s →
  longest_palindrome s = s
  := by
sorry
-- </vc-theorems>