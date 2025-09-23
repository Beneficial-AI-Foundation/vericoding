-- <vc-preamble>
def isPalindrome (s : String) : Bool := sorry

def isSubsequence (sub orig : String) : Bool := sorry

def startsWithStr (s pre : String) : Bool := sorry

/- Function that finds a palindrome supersequence of a given string -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_palindrome_supersequence (s : String) : String := sorry

/- The result is a palindrome -/
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_palindrome (s : String) :
  let result := find_palindrome_supersequence s
  isPalindrome result = true := sorry

/- The original string is a subsequence of the result -/

theorem original_is_subsequence (s : String) :
  let result := find_palindrome_supersequence s
  isSubsequence s result = true := sorry

/- The length of the result is twice the original length -/

theorem length_property (s : String) :
  let result := find_palindrome_supersequence s
  result.length = 2 * s.length := sorry

/- The result starts with the original string -/

theorem starts_with_original (s : String) :
  let result := find_palindrome_supersequence s
  startsWithStr result s = true := sorry

/- Empty string case -/

theorem empty_string :
  find_palindrome_supersequence "" = "" := sorry

end PalindromeSupersequence

/-
info: 'abaaba'
-/
-- #guard_msgs in
-- #eval find_palindrome_supersequence "aba"

/-
info: 'abba'
-/
-- #guard_msgs in
-- #eval find_palindrome_supersequence "ab"

/-
info: 'abcabbacba'
-/
-- #guard_msgs in
-- #eval find_palindrome_supersequence "abcab"
-- </vc-theorems>