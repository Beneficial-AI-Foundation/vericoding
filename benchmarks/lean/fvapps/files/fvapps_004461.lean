-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def buildPalindrome (s : String) : String := sorry

def isSubstring (sub str : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_palindrome (s : String) (h : s.length > 0) :
  let result := buildPalindrome s
  result.data = result.data.reverse := sorry

theorem original_string_is_substring (s : String) (h : s.length > 0) :
  let result := buildPalindrome s
  isSubstring s result = true := sorry

theorem minimal_length (s : String) (h : s.length > 0) :
  let result := buildPalindrome s
  (result.length ≥ s.length) ∧ 
  (∀ sub : String, sub.length < result.length → 
    (sub.data = sub.data.reverse ∧ isSubstring s sub = true) → False) := sorry

theorem preserved_characters (s : String) (h : s.length > 0) :
  let result := buildPalindrome s
  ∀ c : Char, 
    result.data.count c ≥ s.data.count c := sorry
-- </vc-theorems>