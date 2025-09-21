-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LongestCommonPrefix (str1 : Array Char) (str2 : Array Char) : Array Char :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem LongestCommonPrefix_spec (str1 : Array Char) (str2 : Array Char) (_prefix : Array Char) :
_prefix.size ≤ str1.size ∧
_prefix.size ≤ str2.size ∧
(∀ i, i < _prefix.size → _prefix[i]! = str1[i]!) ∧
(∀ i, i < _prefix.size → _prefix[i]! = str2[i]!) ∧
(_prefix.size = str1.size ∨
_prefix.size = str2.size ∨
str1[_prefix.size]! ≠ str2[_prefix.size]!) :=
sorry
-- </vc-theorems>