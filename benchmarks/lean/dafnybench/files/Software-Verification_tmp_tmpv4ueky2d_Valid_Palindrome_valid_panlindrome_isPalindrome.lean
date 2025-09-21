-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPalindrome (s : Array Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isPalindrome_spec (s : Array Char) :
1 ≤ s.size ∧ s.size ≤ 200000 →
isPalindrome s = ∀ i, 0 ≤ i ∧ i < s.size / 2 → s[i]! = s[s.size - 1 - i]! :=
sorry
-- </vc-theorems>