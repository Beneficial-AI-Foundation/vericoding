-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsPalindrome (x : Array Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsPalindrome_spec (x : Array Char) :
IsPalindrome x = true ↔
(∀ i, 0 ≤ i ∧ i < x.size → x[i]! = x[x.size - i - 1]!) :=
sorry
-- </vc-theorems>