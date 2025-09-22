-- <vc-preamble>
def IsSorted (s : Array Int) : Prop :=
∀ p q, 0 ≤ p → p < q → q < s.size → s[p]! ≤ s[q]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def InsertionSort (s : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem InsertionSort_spec (s : Array Int) :
let r := InsertionSort s
(r = s) ∧ IsSorted r :=
sorry
-- </vc-theorems>