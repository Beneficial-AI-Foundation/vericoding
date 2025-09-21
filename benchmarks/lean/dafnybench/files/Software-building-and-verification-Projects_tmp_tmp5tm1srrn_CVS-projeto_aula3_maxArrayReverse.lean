-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxArrayReverse (arr : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxArrayReverse_spec (arr : Array Int) :
arr.size > 0 →
(∀ i : Nat, 0 ≤ i ∧ i < arr.size → arr[i]! ≤ maxArrayReverse arr) ∧
(∃ x : Nat, 0 ≤ x ∧ x < arr.size ∧ arr[x]! = maxArrayReverse arr) :=
sorry
-- </vc-theorems>