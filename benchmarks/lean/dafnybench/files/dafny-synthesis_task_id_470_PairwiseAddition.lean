-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def PairwiseAddition (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem PairwiseAddition_spec (a : Array Int) :
a.size % 2 = 0 →
let result := PairwiseAddition a
result.size = a.size / 2 ∧
∀ i, 0 ≤ i ∧ i < result.size →
result[i]! = a[2*i]! + a[2*i + 1]! :=
sorry
-- </vc-theorems>