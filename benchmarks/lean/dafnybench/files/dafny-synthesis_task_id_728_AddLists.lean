-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def AddLists (a b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem AddLists_spec (a b : Array Int) :
a.size = b.size →
let result := AddLists a b
result.size = a.size ∧
∀ i, 0 ≤ i ∧ i < result.size → result[i]! = a[i]! + b[i]! :=
sorry
-- </vc-theorems>