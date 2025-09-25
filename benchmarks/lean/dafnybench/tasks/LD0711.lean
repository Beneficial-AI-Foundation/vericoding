-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IndexWiseAddition (a b : Array (Array Int)) : Array (Array Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IndexWiseAddition_spec (a b : Array (Array Int)) :
a.size > 0 ∧ b.size > 0 ∧
a.size = b.size ∧
(∀ i, 0 ≤ i ∧ i < a.size → (a[i]!).size = (b[i]!).size) →
let result := IndexWiseAddition a b
result.size = a.size ∧
(∀ i, 0 ≤ i ∧ i < result.size → (result[i]!).size = (a[i]!).size) ∧
(∀ i, 0 ≤ i ∧ i < result.size →
∀ j, 0 ≤ j ∧ j < (result[i]!).size →
(result[i]!)[j]! = (a[i]!)[j]! + (b[i]!)[j]!) :=
sorry
-- </vc-theorems>