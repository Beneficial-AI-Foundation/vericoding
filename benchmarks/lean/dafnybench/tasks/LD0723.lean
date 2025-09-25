-- <vc-preamble>
def IsNegative (n : Int) : Bool :=
n < 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindNegativeNumbers (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindNegativeNumbers_spec (arr : Array Int) :
let result := FindNegativeNumbers arr
(∀ i, 0 ≤ i ∧ i < result.size → IsNegative (result[i]!) ∧ (∃ j, 0 ≤ j ∧ j < arr.size ∧ result[i]! = arr[j]!)) ∧
(∀ i, 0 ≤ i ∧ i < arr.size ∧ IsNegative (arr[i]!) → (∃ j, 0 ≤ j ∧ j < result.size ∧ arr[i]! = result[j]!)) :=
sorry
-- </vc-theorems>