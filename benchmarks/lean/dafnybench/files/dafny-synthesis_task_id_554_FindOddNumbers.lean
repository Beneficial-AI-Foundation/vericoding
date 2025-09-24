-- <vc-preamble>
def IsOdd (n : Int) : Bool :=
n % 2 = 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindOddNumbers (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindOddNumbers_spec (arr : Array Int) :
let result := FindOddNumbers arr
(∀ i, 0 ≤ i ∧ i < result.size → IsOdd (result[i]!) ∧ (∃ j, 0 ≤ j ∧ j < arr.size ∧ result[i]! = arr[j]!)) ∧
(∀ i, 0 ≤ i ∧ i < arr.size ∧ IsOdd (arr[i]!) → (∃ j, 0 ≤ j ∧ j < result.size ∧ arr[i]! = result[j]!)) :=
sorry
-- </vc-theorems>