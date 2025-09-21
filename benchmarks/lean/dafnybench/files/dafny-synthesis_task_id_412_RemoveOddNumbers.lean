-- <vc-preamble>
def IsEven (n : Int) : Prop :=
n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RemoveOddNumbers (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RemoveOddNumbers_spec (arr : Array Int) :
let result := RemoveOddNumbers arr
(∀ i, 0 ≤ i ∧ i < result.size → IsEven (result[i]!) ∧ (∃ j, 0 ≤ j ∧ j < arr.size ∧ result[i]! = arr[j]!)) ∧
(∀ i, 0 ≤ i ∧ i < arr.size ∧ IsEven (arr[i]!) → (∃ j, 0 ≤ j ∧ j < result.size ∧ arr[i]! = result[j]!)) :=
sorry
-- </vc-theorems>