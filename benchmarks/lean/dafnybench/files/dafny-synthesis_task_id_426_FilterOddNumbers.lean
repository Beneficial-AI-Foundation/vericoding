-- <vc-preamble>
def IsOdd (n : Int) : Bool :=
n % 2 ≠ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FilterOddNumbers (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FilterOddNumbers_spec (arr : Array Int) :
let result := FilterOddNumbers arr
(∀ i, 0 ≤ i ∧ i < result.size → IsOdd (result[i]!) ∧ (result[i]!) ∈ arr.toList) ∧
(∀ i, 0 ≤ i ∧ i < arr.size ∧ IsOdd (arr[i]!) → (arr[i]!) ∈ result.toList) :=
sorry
-- </vc-theorems>