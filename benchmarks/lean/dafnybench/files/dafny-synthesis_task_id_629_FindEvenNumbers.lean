-- <vc-preamble>
def IsEven (n : Int) : Bool :=
n % 2 = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindEvenNumbers (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindEvenNumbers_spec (arr : Array Int) :
let result := FindEvenNumbers arr
(∀ i, 0 ≤ i ∧ i < result.size → IsEven (result[i]!) ∧ (result[i]!) ∈ arr.toList) ∧
(∀ i, 0 ≤ i ∧ i < arr.size ∧ IsEven (arr[i]!) → (arr[i]!) ∈ result.toList) :=
sorry
-- </vc-theorems>