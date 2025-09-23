-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindFirstOccurrence (arr : Array Int) (target : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindFirstOccurrence_spec
(arr : Array Int) (target : Int) :
(∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.size → arr[i]! ≤ arr[j]!) →
let result := FindFirstOccurrence arr target
(0 ≤ result ∧ result < arr.size → arr[result.toNat]! = target) ∧
(result = -1 → ∀ i, 0 ≤ i ∧ i < arr.size → arr[i]! ≠ target) :=
sorry
-- </vc-theorems>