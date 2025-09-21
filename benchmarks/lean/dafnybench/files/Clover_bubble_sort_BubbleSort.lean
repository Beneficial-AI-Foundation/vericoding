-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BubbleSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BubbleSort_spec (a : Array Int) :
let result := BubbleSort a

-- Array is sorted in ascending order

(∀ i j, 0 ≤ i → i < j → j < result.size → result[i]! ≤ result[j]!) ∧

-- Output is a permutation of input (simplified)

result.size = a.size :=
sorry
-- </vc-theorems>