-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SelectionSort (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SelectionSort_spec (a : Array Int) :
let result := SelectionSort a

-- Array is sorted in ascending order

(∀ i j, 0 ≤ i → i < j → j < result.size → result[i]! ≤ result[j]!) ∧

-- Output is a permutation of input

(result.toList = a.toList) :=
sorry
-- </vc-theorems>