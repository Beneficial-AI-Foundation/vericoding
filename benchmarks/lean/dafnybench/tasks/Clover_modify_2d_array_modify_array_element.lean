-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Array (Array Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem modify_array_element_spec
(arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) :
index1 < arr.size →
index2 < (arr[index1]!).size →
(∀ i j : Nat, i < arr.size ∧ j < arr.size ∧ i ≠ j → arr[i]! ≠ arr[j]!) →
let result := modify_array_element arr index1 index2 val
(∀ i : Nat, i < arr.size → result[i]! = arr[i]!) ∧
(∀ i j : Nat, i < arr.size ∧ j < (arr[i]!).size ∧ (i ≠ index1 ∨ j ≠ index2) →
(result[i]!)[j]! = (arr[i]!)[j]!) ∧
(result[index1]!)[index2]! = val :=
sorry
-- </vc-theorems>