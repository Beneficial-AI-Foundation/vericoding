-- <vc-preamble>
partial def count (arr : Array Int) (value : Int) : Nat :=
if arr.size = 0 then
0
else
(if arr[0]! = value then 1 else 0) + count (arr.extract 1 arr.size) value
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swap (arr : Array Int) (i j : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap_spec (arr : Array Int) (i j : Nat) :
arr.size > 0 ∧
0 ≤ i ∧ i < arr.size ∧
0 ≤ j ∧ j < arr.size →
let result := swap arr i j
result.size = arr.size ∧
result[i]! = arr[j]! ∧
result[j]! = arr[i]! ∧
(∀ k, 0 ≤ k ∧ k < arr.size ∧ k ≠ i ∧ k ≠ j → result[k]! = arr[k]!) :=
sorry
-- </vc-theorems>