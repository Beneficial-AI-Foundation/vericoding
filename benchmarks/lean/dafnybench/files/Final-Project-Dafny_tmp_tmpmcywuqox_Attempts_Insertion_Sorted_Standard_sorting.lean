-- <vc-preamble>
def InsertionSorted (arr : Array Int) (left : Nat) (right : Nat) : Prop :=
0 ≤ left ∧ left ≤ right ∧ right ≤ arr.size ∧
∀ i j, left ≤ i ∧ i < j ∧ j < right → arr[i]! ≤ arr[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sorting (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorting_spec (arr : Array Int) :
arr.size > 1 →
InsertionSorted (sorting arr) 0 (sorting arr).size :=
sorry
-- </vc-theorems>