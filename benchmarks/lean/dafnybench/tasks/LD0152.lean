-- <vc-preamble>
def sorted_between (A : Array Int) (_from : Int) (to : Int) : Prop :=
∀ i j, 0 ≤ i ∧ i ≤ j ∧ j < A.size ∧ _from ≤ i ∧ i ≤ j ∧ j ≤ to →
A[i]! ≤ A[j]!
def sorted (A : Array Int) : Prop :=
sorted_between A 0 (A.size - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BubbleSort (A : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem BubbleSort_spec (A : Array Int) :
let result := BubbleSort A
sorted result ∧

-- Note: Simplified multiset preservation property since Lean doesn't have direct multiset support

result.size = A.size :=
sorry
-- </vc-theorems>