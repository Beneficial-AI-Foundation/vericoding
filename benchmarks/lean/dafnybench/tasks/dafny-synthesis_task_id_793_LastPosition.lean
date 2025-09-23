-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LastPosition (arr : Array Int) (elem : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem LastPosition_spec (arr : Array Int) (elem : Int) :
arr.size > 0 ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < arr.size → arr[i]! ≤ arr[j]!) →
let pos := LastPosition arr elem
(pos = -1 ∨
(0 ≤ pos ∧ pos < arr.size ∧
arr[pos.toNat]! = elem ∧
(pos ≤ arr.size - 1 ∨ arr[(pos + 1).toNat]! > elem))) ∧
(∀ i, 0 ≤ i ∧ i < arr.size → arr[i]! = arr[i]!) :=
sorry
-- </vc-theorems>