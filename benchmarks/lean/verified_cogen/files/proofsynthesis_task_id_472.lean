-- <vc-preamble>
@[reducible, simp]
def containsConsecutiveNumbers_precond (arr : Array Int) : Prop :=
  arr.size > 0 ∧ (∀ i, i < arr.size → 0 ≤ arr[i]! + 1 ∧ arr[i]! + 1 < 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

#check containsConsecutiveNumbers