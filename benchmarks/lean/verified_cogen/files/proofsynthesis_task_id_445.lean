-- <vc-preamble>
@[reducible, simp]
def elementWiseMultiplication_precond (arr1 : Array Int) (arr2 : Array Int) :=
  arr1.size = arr2.size ∧ (∀ i, i < arr1.size → -2147483648 ≤ arr1[i]! * arr2[i]! ∧ arr1[i]! * arr2[i]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

#check elementWiseMultiplication_spec_satisfied