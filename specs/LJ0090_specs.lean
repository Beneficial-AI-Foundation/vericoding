-- <vc-preamble>
@[reducible, simp]
def elementWiseMultiplication_precond (arr1 : Array Int) (arr2 : Array Int) :=
  arr1.size = arr2.size ∧ (∀ i, i < arr1.size → -2147483648 ≤ arr1[i]! * arr2[i]! ∧ arr1[i]! * arr2[i]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elementWiseMultiplication (arr1 : Array Int) (arr2 : Array Int) (h_precond : elementWiseMultiplication_precond arr1 arr2) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def elementWiseMultiplication_postcond (arr1 : Array Int) (arr2 : Array Int) (result: Array Int) (h_precond : elementWiseMultiplication_precond arr1 arr2) :=
  result.size = arr1.size ∧ (∀ i, i < result.size → result[i]! = arr1[i]! * arr2[i]!)

theorem elementWiseMultiplication_spec_satisfied (arr1: Array Int) (arr2: Array Int) (h_precond : elementWiseMultiplication_precond arr1 arr2) :
    elementWiseMultiplication_postcond arr1 arr2 (elementWiseMultiplication arr1 arr2 h_precond) h_precond := by
  sorry
-- </vc-theorems>