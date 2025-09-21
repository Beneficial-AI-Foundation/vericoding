-- <vc-preamble>
@[reducible, simp]
def difference_precond (arr1 : Array Int) (arr2 : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def difference (arr1 : Array Int) (arr2 : Array Int) (h_precond : difference_precond arr1 arr2) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def difference_postcond (arr1 : Array Int) (arr2 : Array Int) (result: Array Int) (h_precond : difference_precond arr1 arr2) :=
  (∀ i, i < arr1.size → ¬(arr2.toList.contains arr1[i]!) → result.toList.contains arr1[i]!) ∧
  (∀ i, i < arr2.size → ¬(arr1.toList.contains arr2[i]!) → result.toList.contains arr2[i]!) ∧
  (∀ i j, i < j → j < result.size → result[i]! ≠ result[j]!)

theorem difference_spec_satisfied (arr1: Array Int) (arr2: Array Int) (h_precond : difference_precond arr1 arr2) :
    difference_postcond arr1 arr2 (difference arr1 arr2 h_precond) h_precond := by
  sorry
-- </vc-theorems>