-- <vc-preamble>
@[reducible, simp]
def intersection_precond (arr1 : Array Int) (arr2 : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def intersection (arr1 : Array Int) (arr2 : Array Int) (h_precond : intersection_precond (arr1) (arr2)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def intersection_postcond (arr1 : Array Int) (arr2 : Array Int) (result: Array Int) (h_precond : intersection_precond (arr1) (arr2)) :=
  (∀ i, i < result.size → (arr1.contains result[i]! ∧ arr2.contains result[i]!)) ∧
  (∀ i j, i < j → j < result.size → result[i]! ≠ result[j]!)

theorem intersection_spec_satisfied (arr1: Array Int) (arr2: Array Int) (h_precond : intersection_precond (arr1) (arr2)) :
    intersection_postcond (arr1) (arr2) (intersection (arr1) (arr2) h_precond) h_precond := by
  sorry
-- </vc-theorems>