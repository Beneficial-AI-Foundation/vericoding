-- <vc-preamble>
@[reducible, simp]
def addList_precond (arr1 : Array Int) (arr2 : Array Int) : Prop :=
  arr1.size = arr2.size ∧ (∀ i, i < arr1.size → -2147483648 ≤ arr1[i]! + arr2[i]! ∧ arr1[i]! + arr2[i]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def addList (arr1 : Array Int) (arr2 : Array Int) (h_precond : addList_precond arr1 arr2) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def addList_postcond (arr1 : Array Int) (arr2 : Array Int) (result: Array Int) (h_precond : addList_precond arr1 arr2) : Prop :=
  result.size = arr1.size ∧ (∀ i, i < result.size → result[i]! = arr1[i]! + arr2[i]!)

theorem addList_spec_satisfied (arr1: Array Int) (arr2: Array Int) (h_precond : addList_precond arr1 arr2) :
    addList_postcond arr1 arr2 (addList arr1 arr2 h_precond) h_precond := by
  sorry
-- </vc-theorems>