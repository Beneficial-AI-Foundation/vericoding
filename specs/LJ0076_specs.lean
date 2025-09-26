-- <vc-preamble>
@[reducible, simp]
def elementWiseDivision_precond (arr1 : Array UInt32) (arr2 : Array UInt32) : Prop :=
  arr1.size = arr2.size ∧ 
  (∀ i, i < arr2.size → arr2[i]! ≠ 0) ∧
  (∀ m, m < arr1.size → True)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elementWiseDivision (arr1 : Array UInt32) (arr2 : Array UInt32) (h_precond : elementWiseDivision_precond arr1 arr2) : Array UInt32 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def elementWiseDivision_postcond (arr1 : Array UInt32) (arr2 : Array UInt32) (result : Array UInt32) (h_precond : elementWiseDivision_precond arr1 arr2) : Prop :=
  result.size = arr1.size ∧
  (∀ i, i < result.size → result[i]! = arr1[i]! / arr2[i]!)

theorem elementWiseDivision_spec_satisfied (arr1 : Array UInt32) (arr2 : Array UInt32) (h_precond : elementWiseDivision_precond arr1 arr2) :
    elementWiseDivision_postcond arr1 arr2 (elementWiseDivision arr1 arr2 h_precond) h_precond := by
  sorry
-- </vc-theorems>