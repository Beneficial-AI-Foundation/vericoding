-- <vc-preamble>
@[reducible, simp]
def bitWiseXor_precond (arr1 : Array UInt32) (arr2 : Array UInt32) :=
  arr1.size = arr2.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bitWiseXor (arr1 : Array UInt32) (arr2 : Array UInt32) (h_precond : bitWiseXor_precond (arr1) (arr2)) : Array UInt32 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def bitWiseXor_postcond (arr1 : Array UInt32) (arr2 : Array UInt32) (result: Array UInt32) (h_precond : bitWiseXor_precond (arr1) (arr2)) :=
  result.size = arr1.size ∧ 
  (∀ i, i < result.size → result[i]! = arr1[i]! ^^^ arr2[i]!)

theorem bitWiseXor_spec_satisfied (arr1: Array UInt32) (arr2: Array UInt32) (h_precond : bitWiseXor_precond (arr1) (arr2)) :
    bitWiseXor_postcond (arr1) (arr2) (bitWiseXor (arr1) (arr2) h_precond) h_precond := by
  sorry
-- </vc-theorems>