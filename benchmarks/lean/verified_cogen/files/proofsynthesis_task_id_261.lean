-- <vc-preamble>
@[reducible, simp]
def elementWiseDivision_precond (arr1 : Array UInt32) (arr2 : Array UInt32) : Prop :=
  arr1.size = arr2.size ∧ 
  (∀ i, i < arr2.size → arr2[i]! ≠ 0) ∧
  (∀ m, m < arr1.size → True)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()