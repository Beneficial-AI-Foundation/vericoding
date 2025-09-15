-- <vc-preamble>
@[reducible, simp]
def elementWiseModule_precond (arr1 : Array Int) (arr2 : Array Int) :=
  arr1.size = arr2.size ∧ (∀ i, i < arr2.size → arr2[i]! ≠ 0) ∧ (∀ i, i < arr1.size → Int.emod arr1[i]! arr2[i]! ≥ Int.negSucc 2147483647 ∧ Int.emod arr1[i]! arr2[i]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()