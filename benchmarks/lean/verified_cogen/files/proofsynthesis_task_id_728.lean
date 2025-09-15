-- <vc-preamble>
@[reducible, simp]
def addList_precond (arr1 : Array Int) (arr2 : Array Int) : Prop :=
  arr1.size = arr2.size ∧ (∀ i, i < arr1.size → -2147483648 ≤ arr1[i]! + arr2[i]! ∧ arr1[i]! + arr2[i]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()