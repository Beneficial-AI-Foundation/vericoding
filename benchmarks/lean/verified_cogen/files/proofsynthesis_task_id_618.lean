-- <vc-preamble>
@[reducible, simp]
def elementWiseDivide_precond (arr1 : Array Nat) (arr2 : Array Nat) :=
  arr1.size = arr2.size ∧ 
  (∀ i, i < arr2.size → arr2[i]! ≠ 0) ∧
  (∀ i, i < arr1.size → (arr1[i]! / arr2[i]! : Int) ≥ Int.negSucc 2147483647 ∧ (arr1[i]! / arr2[i]! : Int) ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()