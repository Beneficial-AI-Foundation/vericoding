-- <vc-preamble>
@[reducible, simp]
def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  ∀ i j, i < j → j < arr.size → arr[i]! ≤ arr[j]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()