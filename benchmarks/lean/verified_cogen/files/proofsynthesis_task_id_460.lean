-- <vc-preamble>
/- Precondition: All sub-arrays must be non-empty -/
@[reducible, simp]
def getFirstElements_precond (arr : Array (Array Int)) :=
  ∀ i, i < arr.size → arr[i]!.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()