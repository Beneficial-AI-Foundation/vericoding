-- <vc-preamble>
@[reducible, simp]
def minSecondValueFirst_precond (arr : Array (Array Int)) :=
  arr.size > 0 ∧ (∀ i, i < arr.size → arr[i]!.size ≥ 2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()