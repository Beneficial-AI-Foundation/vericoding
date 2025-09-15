-- <vc-preamble>
@[reducible, simp]
def maxArray_precond (nums : Array Int) := 
  nums.size ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()