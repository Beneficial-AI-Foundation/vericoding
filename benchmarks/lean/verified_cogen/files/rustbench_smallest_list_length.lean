-- <vc-preamble>
@[reducible, simp]
def smallestListLength_precond (lists : Array (Array Int)) :=
  lists.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()