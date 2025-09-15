-- <vc-preamble>
-- Precondition for smallest_list_length
@[reducible, simp]
def smallestListLength_precond (list : Array (Array Int)) : Prop :=
  list.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := 
  pure ()