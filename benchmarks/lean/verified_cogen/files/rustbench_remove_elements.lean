-- <vc-preamble>
/- Helper function to check if an element exists in an array -/
@[reducible, simp]
def inArray (a : Array Int) (x : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = x

@[reducible, simp]  
def removeElements_precond (a : Array Int) (b : Array Int) : Prop := 
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()