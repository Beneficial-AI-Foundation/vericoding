-- <vc-preamble>
@[reducible, simp]
def reverseToK_precond (list : Array Int) (n : Nat) : Prop :=
  list.size > 0 ∧ 0 < n ∧ n < list.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := 
  return ()