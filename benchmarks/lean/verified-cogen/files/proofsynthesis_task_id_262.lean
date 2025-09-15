-- <vc-preamble>
@[reducible, simp]
def splitArray_precond (list : Array Int) (l : Nat) : Prop :=
  list.size > 0 ∧ 0 < l ∧ l < list.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()