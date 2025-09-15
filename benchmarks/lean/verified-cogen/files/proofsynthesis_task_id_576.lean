-- <vc-preamble>
@[reducible, simp]
def isSubArray_precond (main : Array Int) (sub : Array Int) : Prop :=
  sub.size ≤ main.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()