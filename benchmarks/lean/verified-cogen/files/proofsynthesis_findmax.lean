-- <vc-preamble>
@[reducible, simp]
def findMax_precond (nums : Array Int) : Prop :=
  nums.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()