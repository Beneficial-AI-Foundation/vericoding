-- <vc-preamble>
@[reducible, simp]
def linearSearch_precond (nums : Array Int) (target : Int) : Prop :=
  nums.size < 0x80000000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()