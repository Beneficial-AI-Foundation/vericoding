-- <vc-preamble>
@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()