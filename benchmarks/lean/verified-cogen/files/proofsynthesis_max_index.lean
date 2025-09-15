-- <vc-preamble>
@[reducible, simp]
def myfun1_precond (x : Array Int) : Prop :=
  x.size ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()