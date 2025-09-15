-- <vc-preamble>
@[reducible, simp]
def myfun4_precond (x : Array UInt64) (y : Array UInt64) : Prop :=
  y.size = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  pure ()