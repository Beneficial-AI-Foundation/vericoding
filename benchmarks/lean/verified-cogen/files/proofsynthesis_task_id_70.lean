-- <vc-preamble>
@[reducible, simp]
def allSequenceEqualLength_precond (seq : Array (Array Int)) :=
  seq.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()