-- <vc-preamble>
/- Precondition definition for removeElement -/
@[reducible, simp]
def removeElement_precond (a : Array Int) (pos : Nat) :=
  0 ≤ pos ∧ pos < a.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := do
  return ()