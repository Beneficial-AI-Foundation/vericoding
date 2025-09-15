-- <vc-preamble>
@[reducible, simp]
def barrier_precond (arr : Array Int) (p : Nat) :=
  arr.size > 0 ∧ p < arr.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()