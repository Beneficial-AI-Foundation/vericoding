-- <vc-preamble>
-- Precondition function for myfun2
@[reducible, simp]
def myfun2_precond (x : Array Int) : Prop :=
  ∀ k, 0 ≤ k ∧ k < x.size → x[k]! ≤ 0x7FFFBFFB
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()