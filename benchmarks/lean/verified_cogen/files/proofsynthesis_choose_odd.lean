-- <vc-preamble>
@[reducible, simp]
def chooseOdd_precond (v : Array Nat) : Prop :=
  ∃ q : Nat, q < v.size ∧ v[q]! % 2 = 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()