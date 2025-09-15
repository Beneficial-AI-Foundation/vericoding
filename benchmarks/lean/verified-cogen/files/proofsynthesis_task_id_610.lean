-- <vc-preamble>
@[reducible, simp]
def removeKthElement_precond (list : Array Int) (k : Nat) :=
  list.size > 0 ∧ 0 < k ∧ k < list.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()