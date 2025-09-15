-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (N : Nat) : Prop :=
  N > 0 ∧ a.size = N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()