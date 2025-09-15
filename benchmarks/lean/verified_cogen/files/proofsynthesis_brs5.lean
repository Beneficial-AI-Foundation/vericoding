-- <vc-preamble>
-- Precondition definitions
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) : Prop :=
  a.size = N.natAbs ∧ sum.size = 1 ∧ N > 0 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()