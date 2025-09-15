-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = Int.natAbs N ∧ sum.size = 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()