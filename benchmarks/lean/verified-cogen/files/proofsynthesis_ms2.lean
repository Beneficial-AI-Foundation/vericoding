-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Nat) (sum : Array Nat) (N : Nat) :=
  a.size = N ∧ sum.size = 1 ∧ N > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()