-- <vc-preamble>
@[reducible, simp]
def myfun4_precond (x : Array Nat) (y : Array Nat) : Prop :=
  y.size = 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()