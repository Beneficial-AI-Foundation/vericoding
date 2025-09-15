-- <vc-preamble>
@[reducible, simp]
def twoWaySort_precond (a : Array Bool) : Prop :=
  a.size ≤ 100000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()