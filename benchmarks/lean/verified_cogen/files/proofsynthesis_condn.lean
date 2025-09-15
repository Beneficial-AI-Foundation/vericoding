-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (N : Int) (m : Int) :=
  N > 0 ∧ a.size = N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Example usage:
def main : IO Unit := do
  pure ()
-/