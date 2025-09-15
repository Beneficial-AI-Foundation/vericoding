-- <vc-preamble>
/- Lean 4 version of last_position function for finding the last occurrence of an element in an array -/

@[reducible, simp]
def lastPosition_precond (a : Array Int) (elem : Int) :=
  0 < a.size ∧ a.size < 100000 ∧ (∃ i, i < a.size ∧ a[i]! = elem)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()