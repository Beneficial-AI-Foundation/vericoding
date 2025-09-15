-- <vc-preamble>
@[reducible, simp]
def isSorted_precond (lst : Array Int) :=
  lst.size ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Test cases can be added here -/