-- <vc-preamble>
@[reducible, simp]
def removeDuplicates_precond (a : Array Int) := a.size ≥ 1

def inArray (a : Array Int) (x : Int) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Test cases can be added here -/