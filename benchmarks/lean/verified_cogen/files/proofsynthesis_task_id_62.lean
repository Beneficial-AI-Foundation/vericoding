-- <vc-preamble>
@[reducible, simp]
def smallestNum_precond (nums : Array Int) :=
  nums.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

#check smallestNum_spec_satisfied