-- <vc-preamble>
@[reducible, simp]
def abs_precond (x : Int) : Prop :=
  x ≠ Int.negSucc 2147483647
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

#check abs
#check abs_spec_satisfied