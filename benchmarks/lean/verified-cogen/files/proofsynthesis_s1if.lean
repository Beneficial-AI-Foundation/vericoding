-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = N ∧ sum.size = 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

#check myfun