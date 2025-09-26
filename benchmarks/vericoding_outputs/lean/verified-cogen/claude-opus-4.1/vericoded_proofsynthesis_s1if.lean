import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = N ∧ sum.size = 1
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond (a) (sum) (N)) : Array Int :=
  let result := #[N]
  result
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Int) (result: Array Int) (h_precond : myfun_precond (a) (sum) (N)) :=
  result[0]! = N

theorem myfun_spec_satisfied (a: Array Int) (sum: Array Int) (N: Int) (h_precond : myfun_precond (a) (sum) (N)) :
    myfun_postcond (a) (sum) (N) (myfun (a) (sum) (N) h_precond) h_precond := by
  simp [myfun, myfun_postcond]
-- </vc-theorems>

#check myfun