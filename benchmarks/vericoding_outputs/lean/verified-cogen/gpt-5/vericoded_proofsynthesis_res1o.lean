import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = N.natAbs ∧ b.size = N.natAbs ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed for this file
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b sum N) : Array Int :=
  #[2 * N]
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (result: Array Int) (h_precond : myfun_precond a b sum N) :=
  result[0]! ≤ 2 * N

theorem myfun_spec_satisfied (a: Array Int) (b: Array Int) (sum: Array Int) (N: Int) (h_precond : myfun_precond a b sum N) :
    myfun_postcond a b sum N (myfun a b sum N h_precond) h_precond := by
  simpa [myfun_postcond, myfun]
-- </vc-theorems>
