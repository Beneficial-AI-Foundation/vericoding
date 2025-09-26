import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) : Prop :=
  a.size = N.natAbs ∧ sum.size = 1 ∧ N > 0 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) : Array Int × Array Int :=
  (a, #[2 * N])
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Int) (result : Array Int × Array Int) (h_precond : myfun_precond a sum N) : Prop :=
  result.2[0]! ≤ 2 * N

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  exact le_of_eq (by simp [myfun])
-- </vc-theorems>
