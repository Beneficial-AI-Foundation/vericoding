import Mathlib
-- <vc-preamble>
/- Precondition definitions -/
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) : Prop :=
  N > 0 ∧ a.size = N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma array_getBang_singleton_int (x : Int) : (#[x] : Array Int)[0]! = x := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) : Array Int × Array Int :=
  (a, #[6 * N])
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Int) (result : Array Int × Array Int) (h_precond : myfun_precond a sum N) : Prop :=
  result.2[0]! = 6 * N

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  simp [myfun, myfun_postcond]
-- </vc-theorems>
