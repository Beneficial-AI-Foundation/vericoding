import Mathlib
-- <vc-preamble>
/- Function precondition -/
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) : Prop :=
  N > 0 ∧ a.size = N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemmas for array operations
lemma array_get_of_singleton (x : Int) : (#[x] : Array Int)[0]! = x := by simp

lemma array_size_singleton (x : Int) : (#[x] : Array Int).size = 1 := by simp
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) : Array Int × Array Int :=
  let result_sum := #[3 * N]
  (a, result_sum)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Int) (result : Array Int × Array Int) (h_precond : myfun_precond a sum N) : Prop :=
  result.2[0]! = 3 * N

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  unfold myfun_postcond myfun
  simp
-- </vc-theorems>

def main : IO Unit := return ()