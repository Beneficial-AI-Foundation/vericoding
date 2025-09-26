import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Nat) :=
  N > 0 ∧ a.size = N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma array_get_singleton_zero {α} [Inhabited α] (x : α) :
    (#[x] : Array α)[0]! = x := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Nat) (h_precond : myfun_precond a sum N) : Array Int × Array Int :=
  (a, #[(4 : Int) * (N : Int)])
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Nat) (result_a : Array Int) (result_sum : Array Int) (h_precond : myfun_precond a sum N) :=
  result_sum[0]! = 4 * N

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Nat) (h_precond : myfun_precond a sum N) :
    let result := myfun a sum N h_precond
    myfun_postcond a sum N result.1 result.2 h_precond := by
  have h :
      myfun_postcond a sum N (myfun a sum N h_precond).1 (myfun a sum N h_precond).2 h_precond := by
    simp [myfun_postcond, myfun]
  simpa using h
-- </vc-theorems>
