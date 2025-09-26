import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) : Prop :=
  N > 0 ∧ a.size = Int.natAbs N ∧ b.size = Int.natAbs N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma array_get_singleton_zero_int (x : Int) : (#[x])[0]! = x := by
  simp

-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b sum N) : Array Int :=
  #[2 * N]
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (result : Array Int) (h_precond : myfun_precond a b sum N) : Prop :=
  result[0]! ≤ 2 * N

theorem myfun_spec_satisfied (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b sum N) :
    myfun_postcond a b sum N (myfun a b sum N h_precond) h_precond := by
  simpa [myfun, myfun_postcond] using (le_rfl : 2 * N ≤ 2 * N)
-- </vc-theorems>
