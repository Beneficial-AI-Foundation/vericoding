import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Nat) :=
  N > 0 ∧ a.size = N ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
universe u
@[simp] lemma array_get_zero_singleton {α : Type u} [Inhabited α] (x : α) : (#[x][0]!) = x := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Nat) (h_precond : myfun_precond a sum N) : Array Int :=
  #[(3 : Int) * (N : Int)]
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Nat) (result: Array Int) (h_precond : myfun_precond a sum N) :=
  result[0]! = 3 * N

theorem myfun_spec_satisfied (a: Array Int) (sum: Array Int) (N: Nat) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  simp [myfun, myfun_postcond]
-- </vc-theorems>
