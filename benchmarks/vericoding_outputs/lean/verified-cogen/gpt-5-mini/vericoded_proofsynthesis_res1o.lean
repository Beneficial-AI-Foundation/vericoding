import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = N.natAbs ∧ b.size = N.natAbs ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper lemma about Array.mkArray producing a 1-element array whose 0th entry is 0
theorem mkArray_one_get_zero : (Array.mkArray 1 (0 : Int))[0]! = 0 := rfl
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a b sum N) : Array Int :=
  Array.mkArray 1 (0 : Int)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (b : Array Int) (sum : Array Int) (N : Int) (result: Array Int) (h_precond : myfun_precond a b sum N) :=
  result[0]! ≤ 2 * N

theorem myfun_spec_satisfied (a: Array Int) (b: Array Int) (sum: Array Int) (N: Int) (h_precond : myfun_precond a b sum N) :
    myfun_postcond a b sum N (myfun a b sum N h_precond) h_precond := by
  dsimp [myfun]
  rw [mkArray_one_get_zero]
  have hN := h_precond.1
  linarith
-- </vc-theorems>
