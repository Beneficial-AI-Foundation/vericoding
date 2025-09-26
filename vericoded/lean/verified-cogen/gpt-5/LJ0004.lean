import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) :=
  a.size = N.natAbs ∧ sum.size = 1 ∧ N > 0 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma getBang_singleton {α} [Inhabited α] (x : α) : (#[x] : Array α)[0]! = x := by
  simp

-- LLM HELPER
lemma zero_le_three_mul_of_pos {N : Int} (h : 0 < N) : 0 ≤ 3 * N := by
  have hN0 : 0 ≤ N := le_of_lt h
  have h3 : 0 ≤ (3 : Int) := by decide
  exact mul_nonneg h3 hN0
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) : Array Int × Array Int :=
  (a, #[0])
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Int) (result: Array Int × Array Int) (h_precond : myfun_precond a sum N) :=
  result.2[0]! ≤ 3 * N

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  rcases h_precond with ⟨_, _, h_pos, _⟩
  simpa [myfun_postcond, myfun] using zero_le_three_mul_of_pos (N := N) h_pos
-- </vc-theorems>
