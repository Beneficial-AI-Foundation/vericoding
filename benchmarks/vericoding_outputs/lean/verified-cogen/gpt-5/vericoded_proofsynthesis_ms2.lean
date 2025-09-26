import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Nat) (sum : Array Nat) (N : Nat) :=
  a.size = N ∧ sum.size = 1 ∧ N > 0
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma array_singleton_get! {α} [Inhabited α] (x : α) : (#[x] : Array α)[0]! = x := by
  simp

@[simp] lemma array_singleton_get_zero_nat : (#[0] : Array Nat)[0]! = 0 := by
  simp
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Nat) (sum : Array Nat) (N : Nat) (h_precond : myfun_precond a sum N) : Array Nat × Array Nat :=
  (a, #[0])
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Nat) (sum : Array Nat) (N : Nat) (result_a : Array Nat) (result_sum : Array Nat) (h_precond : myfun_precond a sum N) :=
  result_sum[0]! ≤ N

theorem myfun_spec_satisfied (a : Array Nat) (sum : Array Nat) (N : Nat) (h_precond : myfun_precond a sum N) :
    let (result_a, result_sum) := myfun a sum N h_precond
    myfun_postcond a sum N result_a result_sum h_precond := by
  simpa [myfun, myfun_postcond] using (Nat.zero_le N)
-- </vc-theorems>
