import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = N.natAbs ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>
-- No helper needed since Array.getElem?_replicate already exists in Mathlib
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) : Array Int × Array Int :=
  let result_array := Array.replicate N.natAbs (N + 1)
  (result_array, sum)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (sum : Array Int) (N : Int) (result: Array Int × Array Int) (h_precond : myfun_precond a sum N) :=
  ∀ k : Nat, 0 ≤ k ∧ k < N.natAbs → result.1[k]? = some (N + 1)

theorem myfun_spec_satisfied (a : Array Int) (sum : Array Int) (N : Int) (h_precond : myfun_precond a sum N) :
    myfun_postcond a sum N (myfun a sum N h_precond) h_precond := by
  unfold myfun_postcond myfun
  intro k hk
  simp only []
  have h_size : N.natAbs > 0 := by
    have : N > 0 := h_precond.1
    exact Int.natAbs_pos.mpr (ne_of_gt this)
  rw [Array.getElem?_replicate]
  simp [hk.2]
-- </vc-theorems>

def main : IO Unit := return ()