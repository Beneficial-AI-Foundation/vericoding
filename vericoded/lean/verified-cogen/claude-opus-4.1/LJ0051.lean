import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (sum : Array Int) (N : Int) :=
  N > 0 ∧ a.size = N.natAbs ∧ sum.size = 1 ∧ N < 1000
-- </vc-preamble>

-- <vc-helpers>

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
  intro k ⟨hk_ge, hk_lt⟩
  simp only [Prod.fst]
  have h_N_pos : 0 < N := h_precond.1
  -- LLM HELPER
  have h_idx_valid : k < (Array.replicate N.natAbs (N + 1)).size := by
    simp [Array.size_replicate]
    exact hk_lt
  -- Show that accessing element k gives N + 1
  have h_getElem : (Array.replicate N.natAbs (N + 1))[k]? = some (N + 1) := by
    rw [Array.getElem?_eq_getElem h_idx_valid]
    simp [Array.getElem_replicate]
  exact h_getElem
-- </vc-theorems>

def main : IO Unit := return ()