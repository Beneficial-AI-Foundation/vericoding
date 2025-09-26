-- <vc-preamble>
@[reducible, simp]
def maxDafnyLsp_precond (a : Array Int) := a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxDafnyLsp (a : Array Int) (h_precond : maxDafnyLsp_precond (a)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def maxDafnyLsp_postcond (a : Array Int) (x: Nat) (h_precond : maxDafnyLsp_precond (a)) :=
  0 ≤ x ∧ x < a.size ∧ (∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≤ a[x]!)

theorem maxDafnyLsp_spec_satisfied (a: Array Int) (h_precond : maxDafnyLsp_precond (a)) :
    maxDafnyLsp_postcond (a) (maxDafnyLsp (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>