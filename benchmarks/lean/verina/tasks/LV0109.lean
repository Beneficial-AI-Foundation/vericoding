-- <vc-preamble>
@[reducible, simp]
def removeElement_precond (s : Array Int) (k : Nat) : Prop :=
  k < s.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeElement (s : Array Int) (k : Nat) (h_precond : removeElement_precond (s) (k)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeElement_postcond (s : Array Int) (k : Nat) (result: Array Int) (h_precond : removeElement_precond (s) (k)) :=
  result.size = s.size - 1 ∧
  (∀ i, i < k → result[i]! = s[i]!) ∧
  (∀ i, i < result.size → i ≥ k → result[i]! = s[i + 1]!)

theorem removeElement_spec_satisfied (s: Array Int) (k: Nat) (h_precond : removeElement_precond (s) (k)) :
    removeElement_postcond (s) (k) (removeElement (s) (k) h_precond) h_precond := by
  sorry
-- </vc-theorems>