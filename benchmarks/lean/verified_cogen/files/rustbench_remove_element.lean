-- <vc-preamble>
/- Precondition definition for removeElement -/
@[reducible, simp]
def removeElement_precond (a : Array Int) (pos : Nat) :=
  0 ≤ pos ∧ pos < a.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeElement (a : Array Int) (pos : Nat) (h_precond : removeElement_precond a pos) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeElement_postcond (a : Array Int) (pos : Nat) (result : Array Int) (h_precond : removeElement_precond a pos) :=
  result.size = a.size - 1 ∧ 
  (∀ i, i < pos → result[i]! = a[i]!) ∧ 
  (∀ i, pos ≤ i ∧ i < result.size → result[i]! = a[i + 1]!)

theorem removeElement_spec_satisfied (a : Array Int) (pos : Nat) (h_precond : removeElement_precond a pos) :
    removeElement_postcond a pos (removeElement a pos h_precond) h_precond := by
  sorry
-- </vc-theorems>