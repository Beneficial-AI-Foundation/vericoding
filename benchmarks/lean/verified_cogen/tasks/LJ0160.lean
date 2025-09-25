-- <vc-preamble>
@[reducible, simp]
def reverse_precond (a : Array Int) : Prop := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse (a : Array Int) (h_precond : reverse_precond a) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def reverse_postcond (a : Array Int) (result: Array Int) (h_precond : reverse_precond a) : Prop :=
  result.size = a.size ∧ (∀ i, i < result.size → result[i]! = a[a.size - 1 - i]!)

theorem reverse_spec_satisfied (a: Array Int) (h_precond : reverse_precond a) :
    reverse_postcond a (reverse a h_precond) h_precond := by
  sorry
-- </vc-theorems>