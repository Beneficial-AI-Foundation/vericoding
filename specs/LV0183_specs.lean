-- <vc-preamble>
@[reducible, simp]
def UpdateElements_precond (a : Array Int) : Prop :=
  a.size ≥ 8
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def UpdateElements (a : Array Int) (h_precond : UpdateElements_precond (a)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def UpdateElements_postcond (a : Array Int) (result: Array Int) (h_precond : UpdateElements_precond (a)) :=
  result[4]! = (a[4]!) + 3 ∧
  result[7]! = 516 ∧
  (∀ i, i < a.size → i ≠ 4 → i ≠ 7 → result[i]! = a[i]!)

theorem UpdateElements_spec_satisfied (a: Array Int) (h_precond : UpdateElements_precond (a)) :
    UpdateElements_postcond (a) (UpdateElements (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>