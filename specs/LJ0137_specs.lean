-- <vc-preamble>
@[reducible, simp]
def arrayConcat_precond (a : Array Int) (b : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrayConcat (a : Array Int) (b : Array Int) (h_precond : arrayConcat_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arrayConcat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayConcat_precond (a) (b)) :=
  result.size = a.size + b.size ∧
  (∀ i, 0 ≤ i ∧ i < a.size → result[i]! = a[i]!) ∧
  (∀ i, 0 ≤ i ∧ i < b.size → result[i + a.size]! = b[i]!)

theorem arrayConcat_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arrayConcat_precond (a) (b)) :
    arrayConcat_postcond (a) (b) (arrayConcat (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>