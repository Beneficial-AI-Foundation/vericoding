-- <vc-preamble>
@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayProduct_precond (a) (b)) :=
  result.size = a.size ∧ (∀ i, i < a.size → result[i]! = (a[i]! * b[i]!))

theorem arrayProduct_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    arrayProduct_postcond (a) (b) (arrayProduct (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>