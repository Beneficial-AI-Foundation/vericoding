-- <vc-preamble>
@[reducible, simp]
def elementWiseModulo_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def elementWiseModulo (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def elementWiseModulo_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :=
  result.size = a.size ∧
  (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)

theorem elementWiseModulo_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    elementWiseModulo_postcond (a) (b) (elementWiseModulo (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>