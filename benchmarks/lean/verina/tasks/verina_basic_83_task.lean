-- <vc-preamble>
@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : concat_precond (a) (b)) :=
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)

theorem concat_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : concat_precond (a) (b)) :
    concat_postcond (a) (b) (concat (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>