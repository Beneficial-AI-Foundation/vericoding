-- <vc-preamble>
@[reducible, simp]
def arraySum_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size = b.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arraySum (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def arraySum_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arraySum_precond (a) (b)) :=
  (result.size = a.size) ∧ (∀ i : Nat, i < a.size → a[i]! + b[i]! = result[i]!)

theorem arraySum_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arraySum_precond (a) (b)) :
    arraySum_postcond (a) (b) (arraySum (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>