-- <vc-preamble>
@[reducible, simp]
def ToArray_precond (xs : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def ToArray_postcond (xs : List Int) (result: Array Int) (h_precond : ToArray_precond (xs)) :=
  result.size = xs.length ∧ ∀ (i : Nat), i < xs.length → result[i]! = xs[i]!

theorem ToArray_spec_satisfied (xs: List Int) (h_precond : ToArray_precond (xs)) :
    ToArray_postcond (xs) (ToArray (xs) h_precond) h_precond := by
  sorry
-- </vc-theorems>