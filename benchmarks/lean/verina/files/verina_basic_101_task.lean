-- <vc-preamble>
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  result / 3 = x ∧ result / 3 * 3 = result

theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  sorry
-- </vc-theorems>