-- <vc-preamble>
@[reducible, simp]
def chooseOdd_precond : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chooseOdd (h_precond : chooseOdd_precond) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def chooseOdd_postcond (result: Int) (h_precond : chooseOdd_precond) : Prop :=
  result % 2 = 1

theorem chooseOdd_spec_satisfied (h_precond : chooseOdd_precond) :
    chooseOdd_postcond (chooseOdd h_precond) h_precond := by
  sorry
-- </vc-theorems>