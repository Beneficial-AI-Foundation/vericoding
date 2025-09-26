import Mathlib
-- <vc-preamble>
@[reducible, simp]
def chooseOdd_precond : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- No helpers are needed for this simple proof.
-- </vc-helpers>

-- <vc-definitions>
def chooseOdd (h_precond : chooseOdd_precond) : Int :=
  3
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def chooseOdd_postcond (result: Int) (h_precond : chooseOdd_precond) : Prop :=
  result % 2 = 1

theorem chooseOdd_spec_satisfied (h_precond : chooseOdd_precond) :
    chooseOdd_postcond (chooseOdd h_precond) h_precond := by
   simp [chooseOdd]
-- </vc-theorems>
