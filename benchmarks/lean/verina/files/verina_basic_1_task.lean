-- <vc-preamble>
import Mathlib

@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)

theorem hasOppositeSign_spec_satisfied (a: Int) (b: Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>