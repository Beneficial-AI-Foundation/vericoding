
-- <vc-dependencies>
import Mathlib

@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  True

@[reducible, simp]
def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  -- !benchmark @start postcond
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)

-- </vc-dependencies>

-- <vc-helpers>
-- </vc-helpers>


-- <vc-task>
def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  -- <vc-code>
  sorry
  -- </vc-code>
theorem hasOppositeSign_spec_satisfied (a: Int) (b: Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond :=
 -- <vc-proof>
  by sorry
  -- </vc-proof>

-- </vc-task>
