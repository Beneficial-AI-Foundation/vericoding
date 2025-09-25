-- <vc-preamble>
import Mathlib

@[reducible, simp]
def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) (h_precond : containsConsecutiveNumbers_precond (a)) :=
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result

theorem containsConsecutiveNumbers_spec_satisfied (a: Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    containsConsecutiveNumbers_postcond (a) (containsConsecutiveNumbers (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>