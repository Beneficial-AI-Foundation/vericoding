-- <vc-preamble>
import Mathlib

@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)

theorem Abs_spec_satisfied (x: Int) (h_precond : Abs_precond (x)) :
    Abs_postcond (x) (Abs (x) h_precond) h_precond := by
  sorry
-- </vc-theorems>