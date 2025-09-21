-- <vc-preamble>
import Mathlib

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)

theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  sorry
-- </vc-theorems>