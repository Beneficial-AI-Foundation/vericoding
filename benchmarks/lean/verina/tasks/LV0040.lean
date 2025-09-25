-- <vc-preamble>
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)

theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  sorry
-- </vc-theorems>