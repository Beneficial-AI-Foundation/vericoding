-- <vc-preamble>
@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  result - a * b = 0 ∧ a * b - result = 0

theorem multiply_spec_satisfied (a: Int) (b: Int) (h_precond : multiply_precond (a) (b)) :
    multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>