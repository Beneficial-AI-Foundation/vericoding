-- <vc-preamble>
@[reducible, simp]
def myMin_precond (a : Int) (b : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myMin_postcond (a : Int) (b : Int) (result: Int) (h_precond : myMin_precond (a) (b)) :=
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)

theorem myMin_spec_satisfied (a: Int) (b: Int) (h_precond : myMin_precond (a) (b)) :
    myMin_postcond (a) (b) (myMin (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>