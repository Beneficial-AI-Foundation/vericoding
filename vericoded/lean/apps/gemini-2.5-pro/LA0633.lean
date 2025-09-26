import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length ≥ 3 ∧
  input.data[1]! = ' ' ∧
  (input.data[0]! = 'H' ∨ input.data[0]! = 'D') ∧
  (input.data[2]! = 'H' ∨ input.data[2]! = 'D') ∧
  (input.length = 3 ∨ (input.length > 3 ∧ input.data[3]! = '\n'))

def CorrectOutput (input : String) (h : ValidInput input) : String :=
  if (input.data[0]! = 'H' ∧ input.data[2]! = 'H') ∨ (input.data[0]! = 'D' ∧ input.data[2]! = 'D')
  then "H\n"
  else "D\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  CorrectOutput input h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = CorrectOutput input h_precond ∧ (result = "H\n" ∨ result = "D\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond solve
  apply And.intro
  · rfl
  · unfold CorrectOutput
    split_ifs <;> simp
-- </vc-theorems>
