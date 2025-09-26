import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ 
  (input.data[0]! = '0' ∨ input.data[0]! = '1') ∧ 
  (input.length = 1 ∨ (input.length > 1 ∧ input.data[1]! = '\n'))

def LogicalNot (digit : Char) : String :=
  if digit = '0' then "1\n" else "0\n"

def CorrectOutput (input : String) (output : String) : Prop :=
  output = LogicalNot (input.data[0]!)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for the solve function
-- LLM HELPER
lemma valid_input_first_char (input : String) (h : ValidInput input) : 
  input.data[0]! = '0' ∨ input.data[0]! = '1' := h.2.1
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  LogicalNot (input.data[0]!)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  CorrectOutput input output

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  unfold solve_postcond CorrectOutput
  simp [solve]
-- </vc-theorems>
