import Mathlib
-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧ 
  (let s := if input.length > 0 ∧ input.back = '\n' 
            then input.dropRight 1
            else input;
   s = "ABC" ∨ s = "ARC")

def NormalizeInput (input : String) : String :=
  if input.length > 0 ∧ input.back = '\n' 
  then input.dropRight 1
  else input

def ExpectedOutput (input : String) : String :=
  let s := NormalizeInput input;
  if s = "ABC" then "ARC\n" else "ABC\n"

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem solve_precond_iff (input : String) : solve_precond input ↔ ValidInput input := Iff.rfl
-- LLM HELPER
@[simp] theorem ExpectedOutput_eq (input : String) :
  ExpectedOutput input =
    (let s := NormalizeInput input; if s = "ABC" then "ARC\n" else "ABC\n") := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  ExpectedOutput input
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result = ExpectedOutput input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
