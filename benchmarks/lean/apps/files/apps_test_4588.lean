-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  (input.length = 3 ∧ input.data[1]! = ' ') ∨ 
  (input.length = 4 ∧ input.data[1]! = ' ' ∧ input.data[3]! = '\n')

def ValidHexDigit (c : Char) : Prop :=
  c = 'A' ∨ c = 'B' ∨ c = 'C' ∨ c = 'D' ∨ c = 'E' ∨ c = 'F'

def ValidInputFormat (input : String) : Prop :=
  input.length ≥ 3 ∧
  ValidInput input ∧
  ValidHexDigit (input.data[0]!) ∧
  ValidHexDigit (input.data[2]!)

def CorrectComparison (x y : Char) (result : String) : Prop :=
  (result = "<\n" ∨ result = ">\n" ∨ result = "=\n") ∧
  ((x.toNat < y.toNat) ↔ (result = "<\n")) ∧
  ((x.toNat > y.toNat) ↔ (result = ">\n")) ∧
  ((x.toNat = y.toNat) ↔ (result = "=\n"))

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInputFormat stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  CorrectComparison (stdin_input.data[0]!) (stdin_input.data[2]!) result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>