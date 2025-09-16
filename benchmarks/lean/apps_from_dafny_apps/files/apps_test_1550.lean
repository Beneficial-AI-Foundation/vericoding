-- <vc-preamble>
def ValidInput (n : Int) (digits : String) : Prop :=
  n > 0 ∧ digits.length = n.natAbs ∧ ∀ i, 0 ≤ i ∧ i < digits.length → '0' ≤ digits.data[i]! ∧ digits.data[i]! ≤ '9'

def modifyString (s : String) (index : Int) : String :=
  sorry

def transformDigits (s : String) (key : Int) : String :=
  sorry

def rotateString (s : String) (index : Int) : String :=
  sorry

def isAllDigits (s : String) : Prop :=
  ∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.data[i]! ∧ s.data[i]! ≤ '9'

def parseInput (input : String) : List String :=
  sorry

def parseInputHelper (input : String) (i : Int) (currentLine : String) (lines : List String) : List String :=
  sorry

def parseInt (s : String) : Int :=
  sorry

instance validInputDecidable (n : Int) (digits : String) : Decidable (ValidInput n digits) := by
  sorry

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧ ∃ i, 0 ≤ i ∧ i < stdin_input.length ∧ stdin_input.data[i]! = '\n'
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
  result.length > 0 ∧ 
  result.data[result.length - 1]! = '\n' ∧
  (let lines := parseInput stdin_input
   if lines.length ≥ 2 then
     let n := parseInt (lines[0]!)
     let digits := lines[1]!
     if ValidInput n digits then
       let minResult := result.dropRight 1
       minResult.length = n.natAbs ∧
       (∀ i, 0 ≤ i ∧ i < minResult.length → '0' ≤ minResult.data[i]! ∧ minResult.data[i]! ≤ '9') ∧
       (∃ index, 0 ≤ index ∧ index < n ∧ minResult = modifyString digits index) ∧
       (∀ index, 0 ≤ index ∧ index < n → minResult ≤ modifyString digits index)
     else
       result = "\n"
   else
     result = "\n")

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>
