-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length = 5 ∧ (input.take 4).length = 4 ∧
  (∀ i, 0 ≤ i ∧ i < 4 → '0' ≤ input.data[i]! ∧ input.data[i]! ≤ '9') ∧
  input.data[4]! = '\n'

def CharToDigit (c : Char) : Int :=
  c.toNat - '0'.toNat

def EvaluateExpression (a b c d : Int) (op1 op2 op3 : Char) : Int :=
  let b_val := if op1 = '+' then b else -b
  let c_val := if op2 = '+' then c else -c  
  let d_val := if op3 = '+' then d else -d
  a + b_val + c_val + d_val

def SolutionExists (input : String) : Prop :=
  ValidInput input ∧
  let a := CharToDigit (input.data[0]!)
  let b := CharToDigit (input.data[1]!)
  let c := CharToDigit (input.data[2]!)
  let d := CharToDigit (input.data[3]!)
  ∃ op1 op2 op3, (op1 = '+' ∨ op1 = '-') ∧ (op2 = '+' ∨ op2 = '-') ∧ (op3 = '+' ∨ op3 = '-') ∧
      EvaluateExpression a b c d op1 op2 op3 = 7

def ValidOutput (result input : String) : Prop :=
  ValidInput input ∧
  result.length = 10 ∧ (result.drop 7).take 2 = "=7" ∧ result.data[9]! = '\n' ∧
  result.data[0]! = input.data[0]! ∧ result.data[2]! = input.data[1]! ∧
  result.data[4]! = input.data[2]! ∧ result.data[6]! = input.data[3]! ∧
  (result.data[1]! = '+' ∨ result.data[1]! = '-') ∧ (result.data[3]! = '+' ∨ result.data[3]! = '-') ∧ (result.data[5]! = '+' ∨ result.data[5]! = '-') ∧
  let a := CharToDigit (input.data[0]!)
  let b := CharToDigit (input.data[1]!)
  let c := CharToDigit (input.data[2]!)
  let d := CharToDigit (input.data[3]!)
  EvaluateExpression a b c d (result.data[1]!) (result.data[3]!) (result.data[5]!) = 7

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input ∧ SolutionExists input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput result input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>