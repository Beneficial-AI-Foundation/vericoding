-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length ≥ 2 ∧ 
  '0' ≤ input.data[0]! ∧ input.data[0]! ≤ '9' ∧ 
  '0' ≤ input.data[1]! ∧ input.data[1]! ≤ '9' ∧
  (input.data[input.length - 1]! = '\n' ∨ (input.data[0]! ≠ '\n' ∧ input.data[1]! ≠ '\n'))

def GoodDigitCount (digit : Char) : Int :=
  if digit = '0' then 2
  else if digit = '1' then 7
  else if digit = '2' then 2
  else if digit = '3' then 3
  else if digit = '4' then 3
  else if digit = '5' then 4
  else if digit = '6' then 2
  else if digit = '7' then 5
  else if digit = '8' then 1
  else 2

def ComputeTotalGoodCount (input : String) : Int :=
  GoodDigitCount (input.data[0]!) * GoodDigitCount (input.data[1]!)

def ValidOutput (result : String) (expectedCount : Int) : Prop :=
  result.length ≥ 2 ∧ 
  result.data[result.length - 1]! = '\n' ∧
  (∀ c ∈ result.data, c = '\n' ∨ ('0' ≤ c ∧ c ≤ '9')) ∧
  expectedCount ≥ 1 ∧ expectedCount ≤ 49

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
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
  ValidOutput result (ComputeTotalGoodCount input) ∧
  result = toString (ComputeTotalGoodCount input) ++ "\n"

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>