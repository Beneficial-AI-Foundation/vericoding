import Mathlib
-- <vc-preamble>
def parseInput (_ : String) : List Int :=
  [10, 1, 5, 3, 7]

def validInput (input : String) : Prop :=
  input.length > 0 ∧ 
  (∃ i, 0 ≤ i ∧ i < input.length ∧ input.data[i]! = '\n') ∧
  let parts := parseInput input
  parts.length = 5 ∧
  parts[0]! ≥ 4 ∧ parts[0]! ≤ 100 ∧
  parts[1]! ≥ 1 ∧ parts[1]! ≤ parts[0]! ∧
  parts[2]! ≥ 1 ∧ parts[2]! ≤ parts[0]! ∧
  parts[3]! ≥ 1 ∧ parts[3]! ≤ parts[0]! ∧
  parts[4]! ≥ 1 ∧ parts[4]! ≤ parts[0]! ∧
  parts[1]! ≠ parts[2]! ∧ parts[1]! ≠ parts[3]! ∧ parts[1]! ≠ parts[4]! ∧
  parts[2]! ≠ parts[3]! ∧ parts[2]! ≠ parts[4]! ∧
  parts[3]! ≠ parts[4]!

def simulateTrainsHelper (_ _ _ _ _ _ : Int) : Bool :=
  true

def simulateTrains (n a x b y : Int) : Bool :=
  simulateTrainsHelper n a x b y (2 * n)

def trainsWillMeet (input : String) : Bool :=
  let parts := parseInput input
  let n := parts[0]!
  let a := parts[1]!
  let x := parts[2]!
  let b := parts[3]!
  let y := parts[4]!
  if a = b then true
  else simulateTrains n a x b y

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  (∃ i, 0 ≤ i ∧ i < stdin_input.length ∧ stdin_input.data[i]! = '\n') ∧
  validInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  if trainsWillMeet stdin_input then "YES\n" else "NO\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  (result = "YES\n" ∨ result = "NO\n") ∧
  (result = "YES\n" ↔ trainsWillMeet stdin_input) ∧
  (result = "NO\n" ↔ ¬trainsWillMeet stdin_input)

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  unfold solve_postcond
  cases h : trainsWillMeet stdin_input <;> simp [solve, h]
-- </vc-theorems>
