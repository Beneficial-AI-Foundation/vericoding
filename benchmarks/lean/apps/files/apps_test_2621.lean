-- <vc-preamble>
@[reducible, simp]
def validInput (n m k : Int) (H : List Int) : Prop :=
  n ≥ 1 ∧ n = H.length ∧ m ≥ 0 ∧ k ≥ 0 ∧ 
  (∀ i, 0 ≤ i ∧ i < H.length → H[i]! ≥ 0)

partial def simulateGame (pos blocks n k : Int) (H : List Int) : Bool :=
  if pos = n - 1 then
    true
  else
    let h1 := H[Int.natAbs pos]!
    let h2 := H[Int.natAbs (pos + 1)]!
    if h1 ≥ h2 then
      let newBlocks := if h2 ≥ k then blocks + (h1 - h2) + k else blocks + h1
      simulateGame (pos + 1) newBlocks n k H
    else
      if h2 > h1 + blocks + k then
        false
      else
        let newBlocks := 
          if h2 ≤ k then blocks + h1
          else if (h2 - h1) ≤ k then blocks + k - (h2 - h1)
          else blocks - (h2 - h1 - k)
        newBlocks ≥ 0 ∧ simulateGame (pos + 1) newBlocks n k H

def canReachEnd (n m k : Int) (H : List Int) : Bool :=
  simulateGame 0 m n k H

@[reducible, simp]
def validCompleteInputFormat (input : String) : Prop :=
  input.length > 0 ∧ input.data[input.length - 1]! = '\n'

@[reducible, simp]
def validOutputFormat (output : String) (_ : String) : Prop :=
  output.length ≥ 0 ∧ 
  (output = "" ∨ output.data[output.length - 1]! = '\n') ∧
  (∀ i, 0 ≤ i ∧ i < output.length → 
    let c := output.data[i]!
    c = 'Y' ∨ c = 'E' ∨ c = 'S' ∨ c = 'N' ∨ c = 'O' ∨ c = '\n')

@[reducible, simp]
def correctGameResults (_ : String) (_ : String) : Prop := True

@[reducible, simp]
def outputMatchesTestCaseCount (_ : String) (_ : String) : Prop := True

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  stdin_input.data[stdin_input.length - 1]! = '\n' ∧
  validCompleteInputFormat stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (_ : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (_ : solve_precond stdin_input) : Prop :=
  result.length ≥ 0 ∧
  (∀ i, 0 ≤ i ∧ i < result.length → 
    let c := result.data[i]!
    c = 'Y' ∨ c = 'E' ∨ c = 'S' ∨ c = 'N' ∨ c = 'O' ∨ c = '\n') ∧
  (result = "" ∨ result.data[result.length - 1]! = '\n') ∧
  validOutputFormat result stdin_input ∧
  correctGameResults result stdin_input ∧
  outputMatchesTestCaseCount result stdin_input

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>