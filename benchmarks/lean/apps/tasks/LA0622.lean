-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length ≥ 18 ∧
  input.length > 0 ∧ input.data.get! (input.length - 1) = '\n' ∧
  input.take 7 = "AtCoder" ∧
  input.length > 7 ∧ input.data.get! 7 = ' ' ∧
  (∃ spacePos, 8 ≤ spacePos ∧ spacePos < input.length - 8 ∧ 
   spacePos < input.length ∧ input.data.get! spacePos = ' ' ∧
   (input.drop (spacePos + 1)).take 7 = "Contest" ∧
   spacePos + 8 = input.length - 1) ∧
  (∃ spacePos, 8 ≤ spacePos ∧ spacePos < input.length - 8 ∧ 
   spacePos < input.length ∧ input.data.get! spacePos = ' ' ∧
   spacePos > 8 ∧
   input.length > 8 ∧ 
   'A' ≤ input.data.get! 8 ∧ input.data.get! 8 ≤ 'Z' ∧
   (∀ k, 9 ≤ k ∧ k < spacePos → k < input.length ∧ 'a' ≤ input.data.get! k ∧ input.data.get! k ≤ 'z'))

def ValidOutput (input result : String) : Prop :=
  result.length = 4 ∧
  result.length > 0 ∧ result.data.get! 0 = 'A' ∧
  result.length > 2 ∧ result.data.get! 2 = 'C' ∧
  result.length > 3 ∧ result.data.get! 3 = '\n' ∧
  (∃ spacePos, 8 ≤ spacePos ∧ spacePos < input.length - 8 ∧ 
   spacePos < input.length ∧ input.data.get! spacePos = ' ' ∧
   result.length > 1 ∧ input.length > 8 ∧ result.data.get! 1 = input.data.get! 8)

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
  ValidOutput input result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>