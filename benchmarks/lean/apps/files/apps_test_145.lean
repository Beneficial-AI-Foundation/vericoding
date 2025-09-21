-- <vc-preamble>
def CountDistinct (s : String) : Nat :=
  (s.toList.eraseDups).length

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  (input.length > 0 → input.data[input.length - 1]! = '\n') ∧
  input.length ≥ 2 ∧
  ∀ i, 0 ≤ i ∧ i < input.length - 1 → 
    'a' ≤ input.data[i]! ∧ input.data[i]! ≤ 'z'

def CorrectOutput (username : String) (output : String) : Prop :=
  let distinctCount := CountDistinct username
  (distinctCount % 2 = 1 → output = "IGNORE HIM!\n") ∧
  (distinctCount % 2 = 0 → output = "CHAT WITH HER!\n")

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
def solve_postcond (input : String) (output : String) (h_precond : solve_precond input) : Prop :=
  let username := input.take (input.length - 1)
  CorrectOutput username output

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>