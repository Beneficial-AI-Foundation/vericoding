-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length = 3 ∧ ∀ i, 0 ≤ i ∧ i < input.length → 
    let ch := input.toList[i]!
    ch = 'A' ∨ ch = 'B'

def BusServiceExists (input : String) (h_valid : ValidInput input) : Prop :=
  let ch0 := input.toList[0]!
  let ch1 := input.toList[1]!
  let ch2 := input.toList[2]!
  ch0 ≠ ch1 ∨ ch1 ≠ ch2

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
  (result = "Yes" ↔ BusServiceExists input h_precond) ∧ (result = "Yes" ∨ result = "No")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>