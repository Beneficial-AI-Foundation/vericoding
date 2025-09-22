-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0

def ValidOutput (result : List Int) (input : String) : Prop :=
  result.length ≥ 0 ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! ≥ 1) ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]! ≤ result.length)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : List Int) (h_precond : solve_precond input) : Prop :=
  ValidOutput result input

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>