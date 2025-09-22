-- <vc-preamble>
def IsHardToEnter (s : String) : Prop :=
  s.length = 4 → (s.data.get! 0 = s.data.get! 1 ∨ s.data.get! 1 = s.data.get! 2 ∨ s.data.get! 2 = s.data.get! 3)

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  s.length = 4
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  (result = "Bad" ↔ IsHardToEnter s) ∧ (result = "Good" ↔ ¬IsHardToEnter s)

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  sorry
-- </vc-theorems>