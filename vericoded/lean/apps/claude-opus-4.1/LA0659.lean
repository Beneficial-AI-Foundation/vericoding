import Mathlib
-- <vc-preamble>
def ValidInput (M : Int) : Prop :=
  1 ≤ M ∧ M ≤ 23

def HoursUntilNewYear (M : Int) (h : ValidInput M) : Int :=
  48 - M

def ValidOutput (M : Int) (result : Int) (h : ValidInput M) : Prop :=
  result = HoursUntilNewYear M h ∧ 25 ≤ result ∧ result ≤ 47

@[reducible, simp]
def solve_precond (M : Int) : Prop :=
  ValidInput M
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (M : Int) (h_precond : solve_precond M) : Int :=
  48 - M
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (M : Int) (result : Int) (h_precond : solve_precond M) : Prop :=
  ValidOutput M result h_precond

theorem solve_spec_satisfied (M : Int) (h_precond : solve_precond M) :
    solve_postcond M (solve M h_precond) h_precond := by
  unfold solve_postcond ValidOutput HoursUntilNewYear solve
  simp only [solve_precond, ValidInput] at h_precond
  obtain ⟨h_lower, h_upper⟩ := h_precond
  constructor
  · rfl
  · constructor
    · linarith
    · linarith
-- </vc-theorems>
