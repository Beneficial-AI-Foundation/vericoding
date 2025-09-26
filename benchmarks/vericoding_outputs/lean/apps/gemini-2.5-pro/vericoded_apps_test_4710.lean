import Mathlib
-- <vc-preamble>
def ValidInput (x : Int) : Prop :=
  1 ≤ x ∧ x ≤ 3000

def CorrectOutput (x : Int) (result : String) : Prop :=
  (x < 1200 → result = "ABC\n") ∧ (x ≥ 1200 → result = "ARC\n")

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  ValidInput x
-- </vc-preamble>

-- <vc-helpers>
-- No helpers are needed for this problem.
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : String :=
  if x < 1200 then "ABC\n" else "ARC\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x : Int) (result : String) (h_precond : solve_precond x) : Prop :=
  CorrectOutput x result

theorem solve_spec_satisfied (x : Int) (h_precond : solve_precond x) :
    solve_postcond x (solve x h_precond) h_precond := by
  simp [solve, solve_postcond, CorrectOutput]
-- </vc-theorems>
