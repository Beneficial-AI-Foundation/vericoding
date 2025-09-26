import Mathlib
-- <vc-preamble>
def ValidInput (D T S : Int) : Prop :=
  1 ≤ D ∧ D ≤ 10000 ∧ 1 ≤ T ∧ T ≤ 10000 ∧ 1 ≤ S ∧ S ≤ 10000

def CanTravel (D T S : Int) : Prop :=
  D ≤ T * S

@[reducible, simp]
def solve_precond (D T S : Int) : Prop :=
  ValidInput D T S
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: provide decidability for CanTravel to enable if-then-else on it
instance decCanTravel (D T S : Int) : Decidable (CanTravel D T S) :=
  show Decidable (D ≤ T * S) from inferInstance
-- </vc-helpers>

-- <vc-definitions>
def solve (D T S : Int) (h_precond : solve_precond D T S) : String :=
  if CanTravel D T S then "Yes" else "No"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (D T S : Int) (result : String) (h_precond : solve_precond D T S) : Prop :=
  (CanTravel D T S → result = "Yes") ∧ (¬CanTravel D T S → result = "No")

theorem solve_spec_satisfied (D T S : Int) (h_precond : solve_precond D T S) :
    solve_postcond D T S (solve D T S h_precond) h_precond := by
  constructor
  · intro h
    simp [solve, h]
  · intro hnot
    simp [solve, hnot]
-- </vc-theorems>
