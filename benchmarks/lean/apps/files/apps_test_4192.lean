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
-- </vc-helpers>

-- <vc-definitions>
def solve (D T S : Int) (h_precond : solve_precond D T S) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (D T S : Int) (result : String) (h_precond : solve_precond D T S) : Prop :=
  (CanTravel D T S → result = "Yes") ∧ (¬CanTravel D T S → result = "No")

theorem solve_spec_satisfied (D T S : Int) (h_precond : solve_precond D T S) :
    solve_postcond D T S (solve D T S h_precond) h_precond := by
  sorry
-- </vc-theorems>