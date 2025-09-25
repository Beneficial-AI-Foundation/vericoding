-- <vc-preamble>
def ValidTemperature (temp : Int) : Prop :=
  -40 ≤ temp ∧ temp ≤ 40

def ExpectedOutput (temp : Int) : String :=
  if temp ≥ 30 then "Yes\n" else "No\n"

def CorrectOutput (temp : Int) (output : String) : Prop :=
  output = ExpectedOutput temp

@[reducible, simp]
def solve_precond (X : Int) : Prop :=
  ValidTemperature X
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (X : Int) (h_precond : solve_precond X) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (X : Int) (result : String) (h_precond : solve_precond X) : Prop :=
  CorrectOutput X result

theorem solve_spec_satisfied (X : Int) (h_precond : solve_precond X) :
    solve_postcond X (solve X h_precond) h_precond := by
  sorry
-- </vc-theorems>