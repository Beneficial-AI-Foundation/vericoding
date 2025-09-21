-- <vc-preamble>
def ValidOutcome (outcome : String) : Prop :=
  outcome = "delicious" ∨ outcome = "safe" ∨ outcome = "dangerous"

def DaysPastBestBy (A B : Int) : Int :=
  B - A

def ExpectedOutcome (X A B : Int) : String :=
  let daysPast := DaysPastBestBy A B
  if daysPast ≤ 0 then "delicious"
  else if daysPast ≤ X then "safe"
  else "dangerous"

@[reducible, simp]
def solve_precond (X A B : Int) : Prop :=
  X ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (X A B : Int) (h_precond : solve_precond X A B) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (X A B : Int) (outcome : String) (h_precond : solve_precond X A B) : Prop :=
  outcome = ExpectedOutcome X A B ∧ ValidOutcome outcome

theorem solve_spec_satisfied (X A B : Int) (h_precond : solve_precond X A B) :
    solve_postcond X A B (solve X A B h_precond) h_precond := by
  sorry
-- </vc-theorems>