-- <vc-preamble>
def ValidInput (A B T : Int) : Prop :=
  1 ≤ A ∧ A ≤ 20 ∧ 1 ≤ B ∧ B ≤ 20 ∧ 1 ≤ T ∧ T ≤ 20

def ProductionCount (A T : Int) : Int :=
  if A > 0 then T / A else 0

def TotalBiscuits (A B T : Int) : Int :=
  if A > 0 then B * ProductionCount A T else 0

@[reducible, simp]
def solve_precond (A B T : Int) : Prop :=
  ValidInput A B T
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A B T : Int) (h_precond : solve_precond A B T) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B T : Int) (result : Int) (h_precond : solve_precond A B T) : Prop :=
  result = TotalBiscuits A B T

theorem solve_spec_satisfied (A B T : Int) (h_precond : solve_precond A B T) :
    solve_postcond A B T (solve A B T h_precond) h_precond := by
  sorry
-- </vc-theorems>