-- <vc-preamble>
def ValidInput (A P : Int) : Prop :=
  0 ≤ A ∧ A ≤ 100 ∧ 0 ≤ P ∧ P ≤ 100

def TotalPieces (A P : Int) : Int :=
  A * 3 + P

def MaxPies (A P : Int) : Int :=
  TotalPieces A P / 2

@[reducible, simp]
def solve_precond (A P : Int) : Prop :=
  ValidInput A P
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (A P : Int) (h_precond : solve_precond A P) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A P : Int) (pies : Int) (h_precond : solve_precond A P) : Prop :=
  pies = MaxPies A P ∧ pies ≥ 0 ∧ pies = (A * 3 + P) / 2

theorem solve_spec_satisfied (A P : Int) (h_precond : solve_precond A P) :
    solve_postcond A P (solve A P h_precond) h_precond := by
  sorry
-- </vc-theorems>