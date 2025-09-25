-- <vc-preamble>
def ValidFarmDimensions (a b : Int) : Prop :=
  a ≥ 2 ∧ b ≥ 2 ∧ a ≤ 100 ∧ b ≤ 100

def RemainingFarmArea (a b : Int) : Int :=
  a * b - a - b + 1

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidFarmDimensions a b
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int) (h_precond : solve_precond a b) : Prop :=
  result = RemainingFarmArea a b ∧ result ≥ 0

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  sorry
-- </vc-theorems>