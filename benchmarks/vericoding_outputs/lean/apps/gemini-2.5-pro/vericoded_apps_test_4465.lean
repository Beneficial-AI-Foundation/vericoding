import Mathlib
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
-- LLM HELPER
lemma remaining_area_nonnegative (a b : Int) (h : ValidFarmDimensions a b) :
  RemainingFarmArea a b ≥ 0 := by
  rw [RemainingFarmArea, show a * b - a - b + 1 = (a - 1) * (b - 1) by ring]
  rcases h with ⟨ha, hb, _, _⟩
  apply mul_nonneg <;> linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  RemainingFarmArea a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int) (h_precond : solve_precond a b) : Prop :=
  result = RemainingFarmArea a b ∧ result ≥ 0

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  simp [solve_postcond, solve]
  exact remaining_area_nonnegative a b h_precond
-- </vc-theorems>
