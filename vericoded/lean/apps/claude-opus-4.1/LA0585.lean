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
lemma remaining_farm_area_factorization (a b : Int) :
    RemainingFarmArea a b = (a - 1) * (b - 1) := by
  unfold RemainingFarmArea
  ring

-- LLM HELPER
lemma remaining_farm_area_nonneg (a b : Int) (h : ValidFarmDimensions a b) :
    RemainingFarmArea a b ≥ 0 := by
  rw [remaining_farm_area_factorization]
  have ha : a ≥ 2 := h.1
  have hb : b ≥ 2 := h.2.1
  have : a - 1 ≥ 1 := by omega
  have : b - 1 ≥ 1 := by omega
  apply mul_nonneg <;> omega
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
  unfold solve solve_postcond
  constructor
  · rfl
  · exact remaining_farm_area_nonneg a b h_precond
-- </vc-theorems>
