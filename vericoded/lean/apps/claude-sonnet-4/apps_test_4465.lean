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
-- LLM HELPER: Prove that RemainingFarmArea is non-negative under valid dimensions
lemma remaining_area_nonneg (a b : Int) (h : ValidFarmDimensions a b) : 
    RemainingFarmArea a b ≥ 0 := by
  unfold RemainingFarmArea ValidFarmDimensions at *
  have ha : a ≥ 2 := h.1
  have hb : b ≥ 2 := h.2.1  
  have h_calc : a * b - a - b + 1 = (a - 1) * (b - 1) := by ring
  rw [h_calc]
  have ha_pos : a - 1 ≥ 1 := by linarith
  have hb_pos : b - 1 ≥ 1 := by linarith
  exact Int.mul_nonneg (by linarith) (by linarith)
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
  unfold solve_postcond solve
  constructor
  · rfl
  · exact remaining_area_nonneg a b h_precond
-- </vc-theorems>
