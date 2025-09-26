import Mathlib
-- <vc-preamble>
def ValidInput (H W h w : Int) : Prop :=
  1 ≤ H ∧ H ≤ 20 ∧ 1 ≤ W ∧ W ≤ 20 ∧ 1 ≤ h ∧ h ≤ H ∧ 1 ≤ w ∧ w ≤ W

def WhiteCellsRemaining (H W h w : Int) : Int :=
  (H - h) * (W - w)

@[reducible, simp]
def solve_precond (H W h w : Int) : Prop :=
  ValidInput H W h w
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem sub_nonneg_of_le_int {a b : Int} (h : a ≤ b) : b - a ≥ 0 := by
  linarith

-- </vc-helpers>

-- <vc-definitions>
def solve (H W h w : Int) (h_precond : solve_precond H W h w) : Int :=
  (H - h) * (W - w)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (H W h w : Int) (result: Int) (h_precond : solve_precond H W h w) : Prop :=
  result = WhiteCellsRemaining H W h w ∧ result ≥ 0

theorem solve_spec_satisfied (H W h w : Int) (h_precond : solve_precond H W h w) :
    solve_postcond H W h w (solve H W h w h_precond) h_precond := by
  dsimp [solve_postcond, solve, WhiteCellsRemaining]
  constructor
  · rfl
  · let ⟨H_ge1, H_le20, W_ge1, W_le20, h_ge1, h_leH, w_ge1, w_leW⟩ := h_precond
    have H_sub_h_nonneg := sub_nonneg_of_le_int h_leH
    have W_sub_w_nonneg := sub_nonneg_of_le_int w_leW
    exact Int.mul_nonneg H_sub_h_nonneg W_sub_w_nonneg
-- </vc-theorems>
