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
lemma white_cells_nonneg (H W h w : Int) (h_valid : ValidInput H W h w) :
  WhiteCellsRemaining H W h w ≥ 0 := by
  rcases h_valid with ⟨_, _, _, _, _, h_le_H, _, w_le_W⟩
  unfold WhiteCellsRemaining
  have h_diff_nonneg : H - h ≥ 0 := sub_nonneg.mpr h_le_H
  have w_diff_nonneg : W - w ≥ 0 := sub_nonneg.mpr w_le_W
  exact mul_nonneg h_diff_nonneg w_diff_nonneg
-- </vc-helpers>

-- <vc-definitions>
def solve (H W h w : Int) (h_precond : solve_precond H W h w) : Int :=
  WhiteCellsRemaining H W h w
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (H W h w : Int) (result: Int) (h_precond : solve_precond H W h w) : Prop :=
  result = WhiteCellsRemaining H W h w ∧ result ≥ 0

theorem solve_spec_satisfied (H W h w : Int) (h_precond : solve_precond H W h w) :
    solve_postcond H W h w (solve H W h w h_precond) h_precond := by
  simp [solve]
  exact white_cells_nonneg H W h w h_precond
-- </vc-theorems>
