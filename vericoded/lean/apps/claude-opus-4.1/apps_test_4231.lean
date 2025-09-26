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
lemma white_cells_non_negative (H W h w : Int) (hValid : ValidInput H W h w) :
    WhiteCellsRemaining H W h w ≥ 0 := by
  unfold WhiteCellsRemaining ValidInput at *
  have ⟨hH_pos, hH_bound, hW_pos, hW_bound, hh_pos, hh_bound, hw_pos, hw_bound⟩ := hValid
  have h_diff : H - h ≥ 0 := Int.sub_nonneg_of_le hh_bound
  have w_diff : W - w ≥ 0 := Int.sub_nonneg_of_le hw_bound
  exact Int.mul_nonneg h_diff w_diff
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
  unfold solve_postcond solve
  constructor
  · rfl
  · exact white_cells_non_negative H W h w h_precond
-- </vc-theorems>
