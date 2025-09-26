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
-- LLM HELPER: Lemma to prove non-negativity of WhiteCellsRemaining
lemma white_cells_nonneg (H W h w : Int) (hv : ValidInput H W h w) : 
    WhiteCellsRemaining H W h w ≥ 0 := by
  unfold WhiteCellsRemaining ValidInput at *
  have ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hv
  have w_le : w ≤ W := h7.2
  have h_nonneg : H - h ≥ 0 := Int.sub_nonneg.mpr h6
  have w_nonneg : W - w ≥ 0 := Int.sub_nonneg.mpr w_le
  exact Int.mul_nonneg h_nonneg w_nonneg
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
  · exact white_cells_nonneg H W h w h_precond
-- </vc-theorems>
