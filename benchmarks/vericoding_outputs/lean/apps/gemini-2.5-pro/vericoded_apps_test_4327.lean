import Mathlib
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

-- LLM HELPER
private theorem total_pieces_nonneg (A P : Int) (h : ValidInput A P) : 0 ≤ TotalPieces A P := by
  unfold TotalPieces
  rcases h with ⟨hA_nonneg, _, hP_nonneg, _⟩
  linarith

-- </vc-helpers>

-- <vc-definitions>
def solve (A P : Int) (h_precond : solve_precond A P) : Int :=
  MaxPies A P
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A P : Int) (pies : Int) (h_precond : solve_precond A P) : Prop :=
  pies = MaxPies A P ∧ pies ≥ 0 ∧ pies = (A * 3 + P) / 2

theorem solve_spec_satisfied (A P : Int) (h_precond : solve_precond A P) :
    solve_postcond A P (solve A P h_precond) h_precond := by
  simp [solve, solve_postcond, MaxPies, TotalPieces]
  apply Int.ediv_nonneg
  · exact total_pieces_nonneg A P h_precond
  · norm_num
-- </vc-theorems>
