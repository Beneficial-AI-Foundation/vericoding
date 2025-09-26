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
-- LLM HELPER: Helper lemma for total pieces being nonnegative
lemma total_pieces_nonneg (A P : Int) (h : ValidInput A P) : 0 ≤ TotalPieces A P := by
  unfold TotalPieces ValidInput at *
  have hA := h.1
  have hP := h.2.2
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
  unfold solve_postcond solve MaxPies TotalPieces
  constructor
  · rfl
  constructor
  · apply Int.ediv_nonneg
    · apply total_pieces_nonneg
      exact h_precond
    · norm_num
  · rfl
-- </vc-theorems>
