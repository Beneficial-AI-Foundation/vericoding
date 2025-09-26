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
-- LLM HELPER Helper lemmas for integer arithmetic and properties
lemma TotalPieces_eq (A P : Int) : TotalPieces A P = A * 3 + P := by rfl

lemma MaxPies_eq (A P : Int) : MaxPies A P = (A * 3 + P) / 2 := by rfl

lemma TotalPieces_nonneg (A P : Int) (h_valid : ValidInput A P) : 0 ≤ TotalPieces A P := by
  rw [TotalPieces_eq]
  have hA : 0 ≤ A := h_valid.1
  have hP : 0 ≤ P := h_valid.2.2.1
  linarith

lemma MaxPies_nonneg (A P : Int) (h_valid : ValidInput A P) : 0 ≤ MaxPies A P := by
  rw [MaxPies_eq]
  have h_total_nonneg : 0 ≤ TotalPieces A P := TotalPieces_nonneg A P h_valid
  apply Int.ediv_nonneg h_total_nonneg (by decide)
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
  unfold solve_postcond
  constructor
  · rfl
  constructor
  · apply MaxPies_nonneg A P h_precond
  · rfl
-- </vc-theorems>
