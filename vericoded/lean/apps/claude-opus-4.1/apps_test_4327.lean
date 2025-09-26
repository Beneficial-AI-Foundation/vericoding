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
lemma maxpies_nonneg (A P : Int) (h : ValidInput A P) : MaxPies A P ≥ 0 := by
  unfold MaxPies TotalPieces ValidInput at *
  obtain ⟨ha_pos, ha_bound, hp_pos, hp_bound⟩ := h
  have h_total : 0 ≤ A * 3 + P := by linarith
  exact Int.ediv_nonneg h_total (by norm_num)
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
  unfold solve_postcond solve MaxPies
  constructor
  · rfl
  constructor
  · exact maxpies_nonneg A P h_precond
  · rfl
-- </vc-theorems>
