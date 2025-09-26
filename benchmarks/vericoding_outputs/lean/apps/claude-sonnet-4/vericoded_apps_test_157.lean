import Mathlib
-- <vc-preamble>
def ValidInput (a b c : Int) : Prop :=
  1 ≤ a ∧ a ≤ 1000 ∧ 1 ≤ b ∧ b ≤ 1000 ∧ 1 ≤ c ∧ c ≤ 1000

def MaxRecipeUnits (a b c : Int) : Int :=
  min a (min (b / 2) (c / 4))

def TotalFruitsUsed (units : Int) : Int :=
  units * 7

@[reducible, simp]
def solve_precond (a b c : Int) : Prop :=
  ValidInput a b c
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic helper lemmas
lemma MaxRecipeUnits_nonneg (a b c : Int) (h : ValidInput a b c) : MaxRecipeUnits a b c ≥ 0 := by
  unfold MaxRecipeUnits ValidInput at *
  have ha : a ≥ 1 := h.1
  have hb : b ≥ 1 := h.2.2.1  
  have hc : c ≥ 1 := h.2.2.2.2.1
  have hb_div : b / 2 ≥ 0 := by
    apply Int.ediv_nonneg
    · linarith
    · norm_num
  have hc_div : c / 4 ≥ 0 := by
    apply Int.ediv_nonneg
    · linarith
    · norm_num
  have ha_pos : a ≥ 0 := by linarith
  exact le_min ha_pos (le_min hb_div hc_div)

lemma TotalFruitsUsed_nonneg (units : Int) (h : units ≥ 0) : TotalFruitsUsed units ≥ 0 := by
  unfold TotalFruitsUsed
  linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c : Int) (h_precond : solve_precond a b c) : Int :=
  TotalFruitsUsed (MaxRecipeUnits a b c)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c : Int) (result : Int) (h_precond : solve_precond a b c) : Prop :=
  result = TotalFruitsUsed (MaxRecipeUnits a b c) ∧ result ≥ 0

theorem solve_spec_satisfied (a b c : Int) (h_precond : solve_precond a b c) :
    solve_postcond a b c (solve a b c h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · rfl
  · apply TotalFruitsUsed_nonneg
    apply MaxRecipeUnits_nonneg
    exact h_precond
-- </vc-theorems>
