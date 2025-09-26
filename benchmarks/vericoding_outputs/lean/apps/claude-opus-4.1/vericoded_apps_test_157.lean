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
-- LLM HELPER
lemma max_recipe_units_nonneg (a b c : Int) (h : ValidInput a b c) : 
    MaxRecipeUnits a b c ≥ 0 := by
  unfold MaxRecipeUnits ValidInput at *
  obtain ⟨ha1, ha2, hb1, hb2, hc1, hc2⟩ := h
  simp only [min_def]
  split_ifs <;> try linarith
  · apply Int.ediv_nonneg <;> linarith
  · apply Int.ediv_nonneg <;> linarith
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
  unfold solve solve_postcond TotalFruitsUsed
  constructor
  · rfl
  · unfold solve_precond ValidInput at h_precond
    apply mul_nonneg
    · apply max_recipe_units_nonneg
      exact h_precond
    · norm_num
-- </vc-theorems>
