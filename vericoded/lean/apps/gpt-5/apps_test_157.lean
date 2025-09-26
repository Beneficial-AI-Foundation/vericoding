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
lemma maxRecipeUnits_nonneg_of_precond {a b c : Int}
    (h : ValidInput a b c) : 0 ≤ MaxRecipeUnits a b c := by
  rcases h with ⟨ha1, _, hb1, _, hc1, _⟩
  have ha0 : 0 ≤ a := le_trans (by decide : (0 : Int) ≤ 1) ha1
  have hb0 : 0 ≤ b := le_trans (by decide : (0 : Int) ≤ 1) hb1
  have hc0 : 0 ≤ c := le_trans (by decide : (0 : Int) ≤ 1) hc1
  have hb2 : 0 ≤ b / 2 := by
    have : 0 ≤ (2 : Int) := by decide
    exact Int.ediv_nonneg hb0 this
  have hc4 : 0 ≤ c / 4 := by
    have : 0 ≤ (4 : Int) := by decide
    exact Int.ediv_nonneg hc0 this
  have hmin : 0 ≤ min (b / 2) (c / 4) := le_min hb2 hc4
  exact le_min ha0 hmin

-- LLM HELPER
lemma totalFruits_nonneg_of_units_nonneg {u : Int} (hu : 0 ≤ u) :
    0 ≤ TotalFruitsUsed u := by
  have h7 : 0 ≤ (7 : Int) := by decide
  simpa [TotalFruitsUsed] using mul_nonneg hu h7
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
  dsimp [solve_postcond]
  constructor
  · simp [solve]
  ·
    have hU : 0 ≤ MaxRecipeUnits a b c := maxRecipeUnits_nonneg_of_precond h_precond
    change 0 ≤ solve a b c h_precond
    simpa [solve] using totalFruits_nonneg_of_units_nonneg hU
-- </vc-theorems>
