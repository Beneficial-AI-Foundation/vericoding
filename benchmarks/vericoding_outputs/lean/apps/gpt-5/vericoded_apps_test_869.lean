import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a ≥ 1 ∧ b ≥ 1

def MaxDifferentDays (a b : Int) : Int :=
  if a < b then a else b

def RemainingAfterDifferent (a b : Int) : Int :=
  if a > b then a - MaxDifferentDays a b else b - MaxDifferentDays a b

def SameDays (a b : Int) : Int :=
  RemainingAfterDifferent a b / 2

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma MaxDifferentDays_le_left (a b : Int) : MaxDifferentDays a b ≤ a := by
  unfold MaxDifferentDays
  by_cases h : a < b
  · have : a ≤ a := le_rfl
    simpa [h] using this
  ·
    have hb_le_a : b ≤ a := by
      have h' : ¬ b > a := by simpa [gt_iff_lt] using h
      exact le_of_not_gt h'
    simpa [h] using hb_le_a

-- LLM HELPER
lemma MaxDifferentDays_le_right (a b : Int) : MaxDifferentDays a b ≤ b := by
  unfold MaxDifferentDays
  by_cases h : a < b
  · have : a ≤ b := le_of_lt h
    simpa [h] using this
  ·
    have : b ≤ b := le_rfl
    simpa [h] using this

-- LLM HELPER
lemma MaxDifferentDays_nonneg (a b : Int) (h : ValidInput a b) : 0 ≤ MaxDifferentDays a b := by
  rcases h with ⟨ha, hb⟩
  unfold MaxDifferentDays
  by_cases hlt : a < b
  · have : 0 ≤ a := le_trans (by decide : (0 : Int) ≤ 1) ha
    simpa [hlt] using this
  · have : 0 ≤ b := le_trans (by decide : (0 : Int) ≤ 1) hb
    simpa [hlt] using this

-- LLM HELPER
lemma RemainingAfterDifferent_nonneg (a b : Int) : 0 ≤ RemainingAfterDifferent a b := by
  unfold RemainingAfterDifferent
  by_cases hgt : a > b
  · have hnot : ¬ a < b := not_lt_of_ge (le_of_lt hgt)
    have : 0 ≤ a - b := sub_nonneg.mpr (le_of_lt hgt)
    simpa [hgt, MaxDifferentDays, hnot] using this
  ·
    have : 0 ≤ b - MaxDifferentDays a b := sub_nonneg.mpr (MaxDifferentDays_le_right a b)
    simpa [hgt] using this

-- LLM HELPER
lemma SameDays_nonneg (a b : Int) : 0 ≤ SameDays a b := by
  unfold SameDays
  have hrem : 0 ≤ RemainingAfterDifferent a b := RemainingAfterDifferent_nonneg a b
  have h2 : 0 ≤ (2 : Int) := by decide
  simpa using Int.ediv_nonneg hrem h2
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int × Int :=
  (MaxDifferentDays a b, SameDays a b)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int × Int) (h_precond : solve_precond a b) : Prop :=
  result.1 = MaxDifferentDays a b ∧
  result.2 = SameDays a b ∧
  result.1 ≥ 0 ∧
  result.2 ≥ 0 ∧
  result.1 ≤ a ∧ result.1 ≤ b

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact MaxDifferentDays_nonneg a b h_precond
  constructor
  · exact SameDays_nonneg a b
  constructor
  · exact MaxDifferentDays_le_left a b
  · exact MaxDifferentDays_le_right a b
-- </vc-theorems>
