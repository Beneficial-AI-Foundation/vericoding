import Mathlib
-- <vc-preamble>
def ValidInput (x1 x2 x3 : Int) : Prop :=
  1 ≤ x1 ∧ x1 ≤ 100 ∧ 1 ≤ x2 ∧ x2 ≤ 100 ∧ 1 ≤ x3 ∧ x3 ≤ 100 ∧
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x2 ≠ x3

def MinTotalDistance (x1 x2 x3 : Int) : Int :=
  let max_pos := if x1 ≥ x2 ∧ x1 ≥ x3 then x1
                 else if x2 ≥ x1 ∧ x2 ≥ x3 then x2
                 else x3
  let min_pos := if x1 ≤ x2 ∧ x1 ≤ x3 then x1
                 else if x2 ≤ x1 ∧ x2 ≤ x3 then x2
                 else x3
  max_pos - min_pos

@[reducible, simp]
def solve_precond (x1 x2 x3 : Int) : Prop :=
  ValidInput x1 x2 x3
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma min_total_distance_bounds (x1 x2 x3 : Int) (h : ValidInput x1 x2 x3) :
    1 ≤ MinTotalDistance x1 x2 x3 ∧ MinTotalDistance x1 x2 x3 ≤ 99 := by
  unfold MinTotalDistance ValidInput at *
  obtain ⟨h1_lower, h1_upper, h2_lower, h2_upper, h3_lower, h3_upper, h_ne12, h_ne13, h_ne23⟩ := h
  -- Split on the conditions for max_pos and min_pos
  by_cases hmax1 : x1 ≥ x2 ∧ x1 ≥ x3
  · -- x1 is max
    by_cases hmin1 : x1 ≤ x2 ∧ x1 ≤ x3
    · -- x1 is both max and min, contradiction with distinctness
      simp at hmax1 hmin1
      have : x1 = x2 ∨ x1 = x3 := by omega
      cases this <;> omega
    · by_cases hmin2 : x2 ≤ x1 ∧ x2 ≤ x3
      · -- x1 is max, x2 is min
        simp [hmax1, hmin1, hmin2]
        omega
      · -- x1 is max, x3 is min
        simp [hmax1, hmin1, hmin2]
        omega
  · by_cases hmax2 : x2 ≥ x1 ∧ x2 ≥ x3
    · -- x2 is max
      by_cases hmin1 : x1 ≤ x2 ∧ x1 ≤ x3
      · -- x2 is max, x1 is min
        simp [hmax1, hmax2, hmin1]
        omega
      · by_cases hmin2 : x2 ≤ x1 ∧ x2 ≤ x3
        · -- x2 is both max and min, contradiction
          simp at hmax2 hmin2
          have : x2 = x1 ∨ x2 = x3 := by omega
          cases this <;> omega
        · -- x2 is max, x3 is min
          simp [hmax1, hmax2, hmin1, hmin2]
          omega
    · -- x3 is max (neither x1 nor x2 is max)
      by_cases hmin1 : x1 ≤ x2 ∧ x1 ≤ x3
      · -- x3 is max, x1 is min
        simp [hmax1, hmax2, hmin1]
        omega
      · by_cases hmin2 : x2 ≤ x1 ∧ x2 ≤ x3
        · -- x3 is max, x2 is min
          simp [hmax1, hmax2, hmin1, hmin2]
          omega
        · -- x3 is both max and min, impossible when all distinct
          simp [hmax1, hmax2, hmin1, hmin2]
          -- At this point x3 must be both max and min which means equal to others
          have hx3_ge : x3 ≥ x1 ∧ x3 ≥ x2 := by omega
          have hx3_le : x3 ≤ x1 ∧ x3 ≤ x2 := by omega
          have : x3 = x1 ∨ x3 = x2 := by omega
          cases this <;> omega
-- </vc-helpers>

-- <vc-definitions>
def solve (x1 x2 x3 : Int) (h_precond : solve_precond x1 x2 x3) : Int :=
  MinTotalDistance x1 x2 x3
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x1 x2 x3 : Int) (result : Int) (h_precond : solve_precond x1 x2 x3) : Prop :=
  result = MinTotalDistance x1 x2 x3 ∧ result ≥ 1 ∧ result ≤ 99

theorem solve_spec_satisfied (x1 x2 x3 : Int) (h_precond : solve_precond x1 x2 x3) :
    solve_postcond x1 x2 x3 (solve x1 x2 x3 h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · rfl
  · exact min_total_distance_bounds x1 x2 x3 h_precond
-- </vc-theorems>
