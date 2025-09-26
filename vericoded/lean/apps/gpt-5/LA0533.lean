import Mathlib
-- <vc-preamble>
def ValidInput (A1 A2 A3 : Int) : Prop :=
  1 ≤ A1 ∧ A1 ≤ 100 ∧ 1 ≤ A2 ∧ A2 ≤ 100 ∧ 1 ≤ A3 ∧ A3 ≤ 100

def MaxOfThree (A1 A2 A3 : Int) : Int :=
  if A1 ≥ A2 ∧ A1 ≥ A3 then A1 else if A2 ≥ A3 then A2 else A3

def MinOfThree (A1 A2 A3 : Int) : Int :=
  if A1 ≤ A2 ∧ A1 ≤ A3 then A1 else if A2 ≤ A3 then A2 else A3

def MinimumCost (A1 A2 A3 : Int) : Int :=
  MaxOfThree A1 A2 A3 - MinOfThree A1 A2 A3

@[reducible, simp]
def solve_precond (A1 A2 A3 : Int) : Prop :=
  ValidInput A1 A2 A3
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma le_MaxOfThree_left (A1 A2 A3 : Int) : A1 ≤ MaxOfThree A1 A2 A3 := by
  classical
  unfold MaxOfThree
  by_cases h1 : A1 ≥ A2 ∧ A1 ≥ A3
  · simp [h1]
  · by_cases h2 : A2 ≥ A3
    · have hA1leA2 : A1 ≤ A2 := by
        by_contra h
        have hA2ltA1 : A2 < A1 := lt_of_not_ge h
        have h_ge2 : A1 ≥ A2 := le_of_lt hA2ltA1
        have h_ge3 : A1 ≥ A3 := by
          have : A3 ≤ A2 := h2
          exact le_trans this (le_of_lt hA2ltA1)
        exact (h1 ⟨h_ge2, h_ge3⟩).elim
      simp [h1, h2, hA1leA2]
    · have h2' : A2 < A3 := lt_of_not_ge h2
      have hA1leA3 : A1 ≤ A3 := by
        by_contra h
        have hA3ltA1 : A3 < A1 := lt_of_not_ge h
        have h_ge2 : A1 ≥ A2 := by
          have : A2 ≤ A3 := le_of_lt h2'
          have : A2 ≤ A1 := le_trans this (le_of_lt hA3ltA1)
          exact this
        have h_ge3 : A1 ≥ A3 := le_of_lt hA3ltA1
        exact (h1 ⟨h_ge2, h_ge3⟩).elim
      simp [h1, h2, hA1leA3]

-- LLM HELPER
lemma MinOfThree_le_left (A1 A2 A3 : Int) : MinOfThree A1 A2 A3 ≤ A1 := by
  classical
  unfold MinOfThree
  by_cases h1 : A1 ≤ A2 ∧ A1 ≤ A3
  · simp [h1]
  · by_cases h2 : A2 ≤ A3
    · have hA2leA1 : A2 ≤ A1 := by
        by_contra h
        have hA1ltA2 : A1 < A2 := lt_of_not_ge h
        have h_le2 : A1 ≤ A2 := le_of_lt hA1ltA2
        have h_le3 : A1 ≤ A3 := le_trans (le_of_lt hA1ltA2) h2
        exact (h1 ⟨h_le2, h_le3⟩).elim
      simp [h1, h2, hA2leA1]
    · have h2' : A3 < A2 := lt_of_not_ge h2
      have hA3leA1 : A3 ≤ A1 := by
        by_contra h
        have hA1ltA3 : A1 < A3 := lt_of_not_ge h
        have h_le2 : A1 ≤ A2 := le_trans (le_of_lt hA1ltA3) (le_of_lt h2')
        have h_le3 : A1 ≤ A3 := le_of_lt hA1ltA3
        exact (h1 ⟨h_le2, h_le3⟩).elim
      simp [h1, h2, hA3leA1]

-- LLM HELPER
lemma minimumCost_nonneg (A1 A2 A3 : Int) : 0 ≤ MinimumCost A1 A2 A3 := by
  unfold MinimumCost
  have hle : MinOfThree A1 A2 A3 ≤ MaxOfThree A1 A2 A3 :=
    le_trans (MinOfThree_le_left A1 A2 A3) (le_MaxOfThree_left A1 A2 A3)
  simpa using sub_nonneg.mpr hle
-- </vc-helpers>

-- <vc-definitions>
def solve (A1 A2 A3 : Int) (h_precond : solve_precond A1 A2 A3) : Int :=
  MinimumCost A1 A2 A3
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A1 A2 A3 : Int) (result: Int) (h_precond : solve_precond A1 A2 A3) : Prop :=
  result ≥ 0 ∧ result = MinimumCost A1 A2 A3

theorem solve_spec_satisfied (A1 A2 A3 : Int) (h_precond : solve_precond A1 A2 A3) :
    solve_postcond A1 A2 A3 (solve A1 A2 A3 h_precond) h_precond := by
  constructor
  · simpa [solve] using minimumCost_nonneg A1 A2 A3
  · simp [solve]
-- </vc-theorems>
