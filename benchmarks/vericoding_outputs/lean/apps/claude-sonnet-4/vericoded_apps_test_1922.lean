import Mathlib
-- <vc-preamble>
def ValidInput (N M : Int) : Prop :=
  N ≥ 1 ∧ M ≥ 1

def CountFaceDownCards (N M : Int) : Int :=
  if N = 1 ∧ M = 1 then 1
  else if N = 1 then M - 2
  else if M = 1 then N - 2
  else (N - 2) * (M - 2)

@[reducible, simp]
def solve_precond (N M : Int) : Prop :=
  ValidInput N M
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma CountFaceDownCards_nonneg (N M : Int) (h : ValidInput N M) : CountFaceDownCards N M ≥ 0 := by
  unfold CountFaceDownCards ValidInput at *
  obtain ⟨hN, hM⟩ := h
  by_cases h1 : N = 1 ∧ M = 1
  · simp [h1]
  · by_cases h2 : N = 1
    · simp [h2]
      have hM_ne : M ≠ 1 := fun hM_eq => h1 ⟨h2, hM_eq⟩
      have : M ≥ 2 := by
        cases' lt_or_eq_of_le hM with hM_pos hM_eq
        · exact Int.add_one_le_of_lt hM_pos
        · exfalso; exact hM_ne hM_eq.symm
      -- Since M ≠ 1, the if condition fails and we get M - 2
      -- We know M ≥ 2, so M - 2 ≥ 0
      simp [hM_ne]
      linarith
    · by_cases h3 : M = 1
      · simp [h3, h2]
        have : N ≥ 2 := by
          cases' lt_or_eq_of_le hN with hN_pos hN_eq
          · exact Int.add_one_le_of_lt hN_pos
          · exfalso; exact h2 hN_eq.symm
        -- Since N ≠ 1, we get N - 2
        -- We know N ≥ 2, so N - 2 ≥ 0
        linarith
      · simp [h2, h3]
        have hN_ge : N ≥ 2 := by
          cases' lt_or_eq_of_le hN with hN_pos hN_eq
          · exact Int.add_one_le_of_lt hN_pos
          · exfalso; exact h2 hN_eq.symm
        have hM_ge : M ≥ 2 := by
          cases' lt_or_eq_of_le hM with hM_pos hM_eq
          · exact Int.add_one_le_of_lt hM_pos
          · exfalso; exact h3 hM_eq.symm
        apply mul_nonneg <;> linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (N M : Int) (h_precond : solve_precond N M) : Int :=
  CountFaceDownCards N M
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N M : Int) (result : Int) (h_precond : solve_precond N M) : Prop :=
  result = CountFaceDownCards N M ∧ result ≥ 0

theorem solve_spec_satisfied (N M : Int) (h_precond : solve_precond N M) :
    solve_postcond N M (solve N M h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · rfl
  · exact CountFaceDownCards_nonneg N M h_precond
-- </vc-theorems>
