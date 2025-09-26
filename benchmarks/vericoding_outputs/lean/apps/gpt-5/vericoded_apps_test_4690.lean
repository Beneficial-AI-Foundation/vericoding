import Mathlib
-- <vc-preamble>
def ValidInput (A B C D : Int) : Prop :=
  1 ≤ A ∧ A ≤ 10000 ∧ 1 ≤ B ∧ B ≤ 10000 ∧ 1 ≤ C ∧ C ≤ 10000 ∧ 1 ≤ D ∧ D ≤ 10000

def MaxArea (A B C D : Int) : Int :=
  if A * B ≥ C * D then A * B else C * D

@[reducible, simp]
def solve_precond (A B C D : Int) : Prop :=
  ValidInput A B C D
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma MaxArea_eq_left_or_right (A B C D : Int) :
    MaxArea A B C D = A * B ∨ MaxArea A B C D = C * D := by
  unfold MaxArea
  by_cases h : A * B ≥ C * D
  · simp [h]
  · simp [h]

-- LLM HELPER
lemma MaxArea_ge_left (A B C D : Int) :
    MaxArea A B C D ≥ A * B := by
  unfold MaxArea
  by_cases h : A * B ≥ C * D
  · have : A * B ≥ A * B := le_rfl
    simpa [h] using this
  · have hlt : A * B < C * D := lt_of_not_ge h
    have hle : A * B ≤ C * D := le_of_lt hlt
    simpa [h] using hle

-- LLM HELPER
lemma MaxArea_ge_right (A B C D : Int) :
    MaxArea A B C D ≥ C * D := by
  unfold MaxArea
  by_cases h : A * B ≥ C * D
  · have : A * B ≥ C * D := h
    simpa [h] using this
  · have : C * D ≥ C * D := le_rfl
    simpa [h] using this
-- </vc-helpers>

-- <vc-definitions>
def solve (A B C D : Int) (h_precond : solve_precond A B C D) : Int :=
  MaxArea A B C D
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (A B C D : Int) (result: Int) (h_precond : solve_precond A B C D) : Prop :=
  result = MaxArea A B C D ∧ result ≥ A * B ∧ result ≥ C * D ∧ (result = A * B ∨ result = C * D)

theorem solve_spec_satisfied (A B C D : Int) (h_precond : solve_precond A B C D) :
    solve_postcond A B C D (solve A B C D h_precond) h_precond := by
    -- establish properties of solve
  have h1 : solve A B C D h_precond = MaxArea A B C D := rfl
  have h2 : solve A B C D h_precond ≥ A * B := by
    simpa [solve] using MaxArea_ge_left A B C D
  have h3 : solve A B C D h_precond ≥ C * D := by
    simpa [solve] using MaxArea_ge_right A B C D
  have h4 : solve A B C D h_precond = A * B ∨ solve A B C D h_precond = C * D := by
    simpa [solve] using MaxArea_eq_left_or_right A B C D
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))
-- </vc-theorems>
