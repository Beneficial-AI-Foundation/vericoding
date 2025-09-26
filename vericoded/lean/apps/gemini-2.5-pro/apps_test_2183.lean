import Mathlib
-- <vc-preamble>
def ValidBrotherNumbers (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3 ∧ a ≠ b

def LateBrother (a b : Int) : Int :=
  6 - a - b

def IsValidResult (a b result : Int) : Prop :=
  ValidBrotherNumbers a b → (1 ≤ result ∧ result ≤ 3 ∧ result ≠ a ∧ result ≠ b)

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidBrotherNumbers a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma sum_bounds (a b : Int) (h : ValidBrotherNumbers a b) : 3 ≤ a + b ∧ a + b ≤ 5 := by
  rcases h with ⟨ha1, ha3, hb1, hb3, habne⟩
  interval_cases a
  · -- a = 1
    interval_cases b
    · -- b = 1
      exfalso; apply habne; simp_all
    · -- b = 2
      constructor <;> norm_num
    · -- b = 3
      constructor <;> norm_num
  · -- a = 2
    interval_cases b
    · -- b = 1
      constructor <;> norm_num
    · -- b = 2
      exfalso; apply habne; simp_all
    · -- b = 3
      constructor <;> norm_num
  · -- a = 3
    interval_cases b
    · -- b = 1
      constructor <;> norm_num
    · -- b = 2
      constructor <;> norm_num
    · -- b = 3
      exfalso; apply habne; simp_all

-- LLM HELPER
lemma late_brother_bounds (a b : Int) (h : ValidBrotherNumbers a b) : 1 ≤ LateBrother a b ∧ LateBrother a b ≤ 3 := by
  have h_sum_bounds := sum_bounds a b h
  dsimp [LateBrother]
  constructor
  · linarith [h_sum_bounds.2]
  · linarith [h_sum_bounds.1]

-- LLM HELPER
lemma late_brother_ne_a (a b : Int) (h : ValidBrotherNumbers a b) : LateBrother a b ≠ a := by
  intro h_eq
  dsimp [LateBrother] at h_eq
  have h_eq' : 2 * a + b = 6 := by linarith
  rcases h with ⟨ha1, ha3, hb1, hb3, habne⟩
  interval_cases a
  · -- a = 1
    have : b = 4 := by linarith
    linarith [this, hb3]
  · -- a = 2
    have : b = 2 := by linarith
    subst this
    contradiction
  · -- a = 3
    have : b = 0 := by linarith
    linarith [this, hb1]

-- LLM HELPER
lemma late_brother_ne_b (a b : Int) (h : ValidBrotherNumbers a b) : LateBrother a b ≠ b := by
  intro h_eq
  dsimp [LateBrother] at h_eq
  have h_eq' : a + 2 * b = 6 := by linarith
  rcases h with ⟨ha1, ha3, hb1, hb3, habne⟩
  interval_cases b
  · -- b = 1
    have : a = 4 := by linarith
    linarith [this, ha3]
  · -- b = 2
    have : a = 2 := by linarith
    subst this
    contradiction
  · -- b = 3
    have : a = 0 := by linarith
    linarith [this, ha1]

-- LLM HELPER
lemma late_brother_is_valid (a b : Int) (h_precond : ValidBrotherNumbers a b) :
    IsValidResult a b (LateBrother a b) := by
  unfold IsValidResult
  intro h
  have h_bounds := late_brother_bounds a b h_precond
  have h_ne_a := late_brother_ne_a a b h_precond
  have h_ne_b := late_brother_ne_b a b h_precond
  exact ⟨h_bounds.1, h_bounds.2, h_ne_a, h_ne_b⟩

-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  LateBrother a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  IsValidResult a b result ∧ result = LateBrother a b

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  dsimp [solve_postcond, solve]
  constructor
  · apply late_brother_is_valid
    exact h_precond
  · rfl
-- </vc-theorems>
