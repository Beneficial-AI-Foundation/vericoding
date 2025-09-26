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
lemma valid_brothers_sum (a b : Int) (h : ValidBrotherNumbers a b) : 
    a + b + (6 - a - b) = 6 := by
  ring

-- LLM HELPER  
lemma late_brother_valid (a b : Int) (h : ValidBrotherNumbers a b) :
    1 ≤ LateBrother a b ∧ LateBrother a b ≤ 3 := by
  unfold ValidBrotherNumbers at h
  unfold LateBrother
  obtain ⟨ha1, ha3, hb1, hb3, hab⟩ := h
  constructor
  · -- 1 ≤ 6 - a - b
    omega
  · -- 6 - a - b ≤ 3
    omega

-- LLM HELPER
lemma late_brother_distinct (a b : Int) (h : ValidBrotherNumbers a b) :
    LateBrother a b ≠ a ∧ LateBrother a b ≠ b := by
  unfold ValidBrotherNumbers at h
  unfold LateBrother
  obtain ⟨ha1, ha3, hb1, hb3, hab⟩ := h
  constructor <;> intro eq <;> omega
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
  unfold solve_postcond solve
  simp only [solve_precond] at h_precond
  constructor
  · -- IsValidResult a b (LateBrother a b)
    unfold IsValidResult
    intro _
    obtain ⟨h_lower, h_upper⟩ := late_brother_valid a b h_precond
    obtain ⟨h_ne_a, h_ne_b⟩ := late_brother_distinct a b h_precond
    exact ⟨h_lower, h_upper, h_ne_a, h_ne_b⟩
  · -- LateBrother a b = LateBrother a b
    rfl
-- </vc-theorems>
