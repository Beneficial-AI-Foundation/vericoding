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
-- No additional helpers needed
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
  unfold solve_postcond solve MaxArea
  constructor
  · rfl
  constructor
  · split_ifs with h
    · exact le_refl _  -- LLM HELPER: A * B ≥ A * B is reflexive
    · push_neg at h
      exact le_of_lt h
  constructor
  · split_ifs with h
    · exact h  -- LLM HELPER: h gives us A * B ≥ C * D directly
    · exact le_refl _  -- LLM HELPER: C * D ≥ C * D is reflexive
  · split_ifs with h
    · left
      rfl
    · right
      rfl
-- </vc-theorems>
