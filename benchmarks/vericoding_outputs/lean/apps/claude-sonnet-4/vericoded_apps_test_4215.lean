import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100

def UncoveredLength (a b : Int) : Int :=
  max 0 (a - 2 * b)

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: lemma about max and conditional
lemma max_zero_sub_eq_ite (a b : Int) : max 0 (a - 2 * b) = if a > 2 * b then a - 2 * b else 0 := by
  by_cases h : a > 2 * b
  · -- Case: a > 2 * b, so a - 2 * b > 0
    have h_pos : a - 2 * b > 0 := by linarith
    rw [max_eq_right]
    · simp [h]
    · exact Int.le_of_lt h_pos
  · -- Case: a ≤ 2 * b, so a - 2 * b ≤ 0  
    have h_nonpos : a - 2 * b ≤ 0 := by linarith
    rw [max_eq_left h_nonpos]
    simp [h]
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  UncoveredLength a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result: Int) (h_precond : solve_precond a b) : Prop :=
  result ≥ 0 ∧ result = UncoveredLength a b ∧ result = (if a > 2 * b then a - 2 * b else 0)

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve UncoveredLength
  constructor
  · exact Int.le_max_left 0 (a - 2 * b)
  constructor
  · rfl
  · exact max_zero_sub_eq_ite a b
-- </vc-theorems>
