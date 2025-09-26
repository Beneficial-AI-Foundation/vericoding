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
-- LLM HELPER: Properties of MaxArea for easier proof
lemma MaxArea_ge_left (A B C D : Int) : MaxArea A B C D ≥ A * B := by
  unfold MaxArea
  split_ifs with h
  · rfl
  · linarith

lemma MaxArea_ge_right (A B C D : Int) : MaxArea A B C D ≥ C * D := by
  unfold MaxArea
  split_ifs with h
  · exact h
  · rfl

lemma MaxArea_is_one_of (A B C D : Int) : MaxArea A B C D = A * B ∨ MaxArea A B C D = C * D := by
  unfold MaxArea
  split_ifs
  · left; rfl
  · right; rfl
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
  unfold solve solve_postcond
  simp [MaxArea_ge_left, MaxArea_ge_right, MaxArea_is_one_of]
-- </vc-theorems>
