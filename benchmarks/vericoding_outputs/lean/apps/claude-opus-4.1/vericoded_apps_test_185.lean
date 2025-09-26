import Mathlib
-- <vc-preamble>
def ValidInput (n k : Int) : Prop :=
  2 ≤ n ∧ n ≤ 5000 ∧ 1 ≤ k ∧ k ≤ n

def OptimalMoves (n k : Int) (h : ValidInput n k) : Int :=
  if k = 1 ∨ k = n then
    3 * n
  else
    3 * n + min (k - 1) (n - k)

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple implementation
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  OptimalMoves n k h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : Int) (h_precond : solve_precond n k) : Prop :=
  result = OptimalMoves n k h_precond ∧ result > 0

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · -- Prove result = OptimalMoves n k h_precond
    rfl
  · -- Prove result > 0
    unfold OptimalMoves
    rcases h_precond with ⟨h_n_ge, h_n_le, h_k_ge, h_k_le⟩
    split_ifs with h_edge
    · -- Case: k = 1 ∨ k = n
      calc 3 * n ≥ 3 * 2 := by linarith
               _ = 6 := by norm_num
               _ > 0 := by norm_num
    · -- Case: k ≠ 1 ∧ k ≠ n
      push_neg at h_edge
      have h_min_pos : min (k - 1) (n - k) ≥ 0 := by
        simp [min_def]
        split_ifs
        · linarith
        · linarith
      calc 3 * n + min (k - 1) (n - k) ≥ 3 * 2 + 0 := by linarith
                                      _ = 6 := by norm_num
                                      _ > 0 := by norm_num
-- </vc-theorems>
