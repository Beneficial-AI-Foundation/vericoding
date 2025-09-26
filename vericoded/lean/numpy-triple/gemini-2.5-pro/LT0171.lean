import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
private theorem diag_index_in_bounds {n : Nat} (i : Fin n) : i.val * n + i.val < n * n := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n' =>
    have : i.val < n' + 1 := i.isLt
    calc
      i.val * (n' + 1) + i.val < i.val * (n' + 1) + (n' + 1) := by
        apply Nat.add_lt_add_left; assumption
      _ = (i.val + 1) * (n' + 1)                            := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (n' + 1) * (n' + 1)                               := by
        apply Nat.mul_le_mul_right; exact Nat.succ_le_of_lt this
-- </vc-helpers>

-- <vc-definitions>
def diag {n : Nat} (matrix : Vector Float (n * n)) : Vector Float n :=
  Vector.ofFn (fun i => matrix.get ⟨i.val * n + i.val, diag_index_in_bounds i⟩)
-- </vc-definitions>

-- <vc-theorems>
theorem diag_spec {n : Nat} (matrix : Vector Float (n * n)) : 
    ∀ i : Fin n, (diag matrix).get i = matrix.get ⟨i.val * n + i.val, by exact diag_index_in_bounds i⟩ := by
  intro i
  simp [diag, Vector.get_ofFn]
-- </vc-theorems>
