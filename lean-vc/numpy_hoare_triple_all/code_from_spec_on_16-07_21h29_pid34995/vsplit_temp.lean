import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def splitRows {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (split_idx : Fin k) (h_div : k > 0 ∧ rows % k = 0) : Vector (Vector Float cols) (rows / k) :=
  let chunk_size := rows / k
  Vector.ofFn (fun row_idx => 
    let global_row_idx := split_idx.val * chunk_size + row_idx.val
    have h_bound : global_row_idx < rows := by
      have h_k_pos : k > 0 := h_div.1
      have h_mod : rows % k = 0 := h_div.2
      have h_div_eq : rows = k * (rows / k) := by
        rw [Nat.mul_div_cancel']
        exact Nat.dvd_iff_mod_eq_zero.mpr h_mod
      rw [h_div_eq]
      have h_split_bound : split_idx.val < k := split_idx.isLt
      have h_row_bound : row_idx.val < rows / k := row_idx.isLt
      rw [Nat.mul_comm k (rows / k)]
      calc global_row_idx 
        = split_idx.val * chunk_size + row_idx.val := rfl
        _ < split_idx.val * chunk_size + chunk_size := by
          simp [chunk_size]; exact Nat.add_lt_add_left h_row_bound _
        _ = (split_idx.val + 1) * chunk_size := by ring
        _ ≤ k * chunk_size := by
          apply Nat.mul_le_mul_right
          exact Nat.succ_le_of_lt h_split_bound
        _ = rows / k * k := by simp [chunk_size]
        _ = rows := by
          rw [Nat.mul_comm (rows / k) k]
          rw [Nat.mul_div_cancel']
          exact Nat.dvd_iff_mod_eq_zero.mpr h_mod
    mat.get ⟨global_row_idx, h_bound⟩)

/-- Split a 2D vector into multiple sub-vectors vertically (row-wise).
    This is a simplified version that handles splitting into equal parts. -/
def vsplit {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (h_div : k > 0 ∧ rows % k = 0) : Id (Vector (Vector (Vector Float cols) (rows / k)) k) :=
  pure (Vector.ofFn (fun split_idx => splitRows mat split_idx h_div))

-- LLM HELPER
lemma splitRows_size {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (split_idx : Fin k) (h_div : k > 0 ∧ rows % k = 0) :
    (splitRows mat split_idx h_div).size = rows / k := by
  unfold splitRows
  simp [Vector.size_ofFn]

-- LLM HELPER
lemma splitRows_get {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (split_idx : Fin k) (h_div : k > 0 ∧ rows % k = 0) 
    (row_idx : Fin (rows / k)) (col_idx : Fin cols) :
    ∃ (global_row : Fin rows), 
      global_row.val = split_idx.val * (rows / k) + row_idx.val ∧
      ((splitRows mat split_idx h_div).get row_idx).get col_idx = 
      (mat.get global_row).get col_idx := by
  unfold splitRows
  simp [Vector.get_ofFn]
  let global_row_idx := split_idx.val * (rows / k) + row_idx.val
  have h_bound : global_row_idx < rows := by
    have h_k_pos : k > 0 := h_div.1
    have h_mod : rows % k = 0 := h_div.2
    have h_div_eq : rows = k * (rows / k) := by
      rw [Nat.mul_div_cancel']
      exact Nat.dvd_iff_mod_eq_zero.mpr h_mod
    rw [h_div_eq]
    have h_split_bound : split_idx.val < k := split_idx.isLt
    have h_row_bound : row_idx.val < rows / k := row_idx.isLt
    rw [Nat.mul_comm k (rows / k)]
    calc global_row_idx 
      = split_idx.val * (rows / k) + row_idx.val := rfl
      _ < split_idx.val * (rows / k) + (rows / k) := by
        exact Nat.add_lt_add_left h_row_bound _
      _ = (split_idx.val + 1) * (rows / k) := by ring
      _ ≤ k * (rows / k) := by
        apply Nat.mul_le_mul_right
        exact Nat.succ_le_of_lt h_split_bound
  use ⟨global_row_idx, h_bound⟩
  constructor
  · rfl
  · rfl

-- LLM HELPER
lemma partition_property {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (h_div : k > 0 ∧ rows % k = 0) (orig_row : Fin rows) :
    ∃ split_idx : Fin k, ∃ row_idx : Fin (rows / k),
      orig_row.val = split_idx.val * (rows / k) + row_idx.val := by
  have h_k_pos : k > 0 := h_div.1
  have h_mod : rows % k = 0 := h_div.2
  have h_div_eq : rows = k * (rows / k) := by
    rw [Nat.mul_div_cancel']
    exact Nat.dvd_iff_mod_eq_zero.mpr h_mod
  let chunk_size := rows / k
  have h_chunk_pos : chunk_size > 0 := by
    have h_rows_pos : rows > 0 := by
      by_contra h_neg
      push_neg at h_neg
      have h_rows_zero : rows = 0 := Nat.eq_zero_of_le_zero h_neg
      rw [h_rows_zero] at orig_row
      exact Nat.not_lt_zero orig_row.val orig_row.isLt
    exact Nat.div_pos (Nat.le_refl rows) h_k_pos
  let split_idx_val := orig_row.val / chunk_size
  let row_idx_val := orig_row.val % chunk_size
  have h_split_bound : split_idx_val < k := by
    exact Nat.div_lt_iff_lt_mul_right h_chunk_pos ▸ (h_div_eq ▸ orig_row.isLt)
  have h_row_bound : row_idx_val < chunk_size := Nat.mod_lt _ h_chunk_pos
  use ⟨split_idx_val, h_split_bound⟩, ⟨row_idx_val, h_row_bound⟩
  exact Nat.div_add_mod orig_row.val chunk_size

/-- Specification: vsplit divides a matrix into k equal parts row-wise, 
    where each part contains consecutive rows from the original matrix -/
theorem vsplit_spec {rows cols k : Nat} (mat : Vector (Vector Float cols) rows) 
    (h_div : k > 0 ∧ rows % k = 0) :
    ⦃⌜k > 0 ∧ rows % k = 0⌝⦄
    vsplit mat h_div
    ⦃⇓result => ⌜(∀ split_idx : Fin k, (result.get split_idx).size = rows / k) ∧
                 (∀ split_idx : Fin k, ∀ row_idx : Fin (rows / k), ∀ col_idx : Fin cols,
                   ∃ (global_row : Fin rows), 
                     global_row.val = split_idx.val * (rows / k) + row_idx.val ∧
                     ((result.get split_idx).get row_idx).get col_idx = 
                     (mat.get global_row).get col_idx) ∧
                 (∀ orig_row : Fin rows, ∃ split_idx : Fin k, ∃ row_idx : Fin (rows / k),
                   orig_row.val = split_idx.val * (rows / k) + row_idx.val)⌝⦄ := by
  apply Triple.pure
  intro h_pre
  unfold vsplit
  simp [Vector.get_ofFn]
  constructor
  · intro split_idx
    exact splitRows_size mat split_idx h_div
  · constructor
    · intros split_idx row_idx col_idx
      exact splitRows_get mat split_idx h_div row_idx col_idx
    · intro orig_row
      exact partition_property mat h_div orig_row