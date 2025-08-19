import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def get_minor {n : Nat} (a : Vector (Vector Float n) n) (skip_row : Fin n) (skip_col : Fin n) : Vector (Vector Float (n-1)) (n-1) :=
  if n > 0 then
    let rows := Vector.ofFn (fun i : Fin (n-1) => 
      let actual_i := if i.val < skip_row.val then i.val else i.val + 1
      if hai : actual_i < n then
        Vector.ofFn (fun j : Fin (n-1) => 
          let actual_j := if j.val < skip_col.val then j.val else j.val + 1
          if haj : actual_j < n then
            (a.get ⟨actual_i, hai⟩).get ⟨actual_j, haj⟩
          else 0
        )
      else Vector.replicate (n-1) 0
    )
    rows
  else Vector.replicate (n-1) (Vector.replicate (n-1) 0)

-- LLM HELPER
def det_aux {n : Nat} (a : Vector (Vector Float n) n) : Float :=
  match n with
  | 0 => 1
  | 1 => 
    have h : 0 < 1 := by norm_num
    (a.get ⟨0, h⟩).get ⟨0, h⟩
  | 2 => 
    have h : 0 < 2 := by norm_num
    have h1 : 1 < 2 := by norm_num
    (a.get ⟨0, h⟩).get ⟨0, h⟩ * (a.get ⟨1, h1⟩).get ⟨1, h1⟩ - 
    (a.get ⟨0, h⟩).get ⟨1, h1⟩ * (a.get ⟨1, h1⟩).get ⟨0, h⟩
  | k + 3 => 
    -- For larger matrices, use cofactor expansion along first row
    let rec cofactor_expansion (j : Fin (k + 3)) : Float :=
      if j.val < k + 3 then
        let sign := if j.val % 2 = 0 then 1 else -1
        have h : 0 < k + 3 := Nat.zero_lt_succ _
        let element := (a.get ⟨0, h⟩).get j
        sign * element * det_aux (get_minor a ⟨0, h⟩ j)
      else 0
    -- Sum over all columns
    (List.range (k + 3)).foldl (fun acc j => 
      if hj : j < k + 3 then
        acc + cofactor_expansion ⟨j, hj⟩
      else acc
    ) 0

/-- Compute the determinant of a square matrix -/
def det {n : Nat} (a : Vector (Vector Float n) n) : Id Float :=
  pure (det_aux a)

/-- Specification: det computes the determinant of a square matrix.
    The determinant satisfies fundamental mathematical properties including:
    - Explicit formulas for small matrices
    - Multilinear properties
    - Behavior under elementary row operations -/
theorem det_spec {n : Nat} (a : Vector (Vector Float n) n) :
    ⦃⌜True⌝⦄
    det a
    ⦃⇓result => ⌜
      -- The determinant of the identity matrix is 1
      ((∀ i j : Fin n, (a.get i).get j = if i = j then 1 else 0) → result = 1) ∧
      -- If a row is all zeros, the determinant is 0
      ((∃ i : Fin n, ∀ j : Fin n, (a.get i).get j = 0) → result = 0) ∧
      -- If two rows are equal, the determinant is 0
      ((∃ i j : Fin n, i ≠ j ∧ (∀ k : Fin n, (a.get i).get k = (a.get j).get k)) → result = 0) ∧
      -- For 1x1 matrices, the determinant is the single element
      ((n = 1) → ∃ h : 0 < n, result = (a.get ⟨0, h⟩).get ⟨0, h⟩) ∧
      -- For 2x2 matrices, the determinant is ad - bc
      ((n = 2) → ∃ h : 0 < n, ∃ h1 : 1 < n, 
        result = (a.get ⟨0, h⟩).get ⟨0, h⟩ * (a.get ⟨1, h1⟩).get ⟨1, h1⟩ - 
                 (a.get ⟨0, h⟩).get ⟨1, h1⟩ * (a.get ⟨1, h1⟩).get ⟨0, h⟩) ∧
      -- For empty matrices (n = 0), the determinant is 1 by convention
      ((n = 0) → result = 1) ∧
      -- If a column is all zeros, the determinant is 0
      ((∃ j : Fin n, ∀ i : Fin n, (a.get i).get j = 0) → result = 0) ∧
      -- If two columns are equal, the determinant is 0
      ((∃ j k : Fin n, j ≠ k ∧ (∀ i : Fin n, (a.get i).get j = (a.get i).get k)) → result = 0) ∧
      -- The determinant is alternating: swapping rows changes sign
      -- The determinant is linear in each row
      (True) -- Placeholder for more advanced multilinear properties
    ⌝⦄ := by
  simp [det, det_aux]
  constructor
  · -- Identity matrix case
    intro h_id
    cases' n with n
    · simp
    · cases' n with n
      · simp
        rw [h_id]
        simp
      · cases' n with n
        · simp
          rw [h_id]
          simp
        · simp
  constructor
  · -- Row of zeros case
    intro h_row_zero
    cases' n with n
    · simp
    · cases' n with n
      · simp
        obtain ⟨i, hi⟩ := h_row_zero
        fin_cases i
        simp at hi
        rw [hi]
        simp
      · cases' n with n
        · simp
          obtain ⟨i, hi⟩ := h_row_zero
          fin_cases i
          · simp at hi
            rw [hi]
            simp
          · simp at hi
            rw [hi]
            simp
        · simp
  constructor
  · -- Equal rows case
    intro h_equal_rows
    cases' n with n
    · simp
    · cases' n with n
      · simp
        obtain ⟨i, j, hij, _⟩ := h_equal_rows
        fin_cases i <;> fin_cases j <;> contradiction
      · cases' n with n
        · simp
          obtain ⟨i, j, hij, h_eq⟩ := h_equal_rows
          fin_cases i <;> fin_cases j <;> try contradiction
          · simp at h_eq
            rw [h_eq]
            simp
        · simp
  constructor
  · -- 1x1 case
    intro h_n1
    simp [h_n1]
    use Nat.one_pos
    rfl
  constructor
  · -- 2x2 case
    intro h_n2
    simp [h_n2]
    use Nat.one_pos, Nat.one_lt_two
    rfl
  constructor
  · -- Empty matrix case
    intro h_n0
    simp [h_n0]
  constructor
  · -- Column of zeros case
    intro h_col_zero
    cases' n with n
    · simp
    · cases' n with n
      · simp
        obtain ⟨j, hj⟩ := h_col_zero
        fin_cases j
        simp at hj
        rw [hj]
        simp
      · cases' n with n
        · simp
          obtain ⟨j, hj⟩ := h_col_zero
          fin_cases j
          · simp at hj
            rw [hj]
            simp
          · simp at hj
            rw [hj]
            simp
        · simp
  constructor
  · -- Equal columns case
    intro h_equal_cols
    cases' n with n
    · simp
    · cases' n with n
      · simp
        obtain ⟨j, k, hjk, _⟩ := h_equal_cols
        fin_cases j <;> fin_cases k <;> contradiction
      · cases' n with n
        · simp
          obtain ⟨j, k, hjk, h_eq⟩ := h_equal_cols
          fin_cases j <;> fin_cases k <;> try contradiction
          · simp at h_eq
            rw [h_eq]
            simp
        · simp
  · -- Placeholder for advanced properties
    trivial