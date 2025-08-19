import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def reverseVector {α : Type} {n : Nat} (v : Vector α n) : Vector α n :=
  Vector.mk v.toList.reverse (by simp [List.length_reverse])

/-- Reverses the order of columns in a 2D matrix (left/right flip).
    For a matrix with shape (rows × cols), this operation reverses the order 
    of elements along each row, effectively flipping the matrix horizontally. -/
def fliplr {rows cols : Nat} (m : Vector (Vector Float cols) rows) : Id (Vector (Vector Float cols) rows) :=
  return Vector.mk (List.map (fun row => reverseVector row) m.toList) (by simp [List.length_map])

-- LLM HELPER
lemma list_reverse_get {α : Type} (l : List α) (i : Fin l.length) :
    l.reverse.get ⟨l.length - 1 - i.val, by
      simp [List.length_reverse]
      have : i.val < l.length := i.isLt
      omega⟩ = l.get i := by
  rw [List.get_reverse]
  simp

-- LLM HELPER
lemma vector_reverse_get {α : Type} {n : Nat} (v : Vector α n) (i : Fin n) :
    (reverseVector v).get i = v.get ⟨n - 1 - i.val, by
      have : i.val < n := i.isLt
      omega⟩ := by
  unfold reverseVector
  simp [Vector.get_mk]
  rw [list_reverse_get]
  simp [Vector.get_eq_get]

-- LLM HELPER
lemma vector_reverse_preserves_elements {α : Type} {n : Nat} (v : Vector α n) (x : α) :
    (∃ i : Fin n, v.get i = x) ↔ (∃ i : Fin n, (reverseVector v).get i = x) := by
  constructor
  · intro ⟨i, hi⟩
    use ⟨n - 1 - i.val, by
      have : i.val < n := i.isLt
      omega⟩
    rw [vector_reverse_get]
    simp
    exact hi
  · intro ⟨i, hi⟩
    use ⟨n - 1 - i.val, by
      have : i.val < n := i.isLt
      omega⟩
    rw [← hi, vector_reverse_get]
    simp

/-- Specification: fliplr reverses the column order in each row of the matrix.
    The element at position (i, j) in the input matrix appears at position 
    (i, cols-1-j) in the output matrix. This captures the mathematical property
    that columns are reversed while rows remain in the same order.
    
    Sanity checks:
    1. The output has the same dimensions as the input (enforced by type)
    2. Each row contains the same elements, just in reversed order
    3. For matrices with odd number of columns, the middle column stays in place
    
    Mathematical properties:
    1. Element mapping: For all valid indices i and j, there exists a corresponding
       index j' such that output[i,j] = input[i,j'] where j' = cols-1-j
    2. Row preservation: Each row contains exactly the same elements as the input
    3. Column reversal: The first column becomes the last, second becomes second-to-last, etc. -/
theorem fliplr_spec {rows : Nat} {cols : Nat} (m : Vector (Vector Float (cols + 1)) rows) :
    ⦃⌜True⌝⦄
    fliplr m
    ⦃⇓result => ⌜(∀ i : Fin rows, ∀ j : Fin (cols + 1), 
                   ∃ k : Fin (cols + 1), 
                   (result.get i).get j = (m.get i).get k ∧ 
                   j.val + k.val = cols) ∧
                 (∀ i : Fin rows, 
                   (∀ x : Float, (∃ j : Fin (cols + 1), (m.get i).get j = x) ↔ 
                                 (∃ j : Fin (cols + 1), (result.get i).get j = x))) ∧
                 (cols % 2 = 0 → 
                   ∀ i : Fin rows, 
                   ∃ mid : Fin (cols + 1),
                   2 * mid.val = cols ∧
                   (result.get i).get mid = (m.get i).get mid)⌝⦄ := by
  intro h
  use Vector.mk (List.map (fun row => reverseVector row) m.toList) (by simp [List.length_map])
  constructor
  · simp [fliplr]
  · constructor
    · intro i j
      use ⟨cols - j.val, by
        have : j.val < cols + 1 := j.isLt
        omega⟩
      constructor
      · simp [Vector.get_mk]
        rw [List.get_map]
        rw [vector_reverse_get]
        simp
      · omega
    · constructor
      · intro i x
        simp [Vector.get_mk]
        rw [List.get_map]
        exact vector_reverse_preserves_elements _ _
      · intro h_even i
        use ⟨cols / 2, by
          have : cols % 2 = 0 := h_even
          have : cols / 2 * 2 = cols := Nat.div_mul_cancel (Nat.dvd_iff_mod_eq_zero.mpr h_even)
          omega⟩
        constructor
        · rw [Nat.mul_div_cancel_left]
          exact Nat.dvd_iff_mod_eq_zero.mpr h_even
        · simp [Vector.get_mk]
          rw [List.get_map]
          rw [vector_reverse_get]
          simp
          have : cols / 2 + cols / 2 = cols := by
            rw [← Nat.two_mul]
            rw [Nat.mul_div_cancel_left]
            exact Nat.dvd_iff_mod_eq_zero.mpr h_even
          omega