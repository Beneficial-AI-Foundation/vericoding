import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.tril",
  "category": "Building matrices",
  "description": "Lower triangle of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.tril.html",
  "doc": "\nLower triangle of an array.\n\nReturn a copy of an array with elements above the k-th diagonal zeroed. For arrays with \nndim exceeding 2, tril will apply to the final two axes.\n\nParameters\n----------\nm : array_like, shape (..., M, N)\n    Input array.\nk : int, optional\n    Diagonal above which to zero elements. k = 0 (the default) is the main diagonal, \n    k < 0 is below it and k > 0 is above.\n\nReturns\n-------\ntril : ndarray, shape (..., M, N)\n    Lower triangle of m, of same shape and data-type as m.\n\nExamples\n--------\n>>> np.tril([[1,2,3],[4,5,6],[7,8,9],[10,11,12]], -1)\narray([[ 0,  0,  0],\n       [ 4,  0,  0],\n       [ 7,  8,  0],\n       [10, 11, 12]])\n\n>>> np.tril(np.arange(3*4*5).reshape(3, 4, 5))[:,:,::2]\narray([[[ 0,  0,  0],\n        [ 5,  0,  0],\n        [10, 11,  0],\n        [15, 16, 17]],\n       [[20,  0,  0],\n        [25, 26,  0],\n        [30, 31, 32],\n        [35, 36, 37]],\n       [[40,  0,  0],\n        [45, 46,  0],\n        [50, 51, 52],\n        [55, 56, 57]]])\n",
  "code": "@array_function_dispatch(_trilu_dispatcher)\ndef tril(m, k=0):\n    \"\"\"\n    Lower triangle of an array.\n\n    Return a copy of an array with elements above the \`k\`-th diagonal zeroed.\n    For arrays with \`\`ndim\`\` exceeding 2, \`tril\` will apply to the final two\n    axes.\n    \"\"\"\n    m = asanyarray(m)\n    mask = tri(*m.shape[-2:], k=k, dtype=bool)\n\n    return where(mask, m, zeros(1, m.dtype))",
  "signature": "numpy.tril(m, k=0)"
}
-/

open Std.Do

/-- numpy.tril: Lower triangle of a matrix.

    Returns a copy of the input matrix with elements above the k-th diagonal zeroed.
    
    - k = 0 (default): zeros elements above the main diagonal
    - k < 0: zeros elements above the k-th diagonal below the main diagonal
    - k > 0: zeros elements above the k-th diagonal above the main diagonal
    
    For a matrix element at position (i, j):
    - It is kept if i >= j - k
    - It is zeroed if i < j - k
-/
def tril {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) : 
    Id (Vector (Vector Float cols) rows) :=
  Vector.map (fun i => 
    Vector.map (fun j => 
      if (i : Int) ≥ (j : Int) - k then j else 0) (Fin.range cols)) 
    (Vector.zip (Fin.range rows) m |>.map Prod.snd)

-- LLM HELPER
lemma Vector.get_map {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  sorry

-- LLM HELPER
lemma Vector.zip_map_snd {α β : Type} {n : Nat} (v1 : Vector α n) (v2 : Vector β n) :
  (Vector.zip v1 v2 |>.map Prod.snd) = v2 := by
  sorry

-- LLM HELPER
lemma Fin.range_get {n : Nat} (i : Fin n) :
  (Fin.range n).get i = i := by
  sorry

/-- Specification: tril returns a lower triangular matrix by zeroing elements above the k-th diagonal.
    
    Mathematical Properties:
    1. Shape preservation: The output matrix has the same dimensions as the input
    2. Lower triangle preservation: Elements on or below the k-th diagonal are unchanged
    3. Upper triangle zeroing: Elements above the k-th diagonal are set to zero
    4. Diagonal selection: The k parameter controls which diagonal forms the boundary
       - k = 0: main diagonal (default)
       - k < 0: diagonal below the main diagonal
       - k > 0: diagonal above the main diagonal
    5. Idempotency: Applying tril twice with the same k yields the same result
    
    Element-wise specification:
    For each element at position (i, j):
    - If i ≥ j - k (on or below the k-th diagonal), the element is preserved
    - If i < j - k (above the k-th diagonal), the element is set to 0
    
    Special cases:
    - k ≥ cols: All elements are preserved (entire matrix is "lower triangular")
    - k ≤ -rows: All elements are zeroed (no elements are "on or below" such a diagonal)
-/
theorem tril_spec {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) :
    ⦃⌜True⌝⦄
    tril m k
    ⦃⇓result => ⌜-- Element-wise specification (core property)
                  (∀ (i : Fin rows) (j : Fin cols), 
                    (result.get i).get j = 
                      if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0) ∧
                  -- Sanity check: diagonal elements are preserved when k = 0
                  (k = 0 → ∀ i : Fin (min rows cols), 
                    have hi : i < rows := by sorry
                    have hj : i < cols := by sorry
                    (result.get ⟨i, hi⟩).get ⟨i, hj⟩ = (m.get ⟨i, hi⟩).get ⟨i, hj⟩) ∧
                  -- Sanity check: all elements preserved when k is very large
                  (k ≥ (cols : Int) → ∀ (i : Fin rows) (j : Fin cols), 
                    (result.get i).get j = (m.get i).get j) ∧
                  -- Sanity check: all elements zeroed when k is very negative
                  (k ≤ -(rows : Int) → ∀ (i : Fin rows) (j : Fin cols), 
                    (result.get i).get j = 0) ∧
                  -- Idempotency property: tril(tril(m, k), k) = tril(m, k)
                  (∀ (i : Fin rows) (j : Fin cols),
                    let twice_applied := tril result k
                    (twice_applied.get i).get j = (result.get i).get j)⌝⦄ := by
  simp only [Std.Do.Triple.pure_triple]
  constructor
  · trivial
  · constructor
    · intro i j
      simp [tril]
      rw [Vector.get_map, Vector.get_map]
      simp [Vector.zip_map_snd, Fin.range_get]
    · constructor
      · intro hk i
        have hi : i < rows := by sorry
        have hj : i < cols := by sorry
        simp [tril]
        rw [Vector.get_map, Vector.get_map]
        simp [Vector.zip_map_snd, Fin.range_get]
        simp [hk]
        simp [Int.sub_zero, Int.le_refl]
      · constructor
        · intro hk i j
          simp [tril]
          rw [Vector.get_map, Vector.get_map]
          simp [Vector.zip_map_snd, Fin.range_get]
          simp only [if_pos]
          · rfl
          · have : (i : Int) ≥ 0 := Int.coe_nat_nonneg i
            have : (j : Int) < cols := Int.coe_nat_pos.mpr j.pos
            have : (j : Int) ≤ cols - 1 := by
              rw [Int.sub_one_lt_iff]
              exact Int.coe_nat_pos.mpr j.pos
            have : (j : Int) - k ≤ j := Int.sub_le_self _ (Int.le_of_coe_nat_le_coe_nat (Int.coe_nat_nonneg k))
            sorry
        · constructor
          · intro hk i j
            simp [tril]
            rw [Vector.get_map, Vector.get_map]
            simp [Vector.zip_map_snd, Fin.range_get]
            simp only [if_neg]
            · rfl
            · have : (i : Int) < rows := Int.coe_nat_pos.mpr i.pos
              have : (j : Int) ≥ 0 := Int.coe_nat_nonneg j
              have : (j : Int) - k ≥ j - (-(rows : Int)) := by
                simp [Int.sub_neg_eq_add]
                have : (j : Int) + rows ≥ j := by
                  rw [Int.add_comm]
                  exact Int.le_add_of_nonneg_right (Int.coe_nat_nonneg rows)
                exact this
              have : (j : Int) - k ≥ j + rows := by
                rw [Int.sub_le_iff_le_add] at hk
                sorry
              have : (i : Int) < j + rows := by
                calc (i : Int) 
                  _ < rows := Int.coe_nat_pos.mpr i.pos
                  _ ≤ j + rows := Int.le_add_of_nonneg_left (Int.coe_nat_nonneg j)
              sorry
          · intro i j
            simp [tril]
            rw [Vector.get_map, Vector.get_map]
            simp [Vector.zip_map_snd, Fin.range_get]
            split
            · simp [tril]
              rw [Vector.get_map, Vector.get_map]
              simp [Vector.zip_map_snd, Fin.range_get]
              simp only [if_pos]
              · rfl
              · assumption
            · simp [tril]
              rw [Vector.get_map, Vector.get_map]
              simp [Vector.zip_map_snd, Fin.range_get]
              simp only [if_neg]
              · rfl
              · assumption