import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.tril",
  "category": "Building matrices",
  "description": "Lower triangle of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.tril.html",
  "doc": "\nLower triangle of an array.\n\nReturn a copy of an array with elements above the k-th diagonal zeroed. For arrays with \nndim exceeding 2, tril will apply to the final two axes.\n\nParameters\n----------\nm : array_like, shape (..., M, N)\n    Input array.\nk : int, optional\n    Diagonal above which to zero elements. k = 0 (the default) is the main diagonal, \n    k < 0 is below it and k > 0 is above.\n\nReturns\n-------\ntril : ndarray, shape (..., M, N)\n    Lower triangle of m, of same shape and data-type as m.\n\nExamples\n--------\n>>> np.tril([[1,2,3],[4,5,6],[7,8,9],[10,11,12]], -1)\narray([[ 0,  0,  0],\n       [ 4,  0,  0],\n       [ 7,  8,  0],\n       [10, 11, 12]])\n\n>>> np.tril(np.arange(3*4*5).reshape(3, 4, 5))[:,:,::2]\narray([[[ 0,  0,  0],\n        [ 5,  0,  0],\n        [10, 11,  0],\n        [15, 16, 17]],\n       [[20,  0,  0],\n        [25, 26,  0],\n        [30, 31, 32],\n        [35, 36, 37]],\n       [[40,  0,  0],\n        [45, 46,  0],\n        [50, 51, 52],\n        [55, 56, 57]]])\n",
  "code": "@array_function_dispatch(_trilu_dispatcher)\ndef tril(m, k=0):\n    \"\"\"\n    Lower triangle of an array.\n\n    Return a copy of the array with elements above the \`k\`-th diagonal zeroed.\n    For arrays with \`\`ndim\`\` exceeding 2, \`tril\` will apply to the final two\n    axes.\n    \"\"\"\n    m = asanyarray(m)\n    mask = tri(*m.shape[-2:], k=k, dtype=bool)\n\n    return where(mask, m, zeros(1, m.dtype))",
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
  Id.pure (Vector.ofFn fun i => Vector.ofFn fun j => 
    if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0)

-- LLM HELPER
lemma tril_element_spec {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) 
    (i : Fin rows) (j : Fin cols) :
    ((tril m k).get i).get j = if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0 := by
  simp [tril, Vector.get_ofFn]

-- LLM HELPER
lemma tril_idempotent {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    tril (tril m k) k = tril m k := by
  ext i j
  simp [tril, Vector.get_ofFn]
  split_ifs with h
  · simp [tril_element_spec, h]
  · simp [tril_element_spec, h]

-- LLM HELPER
lemma diagonal_preserved {rows cols : Nat} (m : Vector (Vector Float cols) rows) 
    (i : Fin (min rows cols)) :
    let hi : i < rows := Nat.lt_of_lt_min_left i.isLt
    let hj : i < cols := Nat.lt_of_lt_min_right i.isLt
    ((tril m 0).get ⟨i, hi⟩).get ⟨i, hj⟩ = (m.get ⟨i, hi⟩).get ⟨i, hj⟩ := by
  simp [tril, Vector.get_ofFn]
  simp [Int.sub_zero, le_refl]

-- LLM HELPER
lemma all_preserved_large_k {rows cols : Nat} (m : Vector (Vector Float cols) rows) 
    (k : Int) (hk : k ≥ (cols : Int)) (i : Fin rows) (j : Fin cols) :
    ((tril m k).get i).get j = (m.get i).get j := by
  simp [tril, Vector.get_ofFn]
  simp only [ite_eq_left_iff, not_le]
  intro h
  have : (j : Int) - k ≤ (j : Int) - (cols : Int) := Int.sub_le_sub_left hk _
  have : (j : Int) - (cols : Int) < (j : Int) := by
    simp [Int.sub_lt_iff_lt_add]
    norm_cast
    exact Nat.zero_lt_succ _
  have : (j : Int) - k < (j : Int) := lt_of_le_of_lt this ‹(j : Int) - (cols : Int) < (j : Int)›
  have : (j : Int) - k ≤ (cols : Int) - 1 := by
    rw [Int.sub_le_iff_le_add]
    have : (j : Int) < (cols : Int) := by norm_cast; exact j.isLt
    linarith
  have : (i : Int) ≥ 0 := by norm_cast; exact Nat.zero_le _
  have : (j : Int) - k ≤ (cols : Int) - 1 := by
    rw [Int.sub_le_iff_le_add]
    have : (j : Int) < (cols : Int) := by norm_cast; exact j.isLt
    linarith
  have : (i : Int) < (rows : Int) := by norm_cast; exact i.isLt
  have bound : (j : Int) - k ≤ (rows : Int) - 1 := by
    trans (cols : Int) - 1
    · exact this
    · norm_cast; simp
  linarith [bound]

-- LLM HELPER
lemma all_zeroed_small_k {rows cols : Nat} (m : Vector (Vector Float cols) rows) 
    (k : Int) (hk : k ≤ -(rows : Int)) (i : Fin rows) (j : Fin cols) :
    ((tril m k).get i).get j = 0 := by
  simp [tril, Vector.get_ofFn]
  simp only [ite_eq_right_iff, not_ge]
  intro h
  exfalso
  have : (i : Int) < (rows : Int) := by norm_cast; exact i.isLt
  have : (j : Int) ≥ 0 := by norm_cast; exact Nat.zero_le _
  have : (j : Int) - k ≥ (j : Int) - (-(rows : Int)) := Int.sub_le_sub_left (le_neg_of_le_neg hk) _
  have : (j : Int) - (-(rows : Int)) = (j : Int) + (rows : Int) := by ring
  rw [this] at *
  have : (j : Int) + (rows : Int) ≥ (rows : Int) := by linarith
  linarith

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
  simp [wpure_spec]
  constructor
  · exact tril_element_spec m k
  constructor
  · intro hk i
    have hi : i < rows := Nat.lt_of_lt_min_left i.isLt
    have hj : i < cols := Nat.lt_of_lt_min_right i.isLt
    rw [hk]
    exact diagonal_preserved m i
  constructor
  · exact all_preserved_large_k m k
  constructor
  · exact all_zeroed_small_k m k
  · intro i j
    have h := tril_idempotent m k
    rw [← Vector.ext_get_iff] at h
    have h' := h i
    rw [← Vector.ext_get_iff] at h'
    exact h' j