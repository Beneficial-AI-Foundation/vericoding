import Std.Do.Triple
import Std.Tactic.Do

/-!
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
  do
    pure (Vector.ofFn (fun i => Vector.ofFn (fun j => 
      if (i : Int) ≥ (j : Int) - k then (m.get i).get j else 0)))

-- LLM HELPER
lemma min_lt_left {a b : Nat} {i : Nat} (h : i < min a b) : i < a := by
  cases' Nat.lt_min_iff.mp h with h1 h2
  exact h1

-- LLM HELPER
lemma min_lt_right {a b : Nat} {i : Nat} (h : i < min a b) : i < b := by
  cases' Nat.lt_min_iff.mp h with h1 h2
  exact h2

-- LLM HELPER
lemma vector_get_ofFn {n : Nat} {α : Type*} (f : Fin n → α) (i : Fin n) : 
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get_ofFn]

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
                    have hi : i < rows := min_lt_left (Fin.val_lt_of_le (le_refl _))
                    have hj : i < cols := min_lt_right (Fin.val_lt_of_le (le_refl _))
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
  simp [tril, Id.run]
  constructor
  · -- Element-wise specification
    intros i j
    simp [vector_get_ofFn]
  constructor
  · -- Diagonal elements preserved when k = 0
    intros h i
    have hi : i < rows := min_lt_left (Fin.val_lt_of_le (le_refl _))
    have hj : i < cols := min_lt_right (Fin.val_lt_of_le (le_refl _))
    simp [vector_get_ofFn, h]
    norm_cast
    simp
  constructor
  · -- All elements preserved when k is very large
    intros h i j
    simp [vector_get_ofFn]
    have : (i : Int) ≥ (j : Int) - k := by
      have : (j : Int) - k ≤ (j : Int) - (cols : Int) := by
        simp [Int.sub_le_sub_iff_left]
        exact h
      have : (j : Int) - (cols : Int) ≤ (i : Int) := by
        simp [Int.sub_le_iff_le_add]
        have : (j : Int) ≤ (cols : Int) - 1 := by
          simp [Int.coe_nat_le_coe_nat_iff]
          exact Nat.le_sub_of_add_le (Nat.succ_le_of_lt j.isLt)
        have : (j : Int) + 1 ≤ (cols : Int) := by
          rw [Int.add_le_iff_le_sub]
          exact this
        have : 0 ≤ (i : Int) := Int.coe_nat_nonneg _
        linarith
      linarith
    simp [if_pos this]
  constructor
  · -- All elements zeroed when k is very negative
    intros h i j
    simp [vector_get_ofFn]
    have : (i : Int) < (j : Int) - k := by
      have : (i : Int) < (rows : Int) := by
        simp [Int.coe_nat_lt_coe_nat_iff]
        exact i.isLt
      have : (j : Int) - k ≥ (j : Int) - (-(rows : Int)) := by
        simp [Int.sub_le_sub_iff_left, Int.neg_le_iff_add_nonneg]
        exact Int.add_nonneg (Int.coe_nat_nonneg _) (Int.coe_nat_nonneg _)
      have : (j : Int) + (rows : Int) ≥ 0 := by
        exact Int.add_nonneg (Int.coe_nat_nonneg _) (Int.coe_nat_nonneg _)
      have : (j : Int) - (-(rows : Int)) = (j : Int) + (rows : Int) := by simp
      rw [this] at *
      have : (rows : Int) > (i : Int) := by
        simp [Int.coe_nat_lt_coe_nat_iff]
        exact i.isLt
      linarith
    simp [if_neg (not_le.mpr this)]
  · -- Idempotency
    intros i j
    simp [tril, Id.run, vector_get_ofFn]
    by_cases h : (i : Int) ≥ (j : Int) - k
    · simp [if_pos h]
    · simp [if_neg h]