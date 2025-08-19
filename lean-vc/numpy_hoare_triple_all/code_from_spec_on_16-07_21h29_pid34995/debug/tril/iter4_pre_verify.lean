import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.tril",
  "category": "Diagonal operations",
  "description": "Lower triangle of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.tril.html",
  "doc": "Lower triangle of an array.\n\nReturn a copy of an array with elements above the \`k\`-th diagonal zeroed. For arrays with \`\`ndim\`\` exceeding 2, \`tril\` will apply to the final two axes.\n\nParameters\n----------\nm : array_like, shape (..., M, N)\n    Input array.\nk : int, optional\n    Diagonal above which to zero elements. \`k = 0\` (the default) is the main diagonal, \`k < 0\` is below it and \`k > 0\` is above.\n\nReturns\n-------\ntril : ndarray, shape (..., M, N)\n    Lower triangle of \`m\`, of same shape and data-type as \`m\`.",
  "code": "@array_function_dispatch(_trilu_dispatcher)\ndef tril(m, k=0):\n    \"\"\"\n    Lower triangle of an array.\n\n    Return a copy of an array with elements above the \`k\`-th diagonal zeroed.\n    For arrays with \`\`ndim\`\` exceeding 2, \`tril\` will apply to the final two\n    axes.\n\n    Parameters\n    ----------\n    m : array_like, shape (..., M, N)\n        Input array.\n    k : int, optional\n        Diagonal above which to zero elements.  \`k = 0\` (the default) is the\n        main diagonal, \`k < 0\` is below it and \`k > 0\` is above.\n\n    Returns\n    -------\n    tril : ndarray, shape (..., M, N)\n        Lower triangle of \`m\`, of same shape and data-type as \`m\`.\n    \"\"\"\n    m = asanyarray(m)\n    mask = tri(*m.shape[-2:], k=k, dtype=bool)\n\n    return where(mask, m, zeros(1, m.dtype))"
}
-/

/-- numpy.tril: Lower triangle of an array.
    
    Return a copy of an array with elements above the k-th diagonal zeroed.
    For simplicity, this specification focuses on square matrices and k=0 (main diagonal).
    
    Given a flattened square matrix (stored in row-major order), returns a copy
    where elements above the main diagonal are set to zero.
    
    This captures the essential mathematical property of extracting the lower
    triangular part of a matrix.
-/
def tril {n : Nat} (matrix : Vector Float (n * n)) : Id (Vector Float (n * n)) :=
  pure (Vector.ofFn (fun idx => 
    let i := idx.val / n
    let j := idx.val % n
    if i ≥ j then matrix.get idx else 0))

-- LLM HELPER
lemma idx_decomposition (n : Nat) (idx : Fin (n * n)) :
    let i := idx.val / n
    let j := idx.val % n
    i < n ∧ j < n ∧ idx.val = i * n + j := by
  simp [Nat.div_lt_iff_lt_mul_right, Nat.mod_lt]
  constructor
  · exact Nat.div_lt_of_lt_mul idx.isLt
  constructor
  · exact Nat.mod_lt idx.val (Nat.zero_lt_of_ne_zero (fun h => by
      have : n * n = 0 := by rw [h]; simp
      have : n = 0 := Nat.eq_zero_of_mul_eq_zero this |>.elim id id
      rw [this] at idx
      exact Nat.not_lt_zero idx.val idx.isLt))
  · exact Nat.div_add_mod idx.val n

-- LLM HELPER
lemma vector_ofFn_size {α : Type*} {n : Nat} (f : Fin n → α) :
    (Vector.ofFn f).size = n := by
  simp [Vector.ofFn]

-- LLM HELPER
lemma vector_ofFn_get {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.ofFn, Vector.get]

/-- Specification: tril returns the lower triangle of a matrix with elements above the main diagonal zeroed.
    
    Mathematical Properties:
    1. Shape Preservation: The output has the same shape as the input
    2. Lower Triangle Preservation: Elements at or below the main diagonal are unchanged
    3. Upper Triangle Zeroing: Elements above the main diagonal are set to zero
    4. Diagonal Definition: For a square matrix stored in row-major order,
       element at position (i,j) corresponds to index i*n + j in the flattened vector
    
    The main diagonal consists of elements where i = j.
    Lower triangle consists of elements where i ≥ j.
    Upper triangle consists of elements where i < j.
    
    This specification provides a foundation for formal verification of
    triangular matrix operations in numerical computing.
-/
theorem tril_spec {n : Nat} (matrix : Vector Float (n * n)) :
    ⦃⌜True⌝⦄
    tril matrix
    ⦃⇓result => ⌜
      -- The result has the same shape as the input
      result.size = matrix.size ∧
      -- For the lower triangle (i ≥ j), elements are preserved
      (∀ i : Fin n, ∀ j : Fin n, i.val ≥ j.val → 
        ∃ (hi : i.val * n + j.val < n * n) (hj : i.val * n + j.val < n * n),
          result.get ⟨i.val * n + j.val, hi⟩ = matrix.get ⟨i.val * n + j.val, hj⟩) ∧
      -- For the upper triangle (i < j), elements are zero
      (∀ i : Fin n, ∀ j : Fin n, i.val < j.val → 
        ∃ (hi : i.val * n + j.val < n * n),
          result.get ⟨i.val * n + j.val, hi⟩ = 0)⌝⦄ := by
  unfold tril
  simp [pure_spec]
  constructor
  · rw [vector_ofFn_size]
  constructor
  · intro i j h_ge
    have h_bounds : i.val * n + j.val < n * n := by
      rw [Nat.mul_comm n n]
      exact Nat.add_lt_mul_of_pos_left j.isLt i.isLt
    use h_bounds, h_bounds
    rw [vector_ofFn_get]
    simp
    have h_div : (i.val * n + j.val) / n = i.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_ne_zero (fun h => by
        have : n * n = 0 := by rw [h]; simp
        have : n = 0 := Nat.eq_zero_of_mul_eq_zero this |>.elim id id
        rw [this] at i
        exact Nat.not_lt_zero i.val i.isLt))]
      rw [Nat.div_lt_iff_lt_mul_right]
      exact j.isLt
    have h_mod : (i.val * n + j.val) % n = j.val := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt j.isLt
    simp [h_div, h_mod, h_ge]
  · intro i j h_lt
    have h_bounds : i.val * n + j.val < n * n := by
      rw [Nat.mul_comm n n]
      exact Nat.add_lt_mul_of_pos_left j.isLt i.isLt
    use h_bounds
    rw [vector_ofFn_get]
    simp
    have h_div : (i.val * n + j.val) / n = i.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_ne_zero (fun h => by
        have : n * n = 0 := by rw [h]; simp
        have : n = 0 := Nat.eq_zero_of_mul_eq_zero this |>.elim id id
        rw [this] at i
        exact Nat.not_lt_zero i.val i.isLt))]
      rw [Nat.div_lt_iff_lt_mul_right]
      exact j.isLt
    have h_mod : (i.val * n + j.val) % n = j.val := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt j.isLt
    simp [h_div, h_mod, Nat.not_le_of_gt h_lt]