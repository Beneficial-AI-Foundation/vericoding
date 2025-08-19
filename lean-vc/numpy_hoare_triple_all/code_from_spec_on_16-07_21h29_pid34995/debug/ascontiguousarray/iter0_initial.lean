import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.ascontiguousarray",
  "category": "From existing data",
  "description": "Return a contiguous array (ndim >= 1) in memory (C order)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ascontiguousarray.html",
  "doc": "\nReturn a contiguous array (ndim >= 1) in memory (C order).\n\nParameters\n----------\na : array_like\n    Input array.\ndtype : str or dtype object, optional\n    Data-type of returned array.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n\nReturns\n-------\nout : ndarray\n    Contiguous array of same shape and content as a, with type dtype if specified.\n\nExamples\n--------\n>>> x = np.arange(6).reshape(2,3)\n>>> np.ascontiguousarray(x, dtype=np.float32)\narray([[0., 1., 2.],\n       [3., 4., 5.]], dtype=float32)\n>>> x.flags['C_CONTIGUOUS']\nTrue\n\nNote: This function returns at least a 1-dimensional array. Scalar inputs are converted to 1-dimensional arrays.\n",
  "code": "@array_function_dispatch(_ascontiguousarray_dispatcher)\ndef ascontiguousarray(a, dtype=None, *, like=None):\n    \"\"\"\n    Return a contiguous array (ndim >= 1) in memory (C order).\n    \"\"\"\n    if like is not None:\n        return _ascontiguousarray_with_like(a, dtype=dtype, like=like)\n\n    return array(a, dtype, copy=False, order='C', ndmin=1)",
  "signature": "numpy.ascontiguousarray(a, dtype=None, *, like=None)"
}
-/

-- LLM HELPER
lemma max_n_1_ge_1 (n : Nat) : max n 1 ≥ 1 := by
  simp [max_def]
  cases' le_total n 1 with h h
  · simp [h]
  · simp [h]

-- LLM HELPER
lemma max_n_1_eq_n_when_positive (n : Nat) (h : n > 0) : max n 1 = n := by
  simp [max_def]
  cases' le_total n 1 with h' h'
  · cases' h' with h'
    · contradiction
    · simp [h']
  · simp [h']

-- LLM HELPER
lemma max_n_1_eq_1_when_zero (n : Nat) (h : n = 0) : max n 1 = 1 := by
  simp [h, max_def]

/-- Return a contiguous array (ndim >= 1) in memory (C order).
    This function ensures the input array is contiguous in C order and guarantees
    minimum dimensionality of 1. For non-empty input, preserves all elements. -/
def ascontiguousarray {n : Nat} (a : Vector Float n) : Id (Vector Float (max n 1)) :=
  if h : n > 0 then
    by
      rw [max_n_1_eq_n_when_positive n h]
      exact pure a
  else
    by
      have h' : n = 0 := by omega
      rw [max_n_1_eq_1_when_zero n h']
      exact pure ⟨[0.0], rfl⟩

/-- Specification: ascontiguousarray returns a contiguous array with same content,
    ensuring minimum dimensionality of 1. For non-empty arrays, elements are preserved
    exactly. For empty arrays, returns a 1-dimensional array with 1 element. -/
theorem ascontiguousarray_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    ascontiguousarray a
    ⦃⇓result => ⌜
      (max n 1 ≥ 1) ∧
      (n > 0 → max n 1 = n) ∧
      (n = 0 → max n 1 = 1) ∧
      (n > 0 → ∀ i : Fin n, ∃ j : Fin (max n 1), result.get j = a.get i)
    ⌝⦄ := by
  simp [ascontiguousarray]
  triple_let
  split
  · next h =>
    rw [max_n_1_eq_n_when_positive n h]
    simp [pure]
    constructor
    · exact Nat.le_refl _
    constructor
    · intro; rfl
    constructor
    · intro h'
      exfalso
      exact h' h
    · intro h'
      intro i
      use i
      rfl
  · next h =>
    have h' : n = 0 := by omega
    rw [max_n_1_eq_1_when_zero n h']
    simp [pure]
    constructor
    · exact Nat.le_refl _
    constructor
    · intro h_pos
      exfalso
      rw [h'] at h_pos
      exact Nat.lt_irrefl 0 h_pos
    constructor
    · intro; rfl
    · intro h_pos
      exfalso
      rw [h'] at h_pos
      exact Nat.lt_irrefl 0 h_pos