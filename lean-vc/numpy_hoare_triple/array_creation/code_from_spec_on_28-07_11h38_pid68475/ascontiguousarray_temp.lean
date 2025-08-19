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
  simp [Nat.max_def]
  split
  · simp
  · simp

-- LLM HELPER
lemma max_n_1_pos (n : Nat) : n > 0 → max n 1 = n := by
  intro h
  simp [Nat.max_def]
  split
  · contradiction
  · rfl

-- LLM HELPER
lemma max_n_1_zero (n : Nat) : n = 0 → max n 1 = 1 := by
  intro h
  simp [h, Nat.max_def]

/-- Return a contiguous array (ndim >= 1) in memory (C order).
    This function ensures the input array is contiguous in C order and guarantees
    minimum dimensionality of 1. For non-empty input, preserves all elements. -/
def ascontiguousarray {n : Nat} (a : Vector Float n) : Id (Vector Float (max n 1)) :=
  if h : n = 0 then
    have : max n 1 = 1 := max_n_1_zero n h
    this ▸ ⟨[0.0], by simp⟩
  else
    have h_pos : n > 0 := Nat.pos_of_ne_zero h
    have : max n 1 = n := max_n_1_pos n h_pos
    this ▸ a

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
  apply triple_pure_post
  constructor
  · exact max_n_1_ge_1 n
  constructor
  · exact max_n_1_pos n
  constructor
  · exact max_n_1_zero n
  · intro h_pos
    simp [ascontiguousarray]
    split
    · rename_i h_zero
      exfalso
      have : n = 0 := h_zero
      rw [this] at h_pos
      exact Nat.lt_irrefl 0 h_pos
    · rename_i h_ne_zero
      have h_eq : max n 1 = n := max_n_1_pos n h_pos
      simp [h_eq]
      intro i
      use ⟨i.val, by simp [h_eq]; exact i.isLt⟩
      simp [h_eq]