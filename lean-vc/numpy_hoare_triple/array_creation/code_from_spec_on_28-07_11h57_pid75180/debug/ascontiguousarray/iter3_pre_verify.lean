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
def problem_spec : ({n : Nat} → Vector Float n → Id (Vector Float (max n 1))) → Prop :=
  fun impl => ∀ {n : Nat} (a : Vector Float n),
    ⦃⌜True⌝⦄
    impl a
    ⦃⇓result => ⌜
      (max n 1 ≥ 1) ∧
      (n > 0 → max n 1 = n) ∧
      (n = 0 → max n 1 = 1) ∧
      (n > 0 → ∀ i : Fin n, ∃ j : Fin (max n 1), result.get j = a.get i)
    ⌝⦄

-- LLM HELPER
lemma max_n_1_pos (n : Nat) : max n 1 ≥ 1 := by
  simp [Nat.max_def]
  split
  · exact Nat.le_refl 1
  · assumption

-- LLM HELPER
lemma max_n_1_eq_n_when_pos (n : Nat) (h : n > 0) : max n 1 = n := by
  simp [Nat.max_def]
  split
  · omega
  · rfl

-- LLM HELPER
lemma max_n_1_eq_1_when_zero (n : Nat) (h : n = 0) : max n 1 = 1 := by
  simp [h, Nat.max_def]

/-- Return a contiguous array (ndim >= 1) in memory (C order).
    This function ensures the input array is contiguous in C order and guarantees
    minimum dimensionality of 1. For non-empty input, preserves all elements. -/
def ascontiguousarray {n : Nat} (a : Vector Float n) : Id (Vector Float (max n 1)) :=
  if h : n = 0 then
    have : max n 1 = 1 := max_n_1_eq_1_when_zero n h
    pure (this ▸ Vector.mk #[0.0] (by simp))
  else
    have pos : n > 0 := Nat.pos_of_ne_zero h
    have : max n 1 = n := max_n_1_eq_n_when_pos n pos
    pure (this ▸ a)

/-- Specification: ascontiguousarray returns a contiguous array with same content,
    ensuring minimum dimensionality of 1. For non-empty arrays, elements are preserved
    exactly. For empty arrays, returns a 1-dimensional array with 1 element. -/
theorem correctness {n : Nat} (a : Vector Float n) :
    problem_spec ascontiguousarray := by
  intro n a
  apply do_pure_spec
  constructor
  · exact max_n_1_pos n
  constructor
  · intro h
    exact max_n_1_eq_n_when_pos n h
  constructor
  · intro h
    exact max_n_1_eq_1_when_zero n h
  · intro pos
    unfold ascontiguousarray
    simp only [pos, Ne.symm (ne_of_gt pos), ite_false]
    have eq : max n 1 = n := max_n_1_eq_n_when_pos n pos
    simp [eq]
    intro i
    use i.cast eq.symm
    simp [Vector.get_cast]